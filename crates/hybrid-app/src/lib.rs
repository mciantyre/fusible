// SPDX-License-Identifier: MPL-2.0
// SPDX-FileCopyrightText: Copyright 2024 Ian McIntyre

#![no_std]

use core::{num::NonZero, pin::Pin};

use fusible::{
    block_pool::{Block, BlockPool, BlockPoolContext, StaticBlocks},
    event_flags::{EventFlags, EventFlagsContext, GetOption},
    mutex::Mutex,
    queue::{Queue, QueueContext, StaticQueueSlots},
    semaphore::{Semaphore, SemaphoreContext},
    thread::{StaticStack, Thread, ThreadContext},
    AppDefine,
};

extern "C" {
    static sender_thread: ThreadContext<'static>;
    static receiver_thread: ThreadContext<'static>;
    static msg_queue: QueueContext<'static, u32>;

    static block_xform_input: QueueContext<'static, MyBlockPtr<'static>>;
    static block_xform_output: QueueContext<'static, MyBlockPtr<'static>>;

    static pattern_flags: EventFlagsContext<'static>;

    fn sender_thread_entry(_: &'static Semaphore);
    fn setup_c() -> u32;
}

pub trait ExitProcess: Send + 'static {
    fn success(self) -> !;
}

static SENDER_STACK: StaticStack<1024> = StaticStack::new();
static RECEIVER_STACK: StaticStack<1024> = StaticStack::new();
static MSG_SLOTS: StaticQueueSlots<u32, 4> = StaticQueueSlots::new();

fn receiver_thread_entry(queue: &Queue<u32>, finished: &Semaphore) {
    for expected in 0..10 {
        let actual = queue.receive().unwrap();
        assert_eq!(actual, expected);
    }

    finished.put();
}

#[no_mangle]
pub static THREAD_FINISHED: SemaphoreContext = Semaphore::context();
const EXPECTED_THREAD_FINISHES: usize = 6;

static SUPERVISOR_THREAD: ThreadContext = Thread::context();
static SUPERVISOR_STACK: StaticStack<1024> = StaticStack::new();

const UINT32_PER_BLOCK: usize = 12;
type MyBlock = [u32; UINT32_PER_BLOCK];
type MyBlockPtr<'pool> = Block<'pool, MyBlock>;

#[no_mangle]
pub static BLOCK_POOL: BlockPoolContext<MyBlock> = BlockPool::context();
static MY_BLOCK_BLOCKS: StaticBlocks<MyBlock, 13> = StaticBlocks::new();

static BLOCK_PUB_SUB_THREAD: ThreadContext = Thread::context();
static BLOCK_PUB_SUB_STACK: StaticStack<1024> = StaticStack::new();

fn block_pub_sub(
    input: &Queue<MyBlockPtr>,
    output: &Queue<MyBlockPtr>,
    pool: &BlockPool<MyBlock>,
    finished: &Semaphore,
) {
    for i in 0..18 {
        let sent = pool.allocate(|| [i + 113; UINT32_PER_BLOCK]).unwrap();
        let info = pool.info();
        assert_eq!(info.available_blocks, info.total_blocks - 1);
        let sent_ptr: *const MyBlock = &*sent as *const _;
        assert!(input.send(sent).is_ok());

        let info = pool.info();
        assert_eq!(info.available_blocks, info.total_blocks - 1);

        let bitflipped = output.receive().unwrap();
        assert_eq!(*bitflipped, [!(i + 113 + 37); UINT32_PER_BLOCK]);
        let incremented = output.receive().unwrap();
        assert_eq!(*incremented, [(i + 113 + 37); UINT32_PER_BLOCK]);

        let info = pool.info();
        assert_eq!(info.available_blocks, info.total_blocks - 2);
        assert_eq!(sent_ptr, &*incremented as *const MyBlock);

        drop(incremented);
        drop(bitflipped);

        let info = pool.info();
        assert_eq!(info.available_blocks, info.total_blocks);
    }

    finished.put();
}

#[no_mangle]
pub extern "C" fn run_from_c(flags: &EventFlags, antipattern: &Mutex<u32>, other: &Thread) {
    for _ in 0..37 {
        let pattern = flags
            .get(NonZero::new(!0).unwrap(), GetOption::OrClear)
            .unwrap()
            .get();

        let antipattern = antipattern.lock().unwrap();
        assert_eq!(pattern, !*antipattern);

        other.resume().unwrap();
    }
}

#[no_mangle]
pub static FLAG_SIGNAL_THREAD: ThreadContext = Thread::context();
#[no_mangle]
pub static FLAG_RETRIEVAL_THREAD: ThreadContext = Thread::context();

pub fn setup<E: ExitProcess>(_: &AppDefine, exit: E) {
    // Safety: lib.c shows that this function accepts no arguments
    // and produces a u32. It initializes state that is safe for
    // concurrent access from Rust.
    let c_result = unsafe { setup_c() };
    assert_eq!(c_result, 0, "Something in C failed to initialize!");

    let thread_finished =
        Semaphore::create(Pin::static_ref(&THREAD_FINISHED), &Default::default()).unwrap();

    Thread::create(
        Pin::static_ref(&SUPERVISOR_THREAD),
        SUPERVISOR_STACK.take().unwrap(),
        &Default::default(),
        move || {
            for _ in 0..EXPECTED_THREAD_FINISHES {
                thread_finished.get().unwrap();
            }
            exit.success();
        },
    )
    .unwrap();

    Thread::create(
        // Safety: lib.c shows that this is a TX_THREAD control block.
        // A ThreadContext is transparently that same control block.
        Pin::static_ref(unsafe { &sender_thread }),
        SENDER_STACK.take().unwrap(),
        &Default::default(),
        // Safety: lib.c shows that this function has the correct
        // signature.
        move || unsafe { sender_thread_entry(thread_finished) },
    )
    .unwrap();

    let queue = Queue::create(
        // Safety: lib.c shows that this is a TX_QUEUE control block.
        // A QueueContext is transparently that same control block.
        Pin::static_ref(unsafe { &msg_queue }),
        MSG_SLOTS.take().unwrap(),
        &Default::default(),
    )
    .unwrap();

    Thread::create(
        // Safety: lib.c shows that this is a TX_THREAD control block.
        // A ThreadContext is transparently that same control block.
        Pin::static_ref(unsafe { &receiver_thread }),
        RECEIVER_STACK.take().unwrap(),
        &Default::default(),
        move || receiver_thread_entry(queue, thread_finished),
    )
    .unwrap();

    // Safety: lib.c shows that this is a TX_QUEUE control block.
    // A QueueContext is transparently that same control block.
    // setup_c() creates this control block, so this call won't
    // panic.
    let input = Pin::static_ref(unsafe { &block_xform_input })
        .try_created()
        .unwrap();
    // Safety: see above.
    let output = Pin::static_ref(unsafe { &block_xform_output })
        .try_created()
        .unwrap();
    let pool = BlockPool::create(
        Pin::static_ref(&BLOCK_POOL),
        MY_BLOCK_BLOCKS.take().unwrap(),
        &Default::default(),
    )
    .unwrap();

    Thread::create(
        Pin::static_ref(&BLOCK_PUB_SUB_THREAD),
        BLOCK_PUB_SUB_STACK.take().unwrap(),
        &Default::default(),
        move || block_pub_sub(input, output, pool, thread_finished),
    )
    .unwrap();

    EventFlags::create(
        Pin::static_ref(unsafe { &pattern_flags }),
        &Default::default(),
    )
    .unwrap();
}
