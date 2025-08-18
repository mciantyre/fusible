// SPDX-License-Identifier: MPL-2.0
// SPDX-FileCopyrightText: Copyright 2024 Ian McIntyre

//! A portable benchmark application for evaluating fusible kernel objects.
//!
//! To port the application to a new architecture, provide an implementation of the `cycle_count()`
//! function. If you need to initialize your cycle count, implement `init_cycle_count`.
//!
//! To instantiate the application, call [`run`] within your system's kernel initialization
//! function.
//!
//! ```no_run
//! fn main() {
//!     fusible::kernel_enter(|app_define| {
//!         fusible_app_benchmark::run(app_define);
//!     })
//! }
//! ```
//!
//! The application reveals its measurements using `defmt`. To see these measurements, you must
//! include a defmt global logger, like `defmt-rtt` or `defmt-semihosting`.
//!
//! # Theory of operation
//!
//! The benchmark app measures the cycles required to perform a low-priority (LP) to high-priority
//! (HP) context switch. The LP thread blocks on a semaphore that's set by the HP thread. Since
//! the HP thread has higher priority, its put on the semaphore doesn't block. Then, the HP thread
//! blocks on a kernel operation, giving the LP thread a chance to run.
//!
//! The LP thread observes the semaphore put, takes a cycle sample, then executes an operation that
//! wakes the HP thread. This affects a context switch from the LP thread to the HP thread.
//!
//! The HP thread wakes and takes a cycle sample. It computes the difference between the cycle
//! measurements. As long as the CPU was not utilized for other work during the context switch, the
//! difference should represent the number of cycles required for the kernel call and the context
//! switch.

#![no_std]

use core::{num::NonZeroU32, pin::Pin, sync::atomic::AtomicU32};

use fusible::{
    AppDefine,
    event_flags::{EventFlags, EventFlagsContext, SetOption},
    queue::{Queue, QueueContext, StaticQueueSlots},
    semaphore::{Semaphore, SemaphoreContext},
    thread::{self, StaticStack, Thread, ThreadContext, ThreadPriority},
};

/// Initialize your cycle count system.
fn init_cycle_count() {
    cfg_if::cfg_if! {
        if #[cfg(all(target_arch = "arm", target_os = "none"))] {
            let mut cortex_m = unsafe { cortex_m::Peripherals::steal() };
            cortex_m.DCB.enable_trace();
            cortex_m::peripheral::DWT::unlock();
            cortex_m.DWT.enable_cycle_counter();
        } else {
            // When you want something like compiler_warning! but it doesn't exist.
            #[deprecated]
            fn this_build_needs_an_init_cycle_count_impl() -> ! { todo!(); }
            this_build_needs_an_init_cycle_count_impl()
        }
    }
}

/// Takes a snapshot of the CPU's cycle count, an absolute number.
fn cycle_count() -> u32 {
    cfg_if::cfg_if! {
        if #[cfg(all(target_arch = "arm", target_os = "none"))] {
            cortex_m::peripheral::DWT::cycle_count()
        } else {
            #[deprecated]
            fn this_build_needs_a_cycle_count_impl() -> ! { todo!(); }
            this_build_needs_a_cycle_count_impl()
        }
    }
}

/// The assumed ticks per second of the port.
const TX_TIMER_TICKS_PER_SECOND: u32 = 100;

struct CycleSample(AtomicU32);
impl CycleSample {
    const fn new() -> Self {
        Self(AtomicU32::new(0))
    }
    fn sample(&self) {
        self.0
            .store(cycle_count(), core::sync::atomic::Ordering::SeqCst)
    }
    fn read(&self) -> u32 {
        self.0.load(core::sync::atomic::Ordering::SeqCst)
    }
}

static BEGIN: CycleSample = CycleSample::new();
static END: CycleSample = CycleSample::new();

static LOW_PRIO_STACK: StaticStack<512> = StaticStack::new();
static HIGH_PRIO_STACK: StaticStack<512> = StaticStack::new();

static LOW_PRIO_THREAD: ThreadContext = Thread::context();
static HIGH_PRIO_THREAD: ThreadContext = Thread::context();
static HIGH_PRIO_READY: SemaphoreContext = Semaphore::context();

static FLAGS: EventFlagsContext = EventFlags::context();
static SEMAPHORE: SemaphoreContext = Semaphore::context();
// Safety: The value is non-zero by construction.
const CEILING_ONE: NonZeroU32 = unsafe { NonZeroU32::new_unchecked(1) };

static SLOTS: StaticQueueSlots<u32, 1> = StaticQueueSlots::new();
static QUEUE: QueueContext<u32> = Queue::context();

fn low_prio_thread() {
    fn signal<F: FnOnce() -> T, T>(what: F) -> T {
        Pin::static_ref(&HIGH_PRIO_READY)
            .try_created()
            .unwrap()
            .get()
            .unwrap();
        BEGIN.sample();
        what()
    }

    let mut queue_msg = 0u32;
    let queue = Pin::static_ref(&QUEUE).try_created().unwrap();
    let flags = Pin::static_ref(&FLAGS).try_created().unwrap();
    let semaphore = Pin::static_ref(&SEMAPHORE).try_created().unwrap();
    let high_prio_thread = Pin::static_ref(&HIGH_PRIO_THREAD).try_created().unwrap();

    loop {
        thread::sleep(250 * TX_TIMER_TICKS_PER_SECOND / 1000);

        signal(|| high_prio_thread.resume()).unwrap();
        signal(|| flags.set(0xDEADBEEF, SetOption::Or));
        signal(|| semaphore.ceiling_put(CEILING_ONE).unwrap());

        signal(|| queue.send(queue_msg).unwrap());
        queue_msg = queue_msg.wrapping_add(1);
    }
}

fn high_prio_thread() {
    struct Measurements {
        max_cycles: u32,
        min_cycles: u32,
    }

    impl Measurements {
        fn new() -> Self {
            Self {
                max_cycles: 0,
                min_cycles: u32::MAX,
            }
        }

        fn measure<F: FnOnce() -> R, R>(&mut self, what: F) -> R {
            Pin::static_ref(&HIGH_PRIO_READY)
                .try_created()
                .unwrap()
                .ceiling_put(CEILING_ONE)
                .unwrap();

            let result = what();
            END.sample();

            let delta = END.read().wrapping_sub(BEGIN.read());
            self.max_cycles = self.max_cycles.max(delta);
            self.min_cycles = self.min_cycles.min(delta);

            result
        }
    }

    let mut suspend_resume = Measurements::new();
    let mut flags_put_get = Measurements::new();
    let mut semaphore_put_get = Measurements::new();
    let mut queue_send_recv = Measurements::new();

    let queue = Pin::static_ref(&QUEUE).try_created().unwrap();
    let flags = Pin::static_ref(&FLAGS).try_created().unwrap();
    let semaphore = Pin::static_ref(&SEMAPHORE).try_created().unwrap();
    let high_prio_thread = Pin::static_ref(&HIGH_PRIO_THREAD).try_created().unwrap();

    for iter in (0u32..=!0).cycle() {
        suspend_resume
            .measure(|| high_prio_thread.suspend())
            .unwrap();
        defmt::println!(
            "({=u32}) Suspend/Resume: Max {=u32} Min {=u32} cycles",
            iter,
            suspend_resume.max_cycles,
            suspend_resume.min_cycles,
        );

        let flags = flags_put_get.measure(|| {
            flags
                .get(
                    NonZeroU32::new(0xDEADBEEF).unwrap(),
                    fusible::event_flags::GetOption::AndClear,
                )
                .unwrap()
                .get()
        });
        defmt::assert_eq!(flags, 0xDEADBEEF);
        defmt::println!(
            "({=u32}) Event Flags Put/Get: Max {=u32} Min {=u32} cycles",
            iter,
            flags_put_get.max_cycles,
            flags_put_get.min_cycles,
        );

        semaphore_put_get.measure(|| semaphore.get()).unwrap();
        defmt::println!(
            "({=u32}) Semaphore Put/Get: Max {=u32} Min {=u32} cycles",
            iter,
            semaphore_put_get.max_cycles,
            semaphore_put_get.min_cycles,
        );

        let queue_msg = queue_send_recv.measure(|| queue.receive()).unwrap();
        defmt::assert_eq!(queue_msg, iter);
        defmt::println!(
            "({=u32}) Queue Send/Recv: Max {=u32} Min {=u32} cycles",
            iter,
            queue_send_recv.max_cycles,
            queue_send_recv.min_cycles,
        );
    }
}

/// Run the benchmark application.
///
/// See the package documentation for an example.
pub fn run<'ad>(_: &'ad AppDefine<'ad, '_>) {
    init_cycle_count();

    let mut low_prio_options =
        thread::ThreadOptions::single_priority(ThreadPriority::new(5).unwrap());
    low_prio_options.name = Some(c"low-prio");

    let mut high_prio_options =
        thread::ThreadOptions::single_priority(ThreadPriority::new(4).unwrap());
    high_prio_options.name = Some(c"high-prio");

    Semaphore::create(Pin::static_ref(&HIGH_PRIO_READY), &Default::default()).unwrap();
    EventFlags::create(Pin::static_ref(&FLAGS), &Default::default()).unwrap();
    Semaphore::create(Pin::static_ref(&SEMAPHORE), &Default::default()).unwrap();
    Queue::create(
        Pin::static_ref(&QUEUE),
        SLOTS.take().unwrap(),
        &Default::default(),
    )
    .unwrap();

    Thread::create(
        Pin::static_ref(&LOW_PRIO_THREAD),
        LOW_PRIO_STACK.take().unwrap(),
        &low_prio_options,
        low_prio_thread,
    )
    .unwrap();
    Thread::create(
        Pin::static_ref(&HIGH_PRIO_THREAD),
        HIGH_PRIO_STACK.take().unwrap(),
        &high_prio_options,
        high_prio_thread,
    )
    .unwrap();
}
