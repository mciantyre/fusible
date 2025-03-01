// SPDX-License-Identifier: MPL-2.0
// SPDX-FileCopyrightText: Copyright 2024 Ian McIntyre

//! When a queue is dropped, it will drop any elements remaining
//! in the queue.

use std::{
    pin::{Pin, pin},
    sync::atomic::{AtomicUsize, Ordering},
};

use fusible::{
    queue::{Queue, QueueSlot},
    thread::{StaticStack, Thread, ThreadContext},
};

static DROP_COUNT: AtomicUsize = AtomicUsize::new(0);

#[derive(Debug)]
struct Dropper(usize);
impl Dropper {
    const fn new() -> Self {
        Self(1)
    }
}

impl Drop for Dropper {
    fn drop(&mut self) {
        DROP_COUNT.fetch_add(self.0, Ordering::Relaxed);
    }
}

type Slot = QueueSlot<Dropper>;
const ELEMS: usize = 47;

fn fill_a_queue_then_drop_it() {
    let mut slots = [const { Slot::new() }; ELEMS];
    let queue = pin!(Queue::context());
    let queue = queue.as_ref();
    let queue = Queue::create(queue, &mut slots, &Default::default()).unwrap();

    let info = queue.info();
    assert_eq!(info.available_storage, ELEMS as _);
    assert_eq!(info.enqueued, 0);

    loop {
        if let Some(retry) = queue.try_send(Dropper::new()) {
            // Would be dropped, incurring an off-by-one difference
            // in the test.
            core::mem::forget(retry);
            break;
        }
    }

    let info = queue.info();
    assert_eq!(info.available_storage, 0);
    assert_eq!(info.enqueued, ELEMS as _);

    assert_eq!(DROP_COUNT.load(Ordering::Relaxed), 0);
}

static STACK: StaticStack<2048> = StaticStack::new();
static THREAD: ThreadContext = Thread::context();

#[test]
fn main() {
    fusible::kernel_enter(|_| {
        Thread::create(
            Pin::static_ref(&THREAD),
            STACK.take().unwrap(),
            &Default::default(),
            || {
                fill_a_queue_then_drop_it();
                assert_eq!(DROP_COUNT.load(Ordering::Relaxed), ELEMS);
                std::process::exit(0);
            },
        )
        .unwrap();
    })
}
