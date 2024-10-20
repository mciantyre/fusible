// SPDX-License-Identifier: MPL-2.0
// SPDX-FileCopyrightText: Copyright 2024 Ian McIntyre

#![allow(clippy::assertions_on_constants)]

// Assume nothing is Send.
trait AssumeNotSend {
    const IS_SEND: bool = false;
}
impl<T /* : !Send */> AssumeNotSend for T {}

// Then, check if something is Send. Importantly,
// CheckSend is AssumeNotSend.
struct CheckSend<T>(std::marker::PhantomData<T>);

// This conveniently shadows the `IS_SEND` constant
// introduced by the AssumeNotSend blanket.
impl<T: Send> CheckSend<T> {
    const IS_SEND: bool = true;
}

macro_rules! check_send {
    ($t:ty) => {
        CheckSend::<$t>::IS_SEND
    };
}

#[test]
fn contexts_not_send() {
    // Sanity check the types above.
    assert!(check_send!(u32)); // A u32 is trivially Send
    assert!(!check_send!(*mut u32)); // But a raw pointer? Not Send.

    // OK, so none of the context blocks should be send.
    assert!(!check_send!(fusible::block_pool::BlockPoolContext<u32>));
    assert!(!check_send!(fusible::byte_pool::BytePoolContext));
    assert!(!check_send!(fusible::event_flags::EventFlagsContext));
    assert!(!check_send!(fusible::mutex::MutexContext<u32>));
    assert!(!check_send!(fusible::queue::QueueContext<u32>));
    assert!(!check_send!(fusible::semaphore::SemaphoreContext));
    assert!(!check_send!(fusible::thread::ThreadContext));
    assert!(!check_send!(fusible::timer::TimerContext<fn()>));
}
