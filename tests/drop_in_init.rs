// SPDX-License-Identifier: MPL-2.0
// SPDX-FileCopyrightText: Copyright 2024 Ian McIntyre

//! If a resource is dropped in the initialization context, the program aborts.
//!
//! The test runs with no additional command-line arguments. The program will
//! re-run itself with an argument that specifies a function name. That run
//! is expected to abort.

use std::collections::HashMap;
use std::env::args;
use std::pin::pin;
use std::process::Command;

fn block_pool() {
    use fusible::block_pool::{BlockOf, BlockPool};

    fusible::kernel_enter(|_| {
        let mut storage = [const { BlockOf::<u32>::new() }; 32];
        let pool = pin!(BlockPool::context());
        BlockPool::create(pool.into_ref(), &mut storage, &Default::default()).unwrap();
    });
}

fn byte_pool() {
    use fusible::byte_pool::{AlignedBytePoolStorage, BytePool};

    fusible::kernel_enter(|_| {
        let mut storage = AlignedBytePoolStorage::from_array([0; 512]);
        let pool = pin!(BytePool::context());
        BytePool::create(pool.into_ref(), &mut storage, &Default::default()).unwrap();
    });
}

fn event_flags() {
    use fusible::event_flags::EventFlags;

    fusible::kernel_enter(|_| {
        let flags = pin!(EventFlags::context());
        EventFlags::create(flags.into_ref(), &Default::default()).unwrap();
    });
}

fn mutex() {
    use fusible::mutex::Mutex;

    fusible::kernel_enter(|_| {
        let mutex = pin!(Mutex::context(0u32));
        Mutex::create(mutex.into_ref(), &Default::default()).unwrap();
    });
}

fn queue() {
    use fusible::queue::{Queue, QueueSlot};

    fusible::kernel_enter(|_| {
        let mut slots = [const { QueueSlot::<u32>::new() }; 32];
        let queue = pin!(Queue::context());
        Queue::create(queue.into_ref(), &mut slots, &Default::default()).unwrap();
    });
}

fn semaphore() {
    use fusible::semaphore::Semaphore;

    fusible::kernel_enter(|_| {
        let sema = pin!(Semaphore::context());
        Semaphore::create(sema.into_ref(), &Default::default()).unwrap();
    });
}

fn thread() {
    use fusible::thread::{StaticStack, Thread};

    fusible::kernel_enter(|_| {
        static STACK: StaticStack<4096> = StaticStack::new();
        let thread = pin!(Thread::context());
        Thread::create(
            thread.into_ref(),
            STACK.take().unwrap(),
            &Default::default(),
            || (),
        )
        .unwrap();
    });
}

fn timer() {
    use fusible::timer::{Timer, TimerSchedule::OneShot};

    fusible::kernel_enter(|_| {
        fn callback() {}
        let timer = pin!(Timer::context());
        Timer::create(
            timer.into_ref(),
            OneShot {
                ticks: 5.try_into().unwrap(),
            },
            &Default::default(),
            callback,
        )
        .unwrap();
    });
}

fn main() {
    macro_rules! test_case {
        ($ident:ident) => {
            (stringify!($ident), $ident as fn())
        };
    }

    let name_to_test: HashMap<_, fn()> = [
        test_case!(block_pool),
        test_case!(byte_pool),
        test_case!(event_flags),
        test_case!(mutex),
        test_case!(queue),
        test_case!(semaphore),
        test_case!(thread),
        test_case!(timer),
    ]
    .into_iter()
    .collect();

    let mut args = args();
    let myself = args.next().unwrap();

    if let Some(test_name) = args.next() {
        (name_to_test.get(test_name.as_str()).unwrap())()
    } else {
        for test_name in name_to_test.keys() {
            let test_result = Command::new(&myself).arg(test_name).output().unwrap();
            assert!(!test_result.status.success(), "{test_name}");

            let stderr = String::from_utf8(test_result.stderr).unwrap();
            assert!(
                stderr.contains("Attempt to drop resource in the initialization context"),
                "{test_name}"
            );
            assert!(
                stderr.contains("Aborting the Fusible program"),
                "{test_name}"
            );
        }
    }
}
