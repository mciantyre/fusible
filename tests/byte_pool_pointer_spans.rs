// SPDX-License-Identifier: MPL-2.0
// SPDX-FileCopyrightText: Copyright 2024 Ian McIntyre

use fusible::{
    byte_pool::{AlignedBytePoolStorage, BytePool},
    thread::{StaticStack, Thread},
};
use std::{
    collections::HashSet,
    ops::{Range, RangeInclusive},
    pin::pin,
};

static STACK: StaticStack<2048> = StaticStack::new();

fn cast_range<T>(range: Range<*const T>) -> Range<*const ()> {
    Range {
        start: range.start.cast(),
        end: range.end.cast(),
    }
}

fn thread_entry() {
    let mut storage = AlignedBytePoolStorage::from_array([0u8; 256]);

    {
        let storage_range: RangeInclusive<*const ()> = RangeInclusive::new(
            storage.as_ref().as_ptr_range().start.cast(),
            storage.as_ref().as_ptr_range().end.cast(),
        );

        let pool = pin!(BytePool::context());
        let pool = BytePool::create(pool.into_ref(), &mut storage, &Default::default()).unwrap();
        let mut spans = Vec::new();

        let bytes = pool.try_allocate(|| [u8::MAX; 32]).unwrap().unwrap();
        spans.push(cast_range(bytes.as_ptr_range()));

        let halves = pool.try_allocate(|| [u16::MAX; 16]).unwrap().unwrap();
        spans.push(cast_range(halves.as_ptr_range()));

        let words = pool.try_allocate(|| [u32::MAX; 8]).unwrap().unwrap();
        spans.push(cast_range(words.as_ptr_range()));

        drop(bytes);
        drop(halves);
        drop(words);

        for span in spans.iter() {
            assert!(storage_range.contains(&span.start));
            assert!(storage_range.contains(&span.end));
        }

        let unique_spans: HashSet<_> = spans.into_iter().collect();
        assert_eq!(unique_spans.len(), 3);
    }

    std::process::exit(0);
}

#[test]
fn main() {
    let thread = pin!(Thread::context());
    fusible::kernel_enter(|app_define| {
        app_define
            .create_thread(
                thread.into_ref(),
                STACK.take().unwrap(),
                &Default::default(),
                thread_entry,
            )
            .unwrap();
    })
}
