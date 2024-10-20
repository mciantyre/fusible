// SPDX-License-Identifier: MPL-2.0
// SPDX-FileCopyrightText: Copyright 2024 Ian McIntyre

//! Check that access through block pointers are in bounds of the storage.
//! Check that all block spans are unique.

use fusible::{
    block_pool::{BlockOf, BlockPool},
    thread::{StaticStack, Thread},
};
use std::{collections::HashSet, ops::RangeInclusive, pin::pin};

static STACK: StaticStack<2048> = StaticStack::new();
const BLOCK_COUNT: usize = 37;

fn thread_entry() {
    let mut storage = [const { BlockOf::<[u32; 4]>::new() }; BLOCK_COUNT];

    {
        let storage_range = storage.as_ptr_range();
        let storage_range: RangeInclusive<*const u32> =
            RangeInclusive::new(storage_range.start.cast(), storage_range.end.cast());

        let pool = pin!(BlockPool::context());
        let pool = BlockPool::create(pool.into_ref(), &mut storage, &Default::default()).unwrap();

        let mut blocks = Vec::with_capacity(BLOCK_COUNT);
        while let Some(block) = pool.try_allocate(|| [u32::MAX; 4]) {
            // Is this block's span within the total span of the storage?
            let block_range = block.as_ptr_range();
            assert!(storage_range.contains(&block_range.start));
            assert!(storage_range.contains(&block_range.end));
            blocks.push(block);
        }

        assert_eq!(blocks.len(), BLOCK_COUNT);

        // Are all block spans unique?
        let mut unique_ranges = HashSet::new();
        for block in blocks {
            unique_ranges.insert(block.as_ptr_range());
        }
        assert_eq!(unique_ranges.len(), BLOCK_COUNT);
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
