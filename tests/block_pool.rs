// SPDX-License-Identifier: MPL-2.0
// SPDX-FileCopyrightText: Copyright 2024 Ian McIntyre

//! Fusible block pools make it easy for users to perfectly size their
//! block pools for a total number of blocks. This test shows that the total
//! number of blocks computed by ThreadX matches the number of blocks we're
//! sizing for the pool.

use std::pin::{pin, Pin};

use fusible::{
    block_pool::{Block, BlockOf, BlockPool, BlockPoolContext, StaticBlocks},
    kernel_enter,
    thread::{StaticStack, Thread, ThreadContext},
};

fn assert_block_pool_behaviors<T: Default>(block_pool: &BlockPool<T>, total: u32) {
    let info = block_pool.info();
    assert_eq!(info.available_blocks, total);
    assert_eq!(info.total_blocks, total);

    let mut available_blocks = total;
    while available_blocks > 0 {
        let block = block_pool.try_allocate(T::default).unwrap();
        let info = block_pool.info();
        assert_eq!(info.available_blocks, available_blocks - 1);

        drop(block);
        let info = block_pool.info();
        assert_eq!(info.available_blocks, available_blocks);

        let block = block_pool.try_allocate(T::default).unwrap();
        let info = block_pool.info();
        assert_eq!(info.available_blocks, available_blocks - 1);
        std::mem::forget(block);
        available_blocks -= 1;
    }

    let info = block_pool.info();
    assert_eq!(info.available_blocks, 0);
    assert_eq!(info.total_blocks, total);

    assert!(block_pool.try_allocate(T::default).is_none());
}

fn block_test<T: Default, const N: usize>() {
    let mut storage = [const { BlockOf::<T>::new() }; N];
    let block_pool = pin!(BlockPool::context());
    let block_pool =
        BlockPool::create(block_pool.into_ref(), &mut storage, &Default::default()).unwrap();
    assert_block_pool_behaviors(block_pool, N as _);
}

fn extra_static_block_test() {
    static BLOCK_POOL: BlockPoolContext<[u32; 7]> = BlockPool::context();
    const ELEMS: usize = 53;
    static STORAGE: StaticBlocks<[u32; 7], ELEMS> = StaticBlocks::new();
    let block_pool = BlockPool::create(
        Pin::static_ref(&BLOCK_POOL),
        STORAGE.take().unwrap(),
        &Default::default(),
    )
    .unwrap();

    let info = block_pool.info();
    assert_eq!(info.available_blocks, ELEMS as _);
    assert_eq!(info.total_blocks, ELEMS as _);

    let mut block = block_pool.try_allocate(Default::default).unwrap();

    let info = block_pool.info();
    assert_eq!(info.available_blocks, (ELEMS - 1) as _);

    (*block)[4] = 4;
    let block: Block<[u32]> = Block::into_slice(block);
    assert_eq!(block[4], 4);

    let info = block_pool.info();
    assert_eq!(info.available_blocks, (ELEMS - 1) as _);

    drop(block);
    let info = block_pool.info();
    assert_eq!(info.available_blocks, ELEMS as _);

    assert_block_pool_behaviors(block_pool, ELEMS as _);
}

static STACK: StaticStack<4096> = StaticStack::new();
static THREAD: ThreadContext = Thread::context();

#[test]
fn block_pool_sizing() {
    kernel_enter(|_| {
        Thread::create(
            Pin::static_ref(&THREAD),
            STACK.take().unwrap(),
            &Default::default(),
            || {
                block_test::<[u8; 8], 31>();
                block_test::<[u8; 7], 37>();
                block_test::<[u8; 9], 31>();
                block_test::<[u8; 1], 91>();
                block_test::<[u8; 17], 5>();
                block_test::<[u32; 12], 13>();
                extra_static_block_test();

                std::process::exit(0)
            },
        )
        .unwrap();
    });
}
