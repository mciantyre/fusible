// SPDX-License-Identifier: MPL-2.0
// SPDX-FileCopyrightText: Copyright 2024 Ian McIntyre

//! Evaluate different kinds of byte pools with static, inline, external storage.

use std::{alloc::Layout, cell::Cell, pin::Pin};

use fusible::{
    WaitOption,
    byte_pool::{
        self, AlignedBytePoolStorage, BytePool, BytePoolContext, Bytes, StaticBytePoolStorage,
    },
    thread::{StaticStack, Thread, ThreadContext},
};

fn test_byte_pool(byte_pool: &BytePool) {
    fn test_alloc_release_raw<T>(byte_pool: &BytePool) {
        let layout = Layout::new::<T>();

        {
            let memory_ptr = byte_pool::allocate(byte_pool, layout, WaitOption::no_wait()).unwrap();

            assert!(memory_ptr.cast::<T>().is_aligned());
            unsafe {
                byte_pool::release(memory_ptr, layout).unwrap();
            }
        }

        {
            let mut memory_ptrs = Vec::new();
            loop {
                match byte_pool::allocate(byte_pool, layout, WaitOption::no_wait()) {
                    Ok(memory_ptr) if memory_ptr.is_null() => break,
                    Ok(memory_ptr) => memory_ptrs.push(memory_ptr),
                    Err(err) => panic!("{err:?}"),
                }
            }
            assert!(!memory_ptrs.is_empty());
            for memory_ptr in memory_ptrs {
                unsafe { byte_pool::release(memory_ptr, layout).unwrap() };
            }
        }

        {
            let memory_ptr_a =
                byte_pool::allocate(byte_pool, layout, WaitOption::no_wait()).unwrap();
            let memory_ptr_b =
                byte_pool::allocate(byte_pool, layout, WaitOption::no_wait()).unwrap();

            assert_ne!(memory_ptr_a, memory_ptr_b);
            assert!(memory_ptr_a.cast::<T>().is_aligned());
            assert!(memory_ptr_b.cast::<T>().is_aligned());

            unsafe {
                byte_pool::release(memory_ptr_a, layout).unwrap();
                byte_pool::release(memory_ptr_b, layout).unwrap();
            }
        }
    }

    #[repr(align(32))]
    struct BigAlign<const N: usize>([u8; N]);
    impl<const N: usize> Default for BigAlign<N> {
        fn default() -> Self {
            Self([0; N])
        }
    }

    test_alloc_release_raw::<[u8; 1]>(byte_pool);
    test_alloc_release_raw::<[u8; 8]>(byte_pool);
    test_alloc_release_raw::<[u8; 13]>(byte_pool);
    test_alloc_release_raw::<[u8; 16]>(byte_pool);
    test_alloc_release_raw::<[u8; 17]>(byte_pool);

    test_alloc_release_raw::<BigAlign<1>>(byte_pool);
    test_alloc_release_raw::<BigAlign<8>>(byte_pool);
    test_alloc_release_raw::<BigAlign<13>>(byte_pool);
    test_alloc_release_raw::<BigAlign<16>>(byte_pool);
    test_alloc_release_raw::<BigAlign<17>>(byte_pool);

    fn test_alloc_release<'t, T: Default + 't>(byte_pool: &BytePool) {
        {
            let _ = byte_pool.try_allocate(T::default).unwrap();
        }
        {
            let mut objs = Vec::new();
            loop {
                match byte_pool.try_allocate(T::default) {
                    Ok(Some(obj)) => objs.push(obj),
                    Ok(None) => break,
                    Err(err) => panic!("{err:?}"),
                }
            }
            assert!(!objs.is_empty());
            objs.clear()
        }
    }

    test_alloc_release::<[u8; 1]>(byte_pool);
    test_alloc_release::<[u8; 8]>(byte_pool);
    test_alloc_release::<[u8; 13]>(byte_pool);
    test_alloc_release::<[u8; 16]>(byte_pool);
    test_alloc_release::<[u8; 17]>(byte_pool);

    test_alloc_release::<BigAlign<1>>(byte_pool);
    test_alloc_release::<BigAlign<8>>(byte_pool);
    test_alloc_release::<BigAlign<13>>(byte_pool);
    test_alloc_release::<BigAlign<16>>(byte_pool);
    test_alloc_release::<BigAlign<17>>(byte_pool);

    #[derive(Clone)]
    struct DropCounter<'a> {
        ctr: &'a Cell<usize>,
    }
    impl Drop for DropCounter<'_> {
        fn drop(&mut self) {
            self.ctr.set(self.ctr.get().saturating_add(1))
        }
    }

    {
        let counter = DropCounter { ctr: &Cell::new(0) };
        let mut objs = Vec::new();

        while let Ok(Some(obj)) = byte_pool.try_allocate(|| counter.clone()) {
            assert_eq!(obj.ctr.get(), 0);
            objs.push(obj);
        }

        assert!(!objs.is_empty());
        let obj_count = objs.len();

        assert_eq!(0, counter.ctr.get());
        objs.clear();
        assert_eq!(obj_count, counter.ctr.get());
    }
    {
        let counter = DropCounter { ctr: &Cell::new(0) };
        let counters = byte_pool
            .try_allocate(|| [counter.clone(), counter.clone(), counter.clone()])
            .unwrap()
            .unwrap();
        let counters: Bytes<[DropCounter]> = Bytes::into_slice(counters);
        assert_eq!(counter.ctr.get(), 0);
        drop(counters);
        assert_eq!(counter.ctr.get(), 3);
    }

    fn allocate_in_small_scope(byte_pool: &BytePool) -> Bytes<'_, i32> {
        let x = 5;
        byte_pool.try_allocate(|| x).unwrap().unwrap()
    }
    assert_eq!(*allocate_in_small_scope(byte_pool), 5);

    fn reference_capture<'r, 'p>(byte_pool: &'p BytePool, x: &'r i32) -> Bytes<'r, &'r i32>
    where
        'p: 'r,
    {
        byte_pool.try_allocate(|| x).unwrap().unwrap()
    }
    let x = 5;
    assert_eq!(**reference_capture(byte_pool, &x), 5);
}

fn static_byte_pool() {
    static BYTE_POOL: BytePoolContext = BytePool::context();
    static STORAGE: StaticBytePoolStorage<512> = StaticBytePoolStorage::new();

    let byte_pool = BytePool::create(
        Pin::static_ref(&BYTE_POOL),
        STORAGE.take().unwrap(),
        &Default::default(),
    )
    .unwrap();
    test_byte_pool(byte_pool);
}

fn local_byte_pool_stack_storage() {
    let mut storage = AlignedBytePoolStorage::from_array([0u8; 512]);
    let byte_pool = std::pin::pin!(BytePool::context());
    let byte_pool =
        BytePool::create(byte_pool.into_ref(), &mut storage, &Default::default()).unwrap();
    test_byte_pool(byte_pool);
}

fn aligned_heap_storage<const N: usize>() -> Box<[u8]> {
    // Safety: heap-allocated aligned array, without a custom drop, can
    // be managed by a box that disregards the aligned type. We show
    // that the AlignedStorage and its only member are at the same
    // location in memory.
    //
    // TODO(mciantyre): Is there a better way to do this?
    unsafe {
        let storage = Box::new(AlignedBytePoolStorage::from_array([0; N]));
        let member: *const [u8; N] = storage.get();

        let storage: *mut AlignedBytePoolStorage<[u8; N]> = Box::into_raw(storage);
        let storage: *mut [u8; N] = storage.cast();

        assert_eq!(member, storage);
        Box::from_raw(storage)
    }
}

fn local_byte_pool_heap_storage() {
    let mut storage = aligned_heap_storage::<512>();
    let byte_pool = std::pin::pin!(BytePool::context());
    let byte_pool =
        BytePool::create(byte_pool.into_ref(), &mut storage, &Default::default()).unwrap();
    test_byte_pool(byte_pool);
}

fn local_byte_pool_byte_pool_storage() {
    let mut storage: Box<[u8]> = aligned_heap_storage::<2048>();
    let byte_pool = std::pin::pin!(BytePool::context());
    let byte_pool =
        BytePool::create(byte_pool.into_ref(), &mut storage, &Default::default()).unwrap();

    let mut storage = byte_pool
        .try_allocate(|| AlignedBytePoolStorage::from_array([0u8; 1024]))
        .unwrap()
        .unwrap();
    let byte_pool = std::pin::pin!(BytePool::context());
    let byte_pool =
        BytePool::create(byte_pool.into_ref(), &mut *storage, &Default::default()).unwrap();
    test_byte_pool(byte_pool);
}

fn storage_elsewhere() {
    let mut storage = AlignedBytePoolStorage::from_array([0u8; 512]);
    fn create_and_test_pool(storage: &mut [u8]) {
        let byte_pool = std::pin::pin!(BytePool::context());
        let byte_pool =
            BytePool::create(byte_pool.into_ref(), storage, &Default::default()).unwrap();
        test_byte_pool(byte_pool);
    }
    create_and_test_pool(storage.as_mut());
}

static STACK: StaticStack<4096> = StaticStack::new();
static THREAD: ThreadContext = Thread::context();

#[test]
fn byte_pool() {
    fusible::kernel_enter(|_| {
        Thread::create(
            Pin::static_ref(&THREAD),
            STACK.take().unwrap(),
            &Default::default(),
            || {
                static_byte_pool();
                local_byte_pool_stack_storage();
                local_byte_pool_heap_storage();
                local_byte_pool_byte_pool_storage();
                storage_elsewhere();
                std::process::exit(0);
            },
        )
        .unwrap();
    })
}
