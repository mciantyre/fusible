// SPDX-License-Identifier: MPL-2.0
// SPDX-FileCopyrightText: Copyright 2024 Ian McIntyre

//! Common helpers for memory pools.

use core::{alloc::Layout, marker::PhantomData, mem::ManuallyDrop, ptr::NonNull};

use crate::{marker::CovariantLifetime, WaitOption};

/// A general memory pool.
///
/// Both byte and block pools can act as a memory pool. Once implemented,
/// you can utilize `PoolPointer` for object management.
pub(crate) trait MemoryPool {
    /// What kinds of errors occur during memory allocation?
    type AllocateError;
    /// What kinds of errors occur when releasing memory?
    type ReleaseError;

    /// Allocate a block of memory satisfying a layout.
    ///
    /// The returned pointer is not initialized! However, the backing
    /// memory is considered to be exclusively owned by the caller.
    ///
    /// If `wait_option` represents "wait forever," then the returned
    /// pointer cannot be null. Otherwise, it is valid to return a null
    /// pointer if memory could not be allocated before the timeout.
    fn allocate_memory(
        self,
        layout: Layout,
        wait_option: WaitOption,
    ) -> Result<*mut (), Self::AllocateError>;

    /// Release a previously-allocated block of memory.
    ///
    /// Clients of this interface guarantee that `ptr` was a pointer
    /// that was previously allocated by `allocate_memory`. Clients
    /// also guarantee that `ptr` is not aliased. Clients guarnatee
    /// that the layout corresponds to the same layout provided to
    /// `allocate_memory`.
    fn release_memory(ptr: *mut (), layout: Layout) -> Result<(), Self::ReleaseError>;
}

/// Allocate `T` inside a memory pool.
///
/// # Panics
///
/// Panics if the initialization function panics. If this happens,
/// the implementation tries to release the allocated memory.
pub(crate) fn allocate_with_wait<'pool, T, P>(
    pool: P,
    wait_option: WaitOption,
    init: impl FnOnce() -> T,
) -> Result<Option<PoolPointer<'pool, T, P>>, P::AllocateError>
where
    P: MemoryPool + 'pool,
{
    let ptr = pool.allocate_memory(Layout::new::<T>(), wait_option)?;
    if ptr.is_null() {
        return Ok(None);
    }

    let ptr: *mut T = ptr.cast();

    struct ReleaseIfInitPanics<T, P: MemoryPool>(*mut T, PhantomData<P>);
    impl<T, P: MemoryPool> Drop for ReleaseIfInitPanics<T, P> {
        fn drop(&mut self) {
            drop(P::release_memory(self.0.cast(), Layout::new::<T>()));
        }
    }

    // Safety: pointer is valid for writes and owned by us.
    // The pointer points to uninitialized memory, so we should
    // not call drop on that memory; write achieves that.
    // Handle panics by deallocating the memory without dropping
    // that (still uninitialized) object.
    unsafe {
        let guarded_init = ReleaseIfInitPanics::<T, P>(ptr, PhantomData);
        ptr.write(init());
        core::mem::forget(guarded_init);
    };

    // Safety: pointer points to a valid initialized object.
    // That pointer was derived from a valid pool; that's
    // tracked by lifetimes. The pointer is not aliased, since
    // it was just created and it hasn't been passed to any
    // code that copied it.
    Ok(Some(unsafe { PoolPointer::from_raw(ptr) }))
}

/// Allocate `T` inside a memory pool, waiting forever.
pub(crate) fn allocate<'pool, T, P>(
    pool: P,
    init: impl FnOnce() -> T,
) -> Result<PoolPointer<'pool, T, P>, P::AllocateError>
where
    P: MemoryPool + 'pool,
{
    allocate_with_wait(pool, WaitOption::wait_forever(), init)
        // Safety: MemoryPool implementations cannot return a null pointer when we're waiting
        // forever. Since the pointer is never null, we'll never observe `None`; we see this
        // by study of the implementation.
        .map(|ptr| unsafe { ptr.unwrap_unchecked() })
}

/// Try to allocate `T` inside a memory pool.
///
/// Return immediately if allocation cannot happen.
pub(crate) fn try_allocate<'pool, T, P>(
    pool: P,
    init: impl FnOnce() -> T,
) -> Result<Option<PoolPointer<'pool, T, P>>, P::AllocateError>
where
    P: MemoryPool + 'pool,
{
    allocate_with_wait(pool, WaitOption::no_wait(), init)
}

/// Points to an initialized object in a memory pool.
///
/// When this exists, it's assumed that there are no other pointers
/// to the same object. Additionally, the pool is assumed to be
/// valid while the pointer exists.
#[repr(transparent)]
pub(crate) struct PoolPointer<'pool, T: ?Sized, P: MemoryPool> {
    ptr: NonNull<T>,
    release: PhantomData<P>,
    lifetime: CovariantLifetime<'pool>,
}

const _: () = const {
    struct TypeCheckMemoryPool;
    impl MemoryPool for TypeCheckMemoryPool {
        type AllocateError = ();
        type ReleaseError = ();
        fn allocate_memory(self, _: Layout, _: WaitOption) -> Result<*mut (), Self::AllocateError> {
            unimplemented!()
        }
        fn release_memory(_: *mut (), _: Layout) -> Result<(), Self::ReleaseError> {
            unimplemented!()
        }
    }
    type OptPtr<T> = Option<PoolPointer<'static, T, TypeCheckMemoryPool>>;
    assert!(size_of::<OptPtr<u32>>() == size_of::<&'static u32>());
    assert!(size_of::<OptPtr<[u32; 7]>>() == size_of::<&'static ()>());
};

impl<T: ?Sized, P: MemoryPool> Drop for PoolPointer<'_, T, P> {
    fn drop(&mut self) {
        // Safety: drop assumed to only run once per object.
        // Therefore, we only call this once.
        drop(unsafe { self.release_in_place() });
    }
}

// Safety: if the wrapped object can be sent across execution contexts,
// then so can the smart pointer. The inner lifetime prevents a sent
// pointer from outliving its pool.
unsafe impl<T: Send + ?Sized, P: MemoryPool> Send for PoolPointer<'_, T, P> {}
// Safety: if the wrapped object can be shared across execution contexts,
// then so can the smart pointer. The inner lifetime restricts how long
// that borrow can last.
unsafe impl<T: Sync + ?Sized, P: MemoryPool> Sync for PoolPointer<'_, T, P> {}

impl<'pool, T: ?Sized, P: MemoryPool> PoolPointer<'pool, T, P> {
    /// # Safety
    ///
    /// `ptr` must point to a valid object allocated in a valid memory
    /// pool of type `P`. `ptr` must not be aliased.
    unsafe fn from_raw(ptr: *mut T) -> Self {
        Self {
            // Safety: pointer must point to a valid object, per
            // user docs. A null pointer doesn't point to a valid
            // object.
            ptr: unsafe { NonNull::new_unchecked(ptr) },
            release: PhantomData,
            lifetime: CovariantLifetime::mark(),
        }
    }

    fn into_raw(pool_ptr: Self) -> *mut T {
        let Self { ptr, .. } = pool_ptr;
        core::mem::forget(pool_ptr);
        ptr.as_ptr()
    }

    pub(crate) fn as_ref(&self) -> &T {
        // Safety: pointed-to object is valid and exclusively owned
        // by us, per from_raw safety docs.
        unsafe { self.ptr.as_ref() }
    }

    pub(crate) fn as_mut(&mut self) -> &mut T {
        // Safety: pointed-to object is valid and exclusively owned
        // by us, per from_raw safety docs.
        unsafe { self.ptr.as_mut() }
    }

    /// Drop the managed object, and release the memory back to its pool.
    ///
    /// # Safety
    ///
    /// Caller must ensure that this is only called once. Remember that
    /// drop calls this method, too.
    unsafe fn release_in_place(&mut self) -> Result<(), P::ReleaseError> {
        let layout = Layout::for_value(self.as_ref());

        // Safety: Object is valid and aligned. We logically own
        // the object. We no longer reference the object after
        // dropping it.
        unsafe { self.ptr.drop_in_place() };

        P::release_memory(self.ptr.as_ptr().cast(), layout)
    }

    pub(crate) fn release(self) -> Result<(), P::ReleaseError> {
        // Safety: we take ownership of the object. We prevent
        // drop from re-running, preventing a double free.
        unsafe { ManuallyDrop::new(self).release_in_place() }
    }

    pub(crate) fn leak(pool_ptr: Self) -> &'pool mut T {
        // Safety: the pointer must be valid, per creation safety
        // docs. The lifetime of the object is tied to the
        // pool it references, so the pointer will not dangle.
        unsafe { &mut *Self::into_raw(pool_ptr) }
    }
}

impl<'pool, T, P: MemoryPool, const N: usize> PoolPointer<'pool, [T; N], P> {
    pub(crate) fn into_slice(pool_ptr: Self) -> PoolPointer<'pool, [T], P> {
        // Safety: We leak and immediately capture the pointer. If the
        // pointer were initially valid, then it remains valid. We track
        // the pointer lifetime across the call, so the pool is valid.
        unsafe { PoolPointer::from_raw(Self::into_raw(pool_ptr) as *mut [T]) }
    }
}
