// SPDX-License-Identifier: MPL-2.0
// SPDX-FileCopyrightText: Copyright 2024 Ian McIntyre

//! Byte pool services.
//!
//! A [`BytePool`] is a dynamic memory allocator. The pool manages an array of bytes
//! that you allocate. The storage size influences the pool's capacity.
//!
//! A byte pool can allocate arbitrary types of objects. This differs from
//! [`block_pool`], which can only allocate a single type of object. Byte pool requires
//! more memory and time to provide this flexibility.
//!
//! A byte pool's storage must have u32 alignment. Use [`AlignedBytePoolStorage`] to
//! ensure your local buffer's alignment. [`StaticBytePoolStorage`] will automatically
//! align the static storage.
//!
//! # Examples
//!
//! A static pool paired with static storage.
//!
//! ```no_run
//! use fusible::byte_pool::{StaticBytePoolStorage, BytePool, Bytes, BytePoolContext};
//! use core::pin::Pin;
//!
//! static STORAGE: StaticBytePoolStorage<1024> = StaticBytePoolStorage::new();
//! static POOL: BytePoolContext = BytePool::context();
//!
//! # (|| -> Option<()> {
//! let storage = STORAGE.take()?;
//! let pool = Pin::static_ref(&POOL);
//!
//! # let pool = (|storage| -> Result<_, fusible::byte_pool::CreateError> {
//! let pool = BytePool::create(Pin::static_ref(&POOL), storage, &Default::default())?;
//! # Ok(pool) })(storage).unwrap();
//!
//! # (|| -> Result<(), fusible::byte_pool::AllocateError> {
//! let buffer: Bytes<[u32; 6]> = pool.allocate(Default::default)?;
//! # Ok(()) })().unwrap();
//!
//! # Some(()) })().unwrap();
//! ```
//!
//! A local pool paired with local storage.
//!
//! ```no_run
//! use fusible::byte_pool::{AlignedBytePoolStorage, BytePool, Bytes};
//! use core::pin::pin;
//!
//! # (|| -> Result<(), fusible::byte_pool::CreateError> {
//! let mut storage = AlignedBytePoolStorage::from_array([0; 512]);
//! let pool = pin!(BytePool::context());
//!
//! let pool = BytePool::create(pool.into_ref(), &mut storage, &Default::default())?;
//!
//! # (|| -> Result<(), fusible::byte_pool::AllocateError> {
//! let buffer: Bytes<[u32; 6]> = pool.allocate(Default::default)?;
//! # Ok(()) })().unwrap();
//! # Ok(()) })().unwrap();
//! ```
//!
//! # Alignment of byte blocks
//!
//! By default, ThreadX byte pools only provide pointer alignment of the byte block.
//! This doesn't suffice for objects with larger alignment requirements.
//!
//! Unlike raw ThreadX byte pools, the Fusible byte pool supports alignment requirements
//! greater than pointer alignment. If your object requires more than pointer alignment,
//! [`BytePool`] will over-allocate the block. However, if your object can make due with
//! pointer alignment, there is no additional memory required for the byte block.
//!
//! All [`BytePool`] allocation methods handle alignment. If you're a Rust user, there's
//! nothing more to do. On the other hand, If you're a C user who wants to
//! integrate with Fusible's byte pool, you must use [`fusible_byte_allocate`] and
//! [`fusible_byte_release`] to respectively allocate and release your byte blocks.
//!
//! [`block_pool`]: crate::block_pool

use core::alloc::Layout;
use core::ffi::{CStr, c_void};
use core::ops::{Deref, DerefMut};
use core::pin::Pin;

use libthreadx_sys::{UINT, ULONG};

use crate::marker::InvariantLifetime;
use crate::pool::{self, MemoryPool, PoolPointer};
use crate::tx_sys::TX_BYTE_POOL;

use crate::{ControlBlock, StaticCell, WaitOption};

error_enum! {
    /// An error when creating a byte pool.
    #[derive(Debug, Clone, Copy, PartialEq, Eq)]
    #[cfg_attr(feature = "defmt", derive(defmt::Format))]
    pub enum CreateError {
        /// The pool is already created.
        ///
        /// To avoid this error, you should only create a pool once.
        /// If you want to create a pool multiple times, you must first
        /// delete the pool.
        AlreadyCreated = crate::tx_sys::TX_POOL_ERROR,

        /// The storage's starting address is invalid.
        ///
        /// Make sure your storage is four-byte aligned, and that the pointer
        /// isn't null.
        InvalidPointer = crate::tx_sys::TX_PTR_ERROR,

        /// The storage's size is invalid.
        ///
        /// The size cannot be zero.
        InvalidSize = crate::tx_sys::TX_SIZE_ERROR,

        /// Invalid calling context.
        ///
        /// You can only create pools from the initialization or thread
        /// execution contexts.
        Caller = crate::tx_sys::TX_CALLER_ERROR,
    }
}

error_enum! {
    /// An error in object allocation.
    #[derive(Debug, Clone, Copy, PartialEq, Eq)]
    #[cfg_attr(feature = "defmt", derive(defmt::Format))]
    pub enum AllocateError {
        // Not handling TX_DELETED. Users cannot delete byte pools
        // while references are live.

        // Not handling TX_NO_MEMORY. We signal this by returning
        // a null pointer, and we catch that condition before
        // trying to convert result codes.

        /// The call was aborted by another entity.
        ///
        /// This happens when your software chooses to abort a thread's
        /// blocking call.
        WaitAborted = crate::tx_sys::TX_WAIT_ABORTED,

        // Not handling TX_POOL_ERROR. We use the type system to ensure that
        // pools are always created. Additionally, pools cannot be deleted
        // while references are live.

        // Not handling TX_PTR_ERROR. The implementation always provides
        // a valid pointer (to a pointer).

        /// Zero-sized allocation, or an allocation that exceeds the pool's capacity.
        ///
        /// If the size is otherwise valid and there's just not enough space in the
        /// byte pool at the moment, then the allocation blocks until it returns
        /// `WaitAborted` or until the timeout expires.
        InvalidSize = crate::tx_sys::TX_SIZE_ERROR,

        /// The wait option is invalid for the execution context.
        ///
        /// If you're allocating from a non-thread execution context, then you must
        /// use a `try_*` allocation method, or supply "no wait" as the wait option.
        InvalidWait = crate::tx_sys::TX_WAIT_ERROR,

        /// The calling execution context is invalid.
        ///
        /// You can only allocate byte blocks from initialization or thread execution
        /// contexts.
        Caller = crate::tx_sys::TX_CALLER_ERROR,
    }
}

error_enum! {
    /// An error when releasing an object.
    #[derive(Debug, Clone, Copy, PartialEq, Eq)]
    #[cfg_attr(feature = "defmt", derive(defmt::Format))]
    pub enum ReleaseError {
        /// The implementation happened to notice that the pointer is invalid.
        ///
        /// This error is not guaranteed. Therefore, releasing a byte block is
        /// `unsafe`.
        InvalidPointer = crate::tx_sys::TX_PTR_ERROR,

        /// The calling execution context is invalid.
        ///
        /// You can only release byte blocks from initialization or thread execution
        /// contexts.
        Caller = crate::tx_sys::TX_CALLER_ERROR,
    }
}

/// Helps you meet alignment requirements for byte pool storage.
///
/// Byte pools require their storage to have certain alignment. You can use
/// this adapter to align your storage allocation `S`. Normally, this `S` is
/// some kind of byte array; use [`from_array`](Self::from_array) to specify
/// the starting value for your byte pool's storage.
#[repr(C, align(4))]
#[derive(Clone, Copy)]
pub struct AlignedBytePoolStorage<S>(S);

impl<const N: usize> AlignedBytePoolStorage<[u8; N]> {
    /// Allocate a byte array aligned perfectly for a byte pool.
    #[inline]
    pub const fn from_array(array: [u8; N]) -> Self {
        Self(array)
    }
}

impl<S> AlignedBytePoolStorage<S> {
    /// Borrow the storage.
    #[inline]
    pub fn get(&self) -> &S {
        &self.0
    }
    /// Exclusively borrow the storage.
    #[inline]
    pub fn get_mut(&mut self) -> &mut S {
        &mut self.0
    }
}

impl<S> AsRef<[u8]> for AlignedBytePoolStorage<S>
where
    S: AsRef<[u8]>,
{
    #[inline]
    fn as_ref(&self) -> &[u8] {
        self.0.as_ref()
    }
}

impl<S> AsMut<[u8]> for AlignedBytePoolStorage<S>
where
    S: AsMut<[u8]>,
{
    #[inline]
    fn as_mut(&mut self) -> &mut [u8] {
        self.0.as_mut()
    }
}

/// Statically allocate `N` bytes for a byte pool.
///
/// This manages a static storage allocation of `N` bytes. It also manages
/// a "taken" flag used to track ownership. Use [`take`](Self::take) to acquire
/// the storage.
///
/// This storage is automatically for a byte pool's requirements. If the allocation
/// is zero bytes large, then this fails to compile.
///
/// # Example
///
/// ```no_run
/// use fusible::byte_pool::StaticBytePoolStorage;
///
/// static STORAGE: StaticBytePoolStorage<2048> = StaticBytePoolStorage::new();
///
/// # (|| -> Option<()> {
/// let storage = STORAGE.take()?;
/// # Some(()) })().unwrap();
/// ```
pub struct StaticBytePoolStorage<const N: usize>(StaticCell<AlignedBytePoolStorage<[u8; N]>>);

impl<const N: usize> Default for StaticBytePoolStorage<N> {
    fn default() -> Self {
        Self::new()
    }
}

impl<const N: usize> StaticBytePoolStorage<N> {
    const SIZE_IS_VALID: () = assert!(N > 0 && N <= (u32::MAX as usize));
    /// Allocate the storage.
    pub const fn new() -> Self {
        #[allow(clippy::let_unit_value)] // Force const evaluation.
        {
            let _ = Self::SIZE_IS_VALID;
        }
        Self(StaticCell::new(AlignedBytePoolStorage::from_array([0; N])))
    }

    /// Take a static, mutable reference to this storage.
    ///
    /// If the storage has already been taken, then this returns `None`.
    /// Otherwise, you can use this to create a [`BytePool`]. Despite
    /// being a slice of bytes, this slice is aligned for the byte pool
    /// requirements.
    ///
    /// The implementation uses a brief critical section to swap a `bool`.
    pub fn take(&'static self) -> Option<&'static mut [u8]> {
        self.0.take().map(AsMut::as_mut)
    }
}

/// Options for a byte pool.
#[derive(Default)]
#[non_exhaustive]
pub struct BytePoolOptions<'ctx> {
    /// The byte pool's name.
    pub name: Option<&'ctx CStr>,
}

/// A byte pool for dynamic object alloation.
///
/// The byte pool can allocate arbitrary objects. You interact with those
/// objects through a smart pointer, [`Bytes`].
///
/// The pool exclusively borrows the storage provided to `create`. You can freely
/// re-use the storage once the pool is dropped.
///
/// See [the module-level docs](crate::byte_pool) for examples showing how to create
/// and use a byte pool.
///
/// # FFI
///
/// `BytePool` is transparently a `TX_BYTE_POOL`.
#[repr(transparent)]
pub struct BytePool(ControlBlock<TX_BYTE_POOL>);

/// Manages the byte pool resource and its borrows.
///
/// You'll normally interact with byte pools through [`BytePool`].
/// However, the context lets you access already-created pool.
///
/// # FFI
///
/// The context is transparently a [`BytePool`].
#[repr(transparent)]
pub struct BytePoolContext<'ctx>(BytePool, InvariantLifetime<'ctx>);

impl Drop for BytePoolContext<'_> {
    #[inline]
    fn drop(&mut self) {
        // Safety: Resource is either created and pinned per GSG-002, or not
        // created per GSG-003. Checking lifecycle condition per GSG-003.
        unsafe {
            let result = crate::tx_sys::tx_byte_pool_delete(self.0.0.get());
            aborting_assert!(
                result == crate::tx_sys::TX_SUCCESS || result == crate::tx_sys::TX_POOL_ERROR,
                "Attempt to drop resource in the initialization context"
            );
        }
    }
}

impl BytePool {
    /// Allocate the byte pool.
    ///
    /// This does not create the byte pool, or does it register the byte pool with the
    /// operating system. You'll need to use [`create`](Self::create) for that.
    ///
    /// After you allocate your byte pool, you'll need to pin it before you can call
    /// any other methods.
    pub const fn context<'ctx>() -> BytePoolContext<'ctx> {
        BytePoolContext(BytePool(ControlBlock::new()), InvariantLifetime::mark())
    }
}

impl BytePool {
    /// Create a byte pool that uses `storage` as its storage allocation.
    ///
    /// This registers the bye pool with the operating system, enabling allocation
    /// services. `storage` is exclusively borrowed for the lifetime of the byte
    /// pool.
    pub fn create<'ctx, 'p, S>(
        pool: Pin<&'p BytePoolContext<'ctx>>,
        storage: &'ctx mut S,
        opts: &'_ BytePoolOptions<'ctx>,
    ) -> Result<&'p Self, CreateError>
    where
        S: AsMut<[u8]> + ?Sized,
    {
        // Safety: Since we have an exclusive borrow of the storage,
        // we satisfy create_unchecked's safety requirement.
        unsafe {
            let storage = storage.as_mut();
            let storage_len = storage.len();
            let storage_ptr = storage.as_mut_ptr();
            Self::create_unchecked(pool, storage_ptr, storage_len, opts)
        }
    }

    /// Create a byte pool using an external storage allocation.
    ///
    /// This registers the byte pool with the operating system, enabling allocation
    /// services. Unlike [`create`](Self::create), this method doesn't know the lifetime
    /// of the storage allocation.
    ///
    /// # Safety
    ///
    /// The storage described by the pointer-length pair must remain valid for the life of the byte pool.
    /// The caller must ensure that the storage is exclusively borrowed by the byte pool.
    pub unsafe fn create_unchecked<'p, 'ctx>(
        pool: Pin<&'p BytePoolContext<'ctx>>,
        storage_ptr: *mut u8,
        storage_len: usize,
        opts: &'_ BytePoolOptions<'ctx>,
    ) -> Result<&'p Self, CreateError> {
        // Safety: Context pinned per GSG-001. We're tracking lifetime of borrowed
        // resources (except the storage) per GSG-000.
        unsafe {
            let pool = &pool.get_ref().0;
            let result = crate::tx_sys::tx_byte_pool_create(
                pool.0.get(),
                crate::threadx_string(opts.name),
                storage_ptr.cast(),
                storage_len.try_into().unwrap_or(u32::MAX),
            );
            CreateError::try_from_result(result)?;
            Ok(pool)
        }
    }
}

impl BytePool {
    /// Allocate an object `T` in the pool.
    ///
    /// Unlike the other allocation methods, this method allows a `wait_option` for
    /// specifying timeouts. If you're calling this from a non-thread execution context,
    /// then the only valid wait option is produced by [`WaitOption::no_wait`]. In
    /// this case, consider using [`try_allocate`](Self::try_allocate).
    ///
    /// If `wait_option` is produced by [`WaitOption::wait_forever`], then this call is
    /// the same as [`allocate`](Self::allocate).
    ///
    /// `init` performs object initialization. On success, the object allocated behind
    /// the [`Bytes`] smart pointer will have the value returned by `init`.
    ///
    /// If the timeout expires and there's no memory, the return is `Ok(None)`.
    ///
    /// # Panics
    ///
    /// Panics only if `init` panics. If unwinding is enabled, then the implementation
    /// will try to release the bytes back to the pool.
    pub fn allocate_with_wait<T, F>(
        &self,
        wait_option: WaitOption,
        init: F,
    ) -> Result<Option<Bytes<'_, T>>, AllocateError>
    where
        F: FnOnce() -> T,
    {
        let ptr = pool::allocate_with_wait(self, wait_option, init)?;
        Ok(ptr.map(Bytes))
    }

    /// Allocate an object, waiting forever for memory.
    ///
    /// `init` performs object initialization. On success, the object allocated behind
    /// the [`Bytes`] smart pointer will have the value returned by `init`.
    ///
    /// If you need a timeout, use [`allocate_with_wait`](Self::allocate_with_wait).
    ///
    /// # Panics
    ///
    /// Panics only if `init` panics. If unwinding is enabled, then the implementation
    /// will try to release the bytes back to the pool.
    pub fn allocate<T, F>(&self, init: F) -> Result<Bytes<'_, T>, AllocateError>
    where
        F: FnOnce() -> T,
    {
        pool::allocate(self, init).map(Bytes)
    }

    /// Try to allocate an object, returning immediately if there's no memory.
    ///
    /// This call will never block. Therefore, it's appropriate to use in non-thread
    /// execution contexts, including ISRs and system initialization contexts.
    ///
    /// If no memory is available to satisfy the allocation, then the return is `Ok(None)`.
    ///
    /// # Panics
    ///
    /// Panics only if `init` panics. If unwinding is enabled, then the implementation
    /// will try to release the bytes back to the pool.
    pub fn try_allocate<T, F>(&self, init: F) -> Result<Option<Bytes<'_, T>>, AllocateError>
    where
        F: FnOnce() -> T,
    {
        let ptr = pool::try_allocate(self, init)?;
        Ok(ptr.map(Bytes))
    }

    /// Acquire runtime byte pool information.
    pub fn info(&self) -> BytePoolInfo<'_> {
        // Safety: GSG-002. ThreadX returns a c-string for
        // the name, and we tie the name lifetime to the pool's
        // lifetime. The service doesn't capture pointers to
        // local memory.
        unsafe {
            let mut info = BytePoolInfo::default();
            let mut name: *mut core::ffi::c_char = core::ptr::null_mut();

            let result = crate::tx_sys::tx_byte_pool_info_get(
                self.0.get(),
                &mut name,
                &mut info.available_bytes,
                &mut info.fragments,
                core::ptr::null_mut(),
                core::ptr::null_mut(),
                core::ptr::null_mut(),
            );
            debug_assert_eq!(result, crate::tx_sys::TX_SUCCESS);

            info.name = crate::from_threadx_string(name);
            info
        }
    }

    /// Reprioritize the highest-priority thread blocked on this byte pool.
    ///
    /// By default, threads block on byte pools in FIFO order. This call changes
    /// the policy: it takes the highest-priority thread that's waiting on the
    /// pool, and it puts it at the front of the wait list. All other threads
    /// remain in their FIFO ordering.
    pub fn prioritize(&self) {
        // Safety: Success / failure has no bearing on memory safety.
        // If we're not created, then the call returns with an error
        // but does nothing.
        //
        // Although the caller requires a &self, module inspection
        // reveals that this control block is pinned in memory. If
        // we've been created, then this call will use a valid control
        // block.
        unsafe {
            let result = crate::tx_sys::tx_byte_pool_prioritize(self.0.get());
            debug_assert_eq!(result, crate::tx_sys::TX_SUCCESS);
        }
    }
}

impl BytePoolContext<'_> {
    impl_common_context!(BytePool);
}

/// # Safety
///
/// `malloc` must return a unique allocation for a given number of bytes.
/// If `malloc` cannot do that, it must return a null pointer.
///
/// `free` must be available to deallocate the pointer produced by `malloc`
/// in case of any error.
unsafe fn aligned_malloc<
    Malloc: FnOnce(*mut *mut c_void, ULONG) -> UINT,
    Free: FnOnce(*mut c_void),
>(
    memory_ptr: *mut *mut c_void,
    memory_size: ULONG,
    memory_align: ULONG,
    malloc: Malloc,
    free: Free,
) -> UINT {
    if !memory_align.is_power_of_two() {
        return crate::tx_sys::TX_SIZE_ERROR;
    } else if memory_ptr.is_null() {
        return crate::tx_sys::TX_PTR_ERROR;
    }

    let total_size: Option<ULONG> = Some(POINTER_SIZE)
        .and_then(|total_size| total_size.checked_add(memory_size))
        .and_then(|total_size| total_size.checked_add(memory_align))
        .and_then(|total_size| total_size.checked_sub(1));
    let Some(total_size) = total_size else {
        return crate::tx_sys::TX_SIZE_ERROR;
    };

    let mut start: *mut c_void = core::ptr::null_mut();
    let result = malloc(&mut start, total_size);
    if crate::tx_sys::TX_SUCCESS != result {
        return result;
    }

    // Check that claim about pointer alignment...
    const _: () = assert!(align_of::<*mut c_void>() == align_of::<crate::tx_sys::ALIGN_TYPE>());
    if !start.cast::<*mut c_void>().is_aligned() {
        free(start);
        return crate::tx_sys::TX_PTR_ERROR;
    }

    // We need space to fit the pointer...
    //
    // Safety: if malloc succeeded, then the pointer is valid for total_size.
    // Since total_size is at least as large as a pointer, this increment remains
    // in bounds of the allocation.
    let beyond_header: *mut c_void = unsafe { start.byte_add(size_of::<*mut c_void>()) };

    // Now find the address for aligning the user's data.
    //
    // Safety: All erroneous conversions are handled. We ensure that the alignment
    // offset remains in bounds of the allocation, taking care to handle the pointer-
    // worth of data we already incremented beyond. If the alignment offset is less
    // than the remaining size of the allocation, the pointer offset remains in range.
    let data = unsafe {
        let align_offset = beyond_header.align_offset({
            let Ok(memory_align) = memory_align.try_into() else {
                free(start);
                return crate::tx_sys::TX_SIZE_ERROR;
            };
            memory_align
        });
        if align_offset.try_into().unwrap_or(ULONG::MAX) >= total_size - POINTER_SIZE {
            free(start);
            return crate::tx_sys::TX_PTR_ERROR;
        }
        beyond_header.byte_add(align_offset)
    };

    // Store the starting address provided by the allocator.
    //
    // Safety: Given the above pointer movements, this may not be an
    // aligned address for a pointer. Nevertheless, we've reserved at
    // least the space we needed for the pointer.
    unsafe {
        data.cast::<*mut c_void>()
            .sub(1 /* Pointers-worth */)
            .write_unaligned(start);

        memory_ptr.write(data.cast());
    }

    result
}

/// # Safety
///
/// `ptr` must have been allocated by `aligned_malloc`. The `free` allocation argument
/// must correspond to the `malloc` allocation argument.
unsafe fn aligned_free<Free: FnOnce(*mut c_void) -> UINT>(
    memory_ptr: *mut c_void,
    free: Free,
) -> UINT {
    // Safety: Caller ensures that this was allocated usin aligned_malloc.
    // aligned_malloc performed an unaligned write one pointers-worth of space
    // behind this pointer. In that write, it stored the pointer provided by
    // malloc.
    unsafe {
        let start: *mut c_void = memory_ptr
            .cast::<*mut c_void>()
            .sub(1 /* Pointers-worth */)
            .read_unaligned();
        free(start)
    }
}

#[allow(clippy::cast_possible_truncation)]
const POINTER_ALIGNMENT: ULONG = align_of::<*mut ()>() as ULONG;

#[allow(clippy::cast_possible_truncation)]
const POINTER_SIZE: ULONG = size_of::<*mut ()>() as ULONG;

/// Allocate bytes of memory while considering object alignment.
///
/// This behaves almost like [`tx_byte_allocate`]. However, it includes `memory_align`, a
/// power-of-two alignment requirement for the allocated byte block. If `memory_align` is larger
/// than the natural alignment provided by the byte pool, then the implementation will
/// over-allocate the byte block in order to meet alignment.
///
/// You may use this function *from C* in order to integrate with Fusible's `byte_pool`
/// implementation. The byte block allocated from this function can only be released using
/// [`fusible_byte_release`].
///
/// # Safety
///
/// This has the same safety requirements as [`tx_byte_allocate`]. Namely, the byte pool must
/// be valid, and `memory_ptr` must be valid. The returned pointer can only be accessed up to
/// `memory_size` bytes away from the start.
///
/// You must ensure that the symbol named `fusible_byte_allocate` is implemented by
/// this crate.
///
/// # Return Values
///
/// If the alignment is not a power-of-two, then the return is `TX_SIZE_ERROR`. Additionally,
/// if computing anything related to size or alignment could overflow, then the return is
/// `TX_SIZE_ERROR`.
///
/// If there is no way to provide an aligned allocation, then the return is `TX_PTR_ERROR`.
/// Otherwise, the implementation produces the same return of [`tx_byte_allocate`].
///
/// [`tx_byte_allocate`]: libthreadx_sys::error_checked::tx_byte_allocate
// Safety: Caller swears that this package provides the implementation of this function.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn fusible_byte_allocate(
    pool_ptr: *mut TX_BYTE_POOL,
    memory_ptr: *mut *mut c_void,
    memory_size: ULONG,
    memory_align: ULONG,
    wait_option: ULONG,
) -> UINT {
    // Safety: Caller required to ensure that the byte pool and pointer (to a pointer)
    // is valid. Inspection of aligned_malloc shows that the free function is always
    // called with the pointer produced by tx_byte_allocate.
    unsafe {
        if memory_align > POINTER_ALIGNMENT {
            aligned_malloc(
                memory_ptr,
                memory_size,
                memory_align,
                |memory_ptr, memory_size| {
                    crate::tx_sys::tx_byte_allocate(pool_ptr, memory_ptr, memory_size, wait_option)
                },
                |memory_ptr| {
                    crate::tx_sys::tx_byte_release(memory_ptr);
                },
            )
        } else {
            crate::tx_sys::tx_byte_allocate(pool_ptr, memory_ptr, memory_size, wait_option)
        }
    }
}

/// Release aligned bytes back to the memory pool.
///
/// This behaves like [`tx_byte_release`]. However, `memory_ptr` must have been allocated
/// using [`fusible_byte_allocate`], and `memory_align` must be the same value provided
/// to [`fusible_byte_allocate`].
///
/// On success, this will release the byte block. This function is the release function
/// used throughout `byte_pool`.
///
/// You may use this function *from C* in order to integrate with Fusible's `byte_pool`
/// implementation. If you're a Rust caller, prefer [`release`], or use the safer
/// allocation methods available on [`BytePool`].
///
/// All returns from this function are the same as [`tx_byte_release`].
///
/// # Safety
///
/// `memory_ptr` must have been allocated using [`fusible_byte_allocate`].
/// The caller must prevent others from using the byte block after it's released.
///
/// `memory_align` must be the same value provided to `fusible_byte_allocate`.
///
/// This byte block is associated with a byte pool and a storage allocation. The
/// the byte pool and its storage must be valid.
///
/// You must ensure that the symbol named `fusible_bye_release` is implemented by
/// this crate.
///
/// [`tx_byte_release`]: libthreadx_sys::error_checked::tx_byte_release
// Safety: Caller swears that this package provides the implementation of this function.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn fusible_byte_release(
    memory_ptr: *mut c_void,
    memory_align: ULONG,
) -> UINT {
    // Safety: Caller meets the safety guarantees.
    unsafe {
        if memory_align > POINTER_ALIGNMENT {
            aligned_free(memory_ptr, |memory_ptr| {
                crate::tx_sys::tx_byte_release(memory_ptr)
            })
        } else {
            crate::tx_sys::tx_byte_release(memory_ptr)
        }
    }
}

/// Allocate a byte block, considering alignment and memory footprint.
///
/// This is a simple Rust wrapper around [`fusible_byte_allocate`]. Prefer
/// this function if you're a Rust user seeking a lower-level allocation function.
/// For a nicer API, prefer the allocation methods available on [`BytePool`].
///
/// A "no memory" condition, which occurs when the timeout expires, is signaled by
/// a null pointer wrapped in `Ok`.
#[inline]
pub fn allocate(
    pool: &BytePool,
    layout: Layout,
    wait_option: WaitOption,
) -> Result<*mut u8, AllocateError> {
    pool.allocate_raw(layout, wait_option)
}

/// Release a byte block allocated by [`allocate`].
///
/// This is a simple Rust wrapper around [`fusible_byte_release`]; see its documentation
/// for more information.
///
/// # Safety
///
/// See [`fusible_byte_release`] safety documentation.
#[inline]
pub unsafe fn release(memory_ptr: *mut u8, layout: Layout) -> Result<(), ReleaseError> {
    // Safety: Caller responsible for meeting the safety contract of
    // the unsafe call we're performing.
    unsafe {
        let result = fusible_byte_release(
            memory_ptr.cast(),
            // If the alignment is so big that it overflows, take the code path
            // that will handle the "greater than pointer alignment" deallocation.
            // Twice the pointer alignment is another power of two that is greater
            // than pointer alignment. Force compile-time evaluation to show that
            // multiplication doesn't overflow.
            layout
                .align()
                .try_into()
                .unwrap_or(const { POINTER_ALIGNMENT * 2 }),
        );
        ReleaseError::try_from_result(result)?;
        Ok(())
    }
}

impl BytePool {
    fn allocate_raw(
        &self,
        layout: Layout,
        wait_option: WaitOption,
    ) -> Result<*mut u8, AllocateError> {
        // Safety: The pool is created and pinned, per GSG-002. Shown via
        // module inspection.
        //
        // If allocation succeeds, then we're the exclusive owner of the
        // byte block. We implicitly move this ownership into the caller.
        unsafe {
            let mut memory_ptr: *mut c_void = core::ptr::null_mut();
            let memory_size: ULONG = layout
                .size()
                .try_into()
                .map_err(|_| AllocateError::InvalidSize)?;
            let memory_align = layout
                .align()
                .try_into()
                .map_err(|_| AllocateError::InvalidSize)?;

            let result = fusible_byte_allocate(
                self.0.get(),
                &mut memory_ptr,
                memory_size,
                memory_align,
                wait_option.into(),
            );

            if crate::tx_sys::TX_NO_MEMORY == result {
                Ok(core::ptr::null_mut())
            } else {
                AllocateError::try_from_result(result)?;
                Ok(memory_ptr.cast())
            }
        }
    }
}

impl MemoryPool for &BytePool {
    type AllocateError = AllocateError;
    type ReleaseError = ReleaseError;

    fn allocate_memory(
        self,
        layout: Layout,
        wait_option: WaitOption,
    ) -> Result<*mut (), Self::AllocateError> {
        let ptr = self.allocate_raw(layout, wait_option)?;
        Ok(ptr.cast())
    }

    fn release_memory(ptr: *mut (), layout: Layout) -> Result<(), Self::ReleaseError> {
        // Safety: The byte pool must be alive, since this call dispatches
        // on a reference to a byte pool. Caller guarantees that the pointer
        // and layout provided to this function were the same produced /
        // provided to allocate_memory. The caller couldn't meet this latter
        // guarantee if the byte pool were dropped in between allocate_memory
        // and release_memory calls.
        unsafe { release(ptr.cast(), layout) }
    }
}

/// Information about a byte pool.
///
/// This information is always tracked by a byte pool. It is not affected
/// by build configurations. Use [`BytePool::info`] to query this information.
#[derive(Debug, Default)]
#[cfg_attr(feature = "defmt", derive(defmt::Format))]
#[non_exhaustive]
pub struct BytePoolInfo<'pool> {
    /// What's this pool's name?
    pub name: crate::ResourceName<'pool>,
    /// How many total bytes are available?
    pub available_bytes: u32,
    /// How many fragments are managed by the pool?
    pub fragments: u32,
}

/// A smart pointer to an object in a byte pool.
///
/// `Bytes` provides exclusive ownership of an object allocated within
/// a bytes pool. The pointer the lifetime of the associated byte
/// pool, ensuring that the smart pointer doesn't outlive the pool.
///
/// On drop, `Bytes` will drop the inner object then release the allocation
/// back to the associated byte pool. If an error occurs during drop,
/// the error is silently ignored. If you're concerned about these errors,
/// consider using [`Bytes::release`] to manually release your object.
///
/// # FFI
///
/// `Bytes<T>` is transparently a `NonNull<T>`. The pointer is valid for reads
/// and writes.
#[repr(transparent)]
pub struct Bytes<'pool, T: ?Sized>(PoolPointer<'pool, T, &'pool BytePool>);

impl<'pool, T: ?Sized> Bytes<'pool, T> {
    /// Release the allocation back to the pool.
    ///
    /// You don't have to call this; you can rely on the `Bytes`' drop
    /// implementation to clean up memory. However, you could use this to
    /// learn of any errors during release.
    pub fn release(bytes: Self) -> Result<(), ReleaseError> {
        bytes.0.release()
    }

    /// Pin the object in the pool.
    ///
    /// This is an in-place conversion that adds a [`Pin`] wrapper.
    /// Use this to indicate that your `!Unpin` data is not move-able.
    pub fn into_pin(bytes: Self) -> Pin<Self> {
        // Safety: if data is !Unpin, then user will need subsequent
        // unsafe code in order to mutably access the data.
        unsafe { Pin::new_unchecked(bytes) }
    }

    /// Leak the object in the pool.
    ///
    /// The object will not be dropped, and its memory will not be
    /// reclaimed.
    pub fn leak(bytes: Self) -> &'pool mut T {
        PoolPointer::leak(bytes.0)
    }
}

impl<T: ?Sized> Deref for Bytes<'_, T> {
    type Target = T;
    #[inline]
    fn deref(&self) -> &Self::Target {
        self.0.as_ref()
    }
}

impl<T: ?Sized> DerefMut for Bytes<'_, T> {
    #[inline]
    fn deref_mut(&mut self) -> &mut Self::Target {
        self.0.as_mut()
    }
}

impl<'pool, T, const N: usize> Bytes<'pool, [T; N]> {
    /// Convert an array into a slice.
    ///
    /// This internally re-casts the pointer into a slice. The original
    /// array will be released when the new pointer is dropped.
    #[inline]
    pub fn into_slice(bytes: Self) -> Bytes<'pool, [T]> {
        Bytes(PoolPointer::into_slice(bytes.0))
    }
}

#[cfg(test)]
mod tests {
    #![allow(clippy::undocumented_unsafe_blocks)]

    use std::vec;
    use std::vec::Vec;

    const _: () = assert!(align_of::<usize>() == align_of::<*mut u8>());

    struct ByteAlloc(Vec<usize>);
    impl ByteAlloc {
        fn new(size: usize) -> Self {
            Self(vec![0; size])
        }
        fn malloc(&mut self, size: usize) -> *mut u8 {
            assert!(size < self.0.len() * size_of::<usize>());
            self.start()
        }
        fn free(&mut self, ptr: *mut u8) {
            assert_eq!(ptr, self.start());
        }
        fn start(&mut self) -> *mut u8 {
            self.0.as_mut_ptr().cast()
        }
    }

    #[test]
    fn aligned_alloc_free_align() {
        let mut alloc = ByteAlloc::new(1024);
        for align in [1, 2, 4, 8, 16, 32, 64] {
            for size in [1, 2, 4, 5, 10, 16, 32, 40, 57, 64, 128] {
                unsafe {
                    let mut ptr: *mut core::ffi::c_void = core::ptr::null_mut();
                    super::aligned_malloc(
                        &mut ptr,
                        size,
                        align,
                        |ptr, total| {
                            assert!(total > size);
                            ptr.write(alloc.malloc(total as _).cast());
                            0
                        },
                        |_| unimplemented!(),
                    );
                    assert_eq!(ptr.align_offset(align as _), 0);
                    assert_eq!(ptr.cast::<*mut u8>().sub(1).read(), alloc.start());
                    super::aligned_free(ptr, |ptr| {
                        alloc.free(ptr.cast());
                        0
                    });
                }
            }
        }
    }

    #[test]
    fn aligned_alloc_error() {
        unsafe {
            let mut ptr: *mut core::ffi::c_void = core::ptr::null_mut();
            assert_eq!(super::aligned_malloc(&mut ptr, 37, 64, |_, _| 1, |_| ()), 1);
            assert!(ptr.is_null());
            assert_eq!(super::aligned_malloc(&mut ptr, 4, 4, |_, _| 1, |_| ()), 1);
            assert!(ptr.is_null());
        }
    }
}
