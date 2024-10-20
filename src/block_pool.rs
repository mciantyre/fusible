// SPDX-License-Identifier: MPL-2.0
// SPDX-FileCopyrightText: Copyright 2024 Ian McIntyre

//! Block pool services.
//!
//! A [`BlockPool`] is a dynamic memory allocator that allocates a single type
//! of object. The pool manages storage that you allocate. The storage size
//! influences the capacity of the pool.
//!
//! The allocator manages fixed-size blocks. Since the block size is known,
//! a block pool can provide better performance guarantees than [`byte_pool`].
//!
//! If you need a dynamc memory allocator that can allocate any type of object
//! from the same storage, use [`byte_pool`].
//!
//! # Examples
//!
//! A static block pool paired with static storage.
//!
//! ```no_run
//! use fusible::{block_pool::{BlockOf, StaticBlocks, BlockPool, BlockPoolContext}};
//! use core::pin::Pin;
//!
//! struct MyObject {
//!     x: u32,
//!     ys: [u8; 7],
//!     /* ... */
//! }
//!
//! // Static storage with capacity for 17 objects.
//! static STORAGE: StaticBlocks<MyObject, 17> = StaticBlocks::new();
//! // A static pool that can be shared across threads.
//! static POOL: BlockPoolContext<MyObject> = BlockPool::context();
//!
//! # let storage = (|| -> Option<&'static mut [BlockOf<MyObject>]> {
//! // Take ownership of the static storage.
//! let storage = STORAGE.take()?;
//! # Some(storage) })().unwrap();
//!
//! // All pools must be pinned before creation.
//! # let pool = (|storage| -> Result<_, fusible::block_pool::CreateError> {
//! let pool = BlockPool::create(Pin::static_ref(&POOL), storage, &Default::default())?;
//! # Ok(pool)})(storage).unwrap();
//!
//! # (move || -> Result<(), fusible::block_pool::AllocateError> {
//! let obj = pool.allocate(|| MyObject { x: 5, ys: [4; 7], /* ... */})?;
//! # Ok(()) })().unwrap();
//! ```
//!
//! A local pool paired with local storage.
//!
//! ```no_run
//! use fusible::block_pool::{BlockOf, BlockPool};
//! use core::pin::pin;
//!
//! type MyBlock = BlockOf<[u32; 7]>;
//!
//! # (|| -> Result<(), fusible::block_pool::CreateError> {
//! // Local storage with capacity for 31 objects.
//! let mut storage = [const { MyBlock::new() }; 31];
//!
//! // All pools must be pinned before creation.
//! let pool = pin!(BlockPool::context());
//! let pool = BlockPool::create(pool.into_ref(), &mut storage, &Default::default())?;
//!
//! # (|| -> Result<(), fusible::block_pool::AllocateError> {
//! let obj = pool.allocate(|| [0u32; 7])?;
//! # Ok(()) })().unwrap();
//! # Ok(()) })().unwrap();
//! ```
//!
//! # Limitations
//!
//! [`BlockOf`] will disallow certain types of objects from being allocated
//! in a block pool. See its documentation for more information.
//!
//! [`byte_pool`]: crate::byte_pool

use core::ffi::{c_void, CStr};
use core::mem::MaybeUninit;
use core::pin::Pin;
use core::{
    marker::PhantomData,
    ops::{Deref, DerefMut},
};

use crate::pool::{self, PoolPointer};
use crate::{
    marker::InvariantLifetime,
    pool::MemoryPool,
    tx_sys::{ALIGN_TYPE, TX_BLOCK_POOL, ULONG},
};

use crate::{ControlBlock, StaticCell, WaitOption};

/// Statically allocate `N` blocks for objects.
///
/// This manages a static storage allocation sized for `N` objects.
/// It also manages a "taken" flag used to track storage ownership.
/// Use [`take`](Self::take) to acquire the storage.
///
/// This internally uses [`BlockOf`] to size blocks. Therefore,
/// your type `T` should be the type object you want to allocate.
///
/// # Example
///
/// ```no_run
/// use fusible::block_pool::StaticBlocks;
///
/// type MyObject = [u8; 7];
/// static STORAGE: StaticBlocks<MyObject, 31> = StaticBlocks::new();
///
/// # (|| -> Option<()> {
/// let storage = STORAGE.take()?;
/// # Some(())})().unwrap();
/// ```
pub struct StaticBlocks<T, const N: usize>(StaticCell<[BlockOf<T>; N]>);

impl<T, const N: usize> Default for StaticBlocks<T, N> {
    fn default() -> Self {
        Self::new()
    }
}

impl<T, const N: usize> StaticBlocks<T, N> {
    /// Allocate static blocks.
    pub const fn new() -> Self {
        Self(StaticCell::new([const { BlockOf::new() }; N]))
    }

    /// Take a static, mutable reference to this block storage.
    ///
    /// If the storage has already been taken, then this returns `None`.
    /// Otherwise, you're given a reference to the block slice; don't
    /// lose it!
    ///
    /// The implementation uses a brief critical section to swap a `bool`.
    pub fn take(&'static self) -> Option<&'static mut [BlockOf<T>]> {
        self.0.take().map(<[BlockOf<T>; N]>::as_mut_slice)
    }
}

/// For sizing a block buffer.
///
/// When you write
///
/// ```
/// # use fusible::block_pool::{BlockOf, StaticBlocks};
/// type MyObject = [u8; 7];
/// let mut storage = [const { BlockOf::<MyObject>::new()}; 31];
/// ```
///
/// you might think that the size of the storage allocation is
/// `sizeof(u8)` * 7 * 31 bytes. However, the storage is slightly larger:
///
/// ```
/// # use fusible::block_pool::{BlockOf, StaticBlocks};
/// # type MyObject = [u8; 7];
/// # let mut storage = [const { BlockOf::<MyObject>::new()}; 31];
/// const PTR_SIZE: usize = size_of::<*mut ()>();
/// const OBJ_SIZE: usize = size_of::<MyObject>();
/// const PADDING: usize = 1;
/// assert_eq!(size_of_val(&storage), 31 * (PTR_SIZE + OBJ_SIZE + PADDING));
/// ```
///
/// The block pool allocates an extra pointer and padding for alignment of
/// subsequent blocks. `BlockOf` accounts for this additional information.
/// This means that `[BlockOf<MyObject>; 31]` has just enough capacity for 31
/// `MyObject`s.
///
/// # Limitations
///
/// The `T` allocated in the block cannot require more than pointer alignment, and it
/// must have non-zero size. These conditions are checked at build time.
///
/// ```no_run
/// // OK: a u32 satisfies the alignment and size requirements.
/// use fusible::block_pool::BlockOf;
/// BlockOf::<u32>::new();
/// # // Did this example fail to build? If yes,
/// # // Then fix the compile_fail example(s) below!
/// ```
/// ```compile_fail
/// // Error: more than pointer alignment.
/// # use fusible::block_pool::BlockOf;
/// #[repr(align(32))] struct BigAlign(u32);
/// BlockOf::<BigAlign>::new();
/// ```
/// ```compile_fail
/// // Error: zero-sized type.
/// # use fusible::block_pool::BlockOf;
/// BlockOf::<()>::new();
/// ```
#[repr(C)]
pub struct BlockOf<T> {
    _overhead_ptr: usize,
    _elem: MaybeUninit<T>,
}

const _: () = assert!(align_of::<BlockOf<()>>() >= align_of::<ULONG>());
const _: () = assert!(align_of::<BlockOf<()>>() >= align_of::<ALIGN_TYPE>());

impl<T> Default for BlockOf<T> {
    fn default() -> Self {
        Self::new()
    }
}

impl<T> BlockOf<T> {
    const CAN_SATISFY_ALIGNMENT: () = assert!(align_of::<T>() <= align_of::<*const ()>());

    const HAS_SIZE: () = assert!(size_of::<T>() > 0);

    /// Allocate a block for your object.
    ///
    /// You're expected to use this as the initializer in an array.
    pub const fn new() -> Self {
        #[allow(clippy::let_unit_value)] // Force evaluation to catch compile-time errors.
        {
            let _ = Self::CAN_SATISFY_ALIGNMENT;
            let _ = Self::HAS_SIZE;
        }
        Self {
            _overhead_ptr: 0,
            _elem: MaybeUninit::uninit(),
        }
    }
}

/// Options for a block pool.
#[derive(Default)]
#[non_exhaustive]
pub struct BlockPoolOptions<'ctx> {
    /// The block pool's name.
    pub name: Option<&'ctx CStr>,
}

/// A block pool for dynamic object allocation.
///
/// A `BlockPool<T>` can allocate objects of type `T`.
/// You interact with allocated objects through a smart pointer, [`Block`].
///
/// The block pool exclusively borrows the storage provided to `create`.
/// You can freely re-use the storage once the block pool is dropped.
///
/// The storage allocation must outlive the block pool allocation. If
/// the pool outlives the storage, then your program will not compile.
///
/// See [the module-level docs](crate::block_pool) for examples on how
/// to create and use a block pool.
///
/// # FFI
///
/// `BlockPool<T>` is transparently a `TX_BLOCK_POOL`, regardless of `T`.
#[repr(transparent)]
pub struct BlockPool<T: ?Sized>(ControlBlock<TX_BLOCK_POOL>, PhantomData<T>);

/// Allocates the block pool and tracks its borrows.
///
/// The context manages the block pool resource, and it tracks any borrows
/// required for the block pool. See the crate-level design documentation
/// for more information on resource allocation and creation.
///
/// You'll typically interact with the context through [`BlockPool`].
/// However, the context's methods let you access an already-created block
/// pool.
///
/// # FFI
///
/// The context is transparently a [`BlockPool`].
#[repr(transparent)]
pub struct BlockPoolContext<'ctx, T>(BlockPool<T>, InvariantLifetime<'ctx>);
impl<T> Drop for BlockPoolContext<'_, T> {
    #[inline]
    fn drop(&mut self) {
        // Safety: Resource is created and pinned per GSG-002. Checking lifecycle
        // conditions per GSG-003.
        unsafe {
            let result = crate::tx_sys::tx_block_pool_delete(self.0 .0.get());
            aborting_assert!(
                result == crate::tx_sys::TX_SUCCESS || result == crate::tx_sys::TX_POOL_ERROR,
                "Attempt to drop resource in the initialization context"
            );
        }
    }
}

impl<T> BlockPool<T> {
    /// Allocate a block pool.
    ///
    /// This does not create the block pool, nor does it register the block pool
    /// with the operating system. You'll need to use [`create`](Self::create)
    /// for that.
    ///
    /// After you allocate your block pool, you'll need to pin it before you can
    /// call any other methods.
    pub const fn context<'ctx>() -> BlockPoolContext<'ctx, T> {
        BlockPoolContext(
            BlockPool(ControlBlock::new(), PhantomData),
            InvariantLifetime::mark(),
        )
    }

    /// Create a block pool that uses `blocks` for its storage allocation.
    ///
    /// This registers the block pool with the operating system, enabling allocation
    /// services. The `blocks` are exclusively borrowed for the lifetime of the block
    /// pool.
    ///
    /// On success, you're given a resource handle that lets you allocate from the
    /// pool. Creation can fail; see the error documentation for more information.
    pub fn create<'ctx, 'pool>(
        pool: Pin<&'pool BlockPoolContext<'ctx, T>>,
        blocks: &'ctx mut [BlockOf<T>],
        opts: &'_ BlockPoolOptions<'ctx>,
    ) -> Result<&'pool Self, CreateError> {
        // Safety: Since the implementation exclusively borrows
        // blocks, we have everything needed to meet create_unchecked's safety.
        unsafe {
            let block_len = blocks.len();
            let block_ptr = blocks.as_mut_ptr();
            Self::create_unchecked(pool, block_ptr, block_len, opts)
        }
    }

    /// Create a block pool using an external storage allocation.
    ///
    /// This registers the block pool with the operating system, enabling allocation
    /// services. Unlike [`create`](Self::create), this method doesn't know the lifetime
    /// of the storage allocation.
    ///
    /// On success, you're given a resource handle that lets you allocate from the
    /// pool. Creation can fail; see the error documentation for more information.
    ///
    /// # Safety
    ///
    /// `block_ptr` and `block_len` must describe a valid storage allocation with a byte
    /// size of `block_len * sizeof(BlockOf<T>)`. The storage allocation must remain valid
    /// and exclusively borrowed by the block pool until the block pool is dropped.
    pub unsafe fn create_unchecked<'ctx, 'pool>(
        pool: Pin<&'pool BlockPoolContext<'ctx, T>>,
        block_ptr: *mut BlockOf<T>,
        block_len: usize,
        opts: &'_ BlockPoolOptions<'ctx>,
    ) -> Result<&'pool Self, CreateError> {
        // Safety: Context is pinned per GSG-001. Non-storage borrows
        // are tracked by lifetime per GSG-001. Caller required to track
        // exclusive borrow of storage allocation.
        unsafe {
            let pool = pool.get_ref();

            let Ok(block_size) = size_of::<T>().try_into() else {
                return Err(CreateError::InvalidSize);
            };

            let Some(pool_size) = size_of::<BlockOf<T>>()
                .checked_mul(block_len)
                .and_then(|pool_size| pool_size.try_into().ok())
            else {
                return Err(CreateError::InvalidSize);
            };

            let result = crate::tx_sys::tx_block_pool_create(
                pool.0 .0.get(),
                crate::threadx_string(opts.name),
                block_size,
                block_ptr.cast(),
                pool_size,
            );

            CreateError::try_from_result(result)?;
            Ok(&pool.0)
        }
    }
}

impl<T> BlockPool<T> {
    /// Return runtime information associated with the block pool.
    pub fn info(&self) -> BlockPoolInfo<'_> {
        // Safety: Resource is created and pinned per GSG-002.
        // ThreadX returns a C-string for the name. The service
        // does not capture pointers to local state.
        unsafe {
            let mut info = BlockPoolInfo::default();
            let mut name: *mut core::ffi::c_char = core::ptr::null_mut();

            let result = crate::tx_sys::tx_block_pool_info_get(
                self.0.get(),
                &mut name,
                &mut info.available_blocks,
                &mut info.total_blocks,
                core::ptr::null_mut(),
                core::ptr::null_mut(),
                core::ptr::null_mut(),
            );
            debug_assert_eq!(result, crate::tx_sys::TX_SUCCESS);

            info.name = crate::from_threadx_string(name);
            info
        }
    }

    /// Allocate an object in a block.
    ///
    /// Unlike the other allocation methods, this method accepts a `wait_option` for
    /// specifying timeouts. If you're calling this from a non-thread execution context,
    /// then the only valid wait option is produced by [`WaitOption::no_wait`]. In
    /// this case, consider using [`try_allocate`](Self::try_allocate).
    ///
    /// If `wait_option` is produced by [`WaitOption::wait_forever`], then this call is
    /// the same as [`allocate`](Self::allocate).
    ///
    /// `init` performs block initialization. On success, the object allocated behind
    /// the [`Block`] smart pointer will have the value returned by `init`.
    ///
    /// If the timeout expires and there's no memory available, the return is `Ok(None)`.
    ///
    /// # Panics
    ///
    /// Panics only if `init` panics. If unwinding is enabled, the implementation
    /// will try to release the block back to the pool.
    pub fn allocate_with_wait<F: FnOnce() -> T>(
        &self,
        wait_option: WaitOption,
        init: F,
    ) -> Result<Option<Block<'_, T>>, AllocateError> {
        let ptr = pool::allocate_with_wait(BlockPoolRef(&self.0), wait_option, init)?;
        Ok(ptr.map(Block))
    }

    /// Allocate an object, waiting forever for a memory block.
    ///
    /// `init` performs block initialization. On success, the object allocated behind
    /// the [`Block`] smart pointer will have the value returned by `init`.
    ///
    /// If you need a timeout, use [`allocate_with_wait`](Self::allocate_with_wait).
    ///
    /// # Panics
    ///
    /// Panics only if `init` panics. If unwinding is enabled, the implementation
    /// will try to release the block back to the pool.
    pub fn allocate<F: FnOnce() -> T>(&self, init: F) -> Result<Block<'_, T>, AllocateError> {
        pool::allocate(BlockPoolRef(&self.0), init).map(Block)
    }

    /// Try to allocate a block, returning immediately if there's no memory.
    ///
    /// This call will never block. Therefore, it's appropriate to use in non-thread
    /// execution contexts, including ISRs and system initialization contexts.
    ///
    /// If no memory is available to satisfy the allocation, then the return is `Ok(None)`.
    ///
    /// # Panics
    ///
    /// Panics only if `init` panics. If unwinding is enabled, the implementation
    /// will try to release the block back to the pool.
    pub fn try_allocate<F: FnOnce() -> T>(&self, init: F) -> Option<Block<'_, T>> {
        // Safety: See inline comments for safety. We exhaustively match existing / new errors.
        unsafe {
            match pool::try_allocate(BlockPoolRef(&self.0), init) {
                // The above call uses "no wait" as its wait option. The wait option
                // is valid for all calling contexts.
                Err(AllocateError::InvalidWait) => core::hint::unreachable_unchecked(),
                // The above call uses "no wait" as its wait option. Since it doesn't
                // wait, it cannot be aborted.
                Err(AllocateError::WaitAborted) => core::hint::unreachable_unchecked(),
                Ok(ptr) => ptr.map(Block),
            }
        }
    }
}

impl<T> BlockPoolContext<'_, T> {
    impl_common_context!(BlockPool<T>);
}

/// Information about a block pool.
///
/// This information is always tracked by a block pool. It is not affected
/// by build configurations. Use [`BlockPool::info`] to query this information.
#[derive(Default)]
#[non_exhaustive]
pub struct BlockPoolInfo<'pool> {
    /// What's this pool's name?
    pub name: crate::ResourceName<'pool>,
    /// How many blocks (objects) could be allocated?
    pub available_blocks: u32,
    /// What's the capacity of the pool?
    pub total_blocks: u32,
}

error_enum! {
    /// An error in block pool creation.
    #[derive(Debug, Clone, Copy, PartialEq, Eq)]
    #[cfg_attr(feature = "defmt", derive(defmt::Format))]
    pub enum CreateError {
        /// The pool is already created.
        ///
        /// To avoid this error, you should only create a pool once.
        /// If you want to use the same storage allocation for a different
        /// pool, you'll need to drop the pool that's using the allocation.
        AlreadyCreated = crate::tx_sys::TX_POOL_ERROR,

        /// The storage's starting address is invalid.
        ///
        /// The pointer cannot be null, and the referenced object should be
        /// four-byte aligned.
        InvalidPointer = crate::tx_sys::TX_PTR_ERROR,

        /// The storage's size is invalid.
        ///
        /// The size cannot be zero. The total size of the storage, in bytes,
        /// must be representable in a `u32`.
        InvalidSize = crate::tx_sys::TX_SIZE_ERROR,

        /// Invalid calling context.
        ///
        /// You can only create pools from the initialization or thread
        /// execution contexts.
        Caller = crate::tx_sys::TX_CALLER_ERROR,
    }
}

error_enum! {
    /// An error in block allocation.
    #[derive(Debug, Clone, Copy, PartialEq, Eq)]
    #[cfg_attr(feature = "defmt", derive(defmt::Format))]
    pub enum AllocateError {
        // Not handling TX_DELETED. We use lifetime tracking to
        // ensure that pools cannot be deleted while waiting for
        // allocation. We do not provide an API to delete pools,
        // since pointers to allocated objects could still be live.

        // Not handling TX_NO_MEMORY. We signal this by returning
        // a null pointer, and we catch that condition before
        // trying to convert result codes.

        /// The call was aborted by another entity.
        ///
        /// This happens when your software chooses to abort a thread's
        /// blocking call.
        WaitAborted = crate::tx_sys::TX_WAIT_ABORTED,

        // Not handling TX_POOL_ERROR. Types and runtime checks ensure
        // that pools are created before use.

        /// The wait option is invalid for the execution context.
        ///
        /// If you're allocating from a non-thread execution context, then you must
        /// use a `try_*` allocation method, or supply "no wait" as the wait option.
        InvalidWait = crate::tx_sys::TX_WAIT_ERROR,

        // Not handling TX_PTR_ERROR. The implementation always provides
        // a valid pointer (to a pointer).
    }
}

error_enum! {
    /// An error when releasing a block.
    #[derive(Debug, Clone, Copy, PartialEq, Eq)]
    #[cfg_attr(feature = "defmt", derive(defmt::Format))]
    pub enum ReleaseError {
        /// The implementation happened to notice that the block pointer is invalid.
        InvalidPointer = crate::tx_sys::TX_PTR_ERROR,
    }
}

/// A wrapper to implement `MemoryPool` for a block pool.
///
/// Although not tracked by the type system, it's understood that
/// the control block is pinned in memory; it's part of the context,
/// and the context is pinned in memory before the user can access
/// the `BlockPool` handle.
struct BlockPoolRef<'p>(&'p ControlBlock<TX_BLOCK_POOL>);

impl MemoryPool for BlockPoolRef<'_> {
    type AllocateError = AllocateError;
    type ReleaseError = ReleaseError;

    fn allocate_memory(
        self,
        _: core::alloc::Layout,
        wait_option: WaitOption,
    ) -> Result<*mut (), Self::AllocateError> {
        // Safety: Module inspection shows that the resource is created and pinned. This
        // satisfies GSG-002.
        //
        // If allocation succeeds, then block_ptr points to memory that's exclusively
        // owned by us. This memory isn't initialized, but the caller is aware of this
        // by means of the raw pointer. The caller will make sure that the pointer is
        // properly accessed (within its bounds).
        //
        // We ignore the layout argument to allocate_memory. Module inspection shows
        // that we're always creating a type T, so all calls to this will implicitly
        // use a layout that's sufficient for T.
        unsafe {
            let mut block_ptr: *mut c_void = core::ptr::null_mut();

            let result =
                crate::tx_sys::tx_block_allocate(self.0.get(), &mut block_ptr, wait_option.into());

            if crate::tx_sys::TX_NO_MEMORY == result {
                Ok(core::ptr::null_mut())
            } else {
                AllocateError::try_from_result(result)?;
                Ok(block_ptr.cast())
            }
        }
    }

    fn release_memory(ptr: *mut (), _: core::alloc::Layout) -> Result<(), Self::ReleaseError> {
        // Safety: Callers ensure that ptr is allocated from allocate_memory. Given this
        // guarantee, we expect the block to be valid. We report if it isn't.
        //
        // The pointers produced by allocate_memory are tracked by the Block smart pointer.
        // The smart pointer ensures exclusive access to the memory. By the time this function
        // runs, the smart pointer is being dropped, and no one else can access the block.
        let result = unsafe { crate::tx_sys::tx_block_release(ptr.cast()) };
        ReleaseError::try_from_result(result)?;
        Ok(())
    }
}

/// A smart pointer to an object in a block pool.
///
/// `Block` provides exclusive ownership of an object allocated within
/// a block pool. The block tracks the lifetime of the associated block
/// pool, ensuring that the smart pointer doesn't outlive the pool.
///
/// On drop, `Block` will drop the inner object then release the block
/// back to the associated block pool. If an error occurs during drop,
/// the error is silently ignored. If you're concerned about these errors,
/// consider using [`Block::release`] to manually release your block.
///
/// # FFI
///
/// A `Block` is transparently a `NonNull<T>`. The pointer is valid for reads
/// and writes.
#[repr(transparent)]
pub struct Block<'pool, T: ?Sized>(PoolPointer<'pool, T, BlockPoolRef<'pool>>);

impl<'pool, T: ?Sized> Block<'pool, T> {
    /// Release the block back to the pool.
    ///
    /// You don't have to call this; you can rely on the `Block`'s drop
    /// implementation to clean up memory. However, you could use this to
    /// learn of any errors during block release.
    pub fn release(block: Self) -> Result<(), ReleaseError> {
        block.0.release()
    }

    /// Pin the object in the pool.
    ///
    /// This is an in-place conversion that adds a [`Pin`] wrapper.
    /// Use this to indicate that your `!Unpin` data is not move-able.
    pub fn into_pin(block: Self) -> Pin<Self> {
        // Safety: if data is !Unpin, then user will need subsequent
        // unsafe code in order to mutably access the data.
        unsafe { Pin::new_unchecked(block) }
    }

    /// Leak the object in the pool.
    ///
    /// The object will not be dropped, and its memory will not be
    /// reclaimed.
    pub fn leak(block: Self) -> &'pool mut T {
        PoolPointer::leak(block.0)
    }
}

impl<T: ?Sized> Deref for Block<'_, T> {
    type Target = T;
    #[inline]
    fn deref(&self) -> &Self::Target {
        self.0.as_ref()
    }
}

impl<T: ?Sized> DerefMut for Block<'_, T> {
    #[inline]
    fn deref_mut(&mut self) -> &mut Self::Target {
        self.0.as_mut()
    }
}

impl<'pool, T, const N: usize> Block<'pool, [T; N]> {
    /// Convert an array into a slice.
    ///
    /// This internally re-casts the pointer into a slice. The original
    /// array will be released when the new pointer is dropped.
    #[inline]
    pub fn into_slice(block: Self) -> Block<'pool, [T]> {
        Block(PoolPointer::into_slice(block.0))
    }
}
