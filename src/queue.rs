// SPDX-License-Identifier: MPL-2.0
// SPDX-FileCopyrightText: Copyright 2024 Ian McIntyre

//! Queue services.
//!
//! [`Queue<T>`] provides inter-thread communication. Multiple threads can send
//! and receive objects of type `T`. Threads can suspend when sending or receiving
//! these objects.
//!
//! Each [`Queue`] tracks external storage, called [`QueueSlot`]s,
//! that you allocate. The number of slots influences the capacity of the queue.
//!
//! # Examples
//!
//! A static queue paired with static storage.
//!
//! ```no_run
//! use fusible::queue::{StaticQueueSlots, Queue, QueueContext};
//! use core::pin::Pin;
//!
//! struct MyObject(u32);
//!
//! static SLOTS: StaticQueueSlots<MyObject, 32> = StaticQueueSlots::new();
//! static QUEUE: QueueContext<MyObject> = Queue::context();
//!
//! # (|| -> Option<()> {
//! let slots = SLOTS.take()?;
//!
//! # let queue = (|slots| -> Result<&Queue<MyObject>, fusible::queue::CreateError> {
//! let queue = Queue::create(Pin::static_ref(&QUEUE), slots, &Default::default())?;
//! # Ok(queue) })(slots).unwrap();
//!
//! let mut obj = MyObject(5);
//! loop {
//!     match queue.try_send(obj) {
//!         // Object was sent!
//!         None => break,
//!         // Timeout; the object wasn't sent.
//!         Some(retry) => { obj = retry; },
//!     }
//! }
//! # (|| -> Result<(), fusible::queue::ReceiveError> {
//! let obj = queue.receive()?;
//! # Ok(()) })().unwrap();
//! # Some(()) })().unwrap();
//! ```
//!
//! A local queue paired with local storage.
//!
//! ```no_run
//! use fusible::queue::{Queue, QueueSlot};
//! use core::pin::pin;
//!
//! struct MyObject(u32);
//!
//! # (|| -> Result<(), fusible::queue::CreateError> {
//! let mut slots = [const { QueueSlot::<MyObject>::new() }; 32];
//! let queue = pin!(Queue::context());
//! let queue = Queue::create(queue.into_ref(), &mut slots, &Default::default())?;
//!
//! let mut obj = MyObject(5);
//! loop {
//!     match queue.try_send(obj) {
//!         // Object was sent!
//!         None => break,
//!         // Timeout; the object wasn't sent.
//!         Some(retry) => { obj = retry; },
//!     }
//! }
//! # (|| -> Result<(), fusible::queue::ReceiveError> {
//! let obj = queue.receive()?;
//! # Ok(()) })().unwrap();
//! # Ok(()) })().unwrap();
//! ```

use core::ffi::CStr;
use core::pin::Pin;
use core::{marker::PhantomData, mem::MaybeUninit};

use crate::marker::InvariantLifetime;
use crate::tx_sys::TX_QUEUE;

use crate::{ControlBlock, StaticCell, WaitOption};

error_enum! {
    /// An error when sending on a queue.
    #[derive(Debug, Clone, Copy, PartialEq, Eq)]
    #[cfg_attr(feature = "defmt", derive(defmt::Format))]
    pub enum SendError {
        // Not handling TX_DELETED. A safe user cannot delete the
        // queue while pinned references exist.

        // Not handling TX_QUEUE_FULL. That's handled separately as
        // a success pathway.

        /// The call was aborted by another entity.
        ///
        /// This happens when your software chooses to abort a thread's
        /// blocking call.
        WaitAborted = crate::tx_sys::TX_WAIT_ABORTED,

        // Not handling TX_QUEUE_ERROR. A safe user cannot access the
        // (pinned) queue control block without going through MaybeInert,
        // a type state that checks creation.

        // Not handling TX_PTR_ERROR. Rust requires that all references
        // are valid, so we can never supply an invalid pointer.

        /// The wait option is invalid for the calling context.
        ///
        /// If you're sending on a queue in a non-thread execution context,
        /// then your wait option can only be "no wait."
        InvalidWait = crate::tx_sys::TX_WAIT_ERROR,
    }
}

error_enum! {
    /// An error when receiving from a queue.
    #[derive(Debug, Clone, Copy, PartialEq, Eq)]
    #[cfg_attr(feature = "defmt", derive(defmt::Format))]
    pub enum ReceiveError {
        // Not handling TX_DELETED. A safe user cannot delete the
        // queue while pinned references exist.

        // Not handling TX_QUEUE_EMPTY. That's handled as an option
        // in the success pathway.

        /// The call was aborted by another entity.
        ///
        /// This happens when your software chooses to abort a thread's
        /// blocking call.
        WaitAborted = crate::tx_sys::TX_WAIT_ABORTED,

        // Not handling TX_QUEUE_ERROR. A safe user cannot access the
        // (pinned) queue control block without going through MaybeInert,
        // a type state that checks creation.

        // Not handling TX_PTR_ERROR. Rust requires that all references
        // are valid, so we can never supply an invalid pointer.

        /// The wait option is invalid for the calling context.
        ///
        /// If you're sending on a queue in a non-thread execution context,
        /// then your wait option can only be "no wait."
        InvalidWait = crate::tx_sys::TX_WAIT_ERROR,
    }
}

error_enum! {
    /// An error when creating a queue.
    #[derive(Debug, Clone, Copy, PartialEq, Eq)]
    #[cfg_attr(feature = "defmt", derive(defmt::Format))]
    pub enum CreateError {
        /// The queue is already created.
        AlreadyCreated = crate::tx_sys::TX_QUEUE_ERROR,

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
        /// You can only create queues from the initialization or thread
        /// execution contexts.
        Caller = crate::tx_sys::TX_CALLER_ERROR,
    }
}

/// Options for a queue.
#[derive(Default)]
#[non_exhaustive]
pub struct QueueOptions<'ctx> {
    /// The queue's name.
    pub name: Option<&'ctx CStr>,
}

/// A multi-produce, multi-consumer queue.
///
/// A `Queue<T>` holds elements of type `T` in FIFO order. To push elements into the
/// queue, use
///
/// - [`send`](Self::send) if you're willing to wait forever for space.
/// - [`try_send`](Self::try_send) for non-blocking sends.
/// - [`send_with_wait`](Self::send_with_wait) for sending with a timeout.
///
/// To pop elements from the queue, use
///
/// - [`receive`](Self::receive) if you're willing to wait forever for an element.
/// - [`try_receive`](Self::try_receive) for non-blocking receives.
/// - [`receive_with_wait`](Self::receive_with_wait) for receiving with a timeout.
///
/// See [the module-level documentation](crate::queue) for examples.
///
/// # Dropping a queue
///
/// When `Queue` is dropped, it will individually drop all elements remaining
/// in the queue. This is linear time, based on the number of elements in the
/// queue. Then, the `Queue` is deleted.
///
/// # FFI
///
/// `Queue<T>` is transparently a `TX_QUEUE`, regardless of `T`.
#[repr(transparent)]
pub struct Queue<T>(ControlBlock<TX_QUEUE>, PhantomData<T>);

/// Manages the queue control block and borrowed data.
///
/// Use [`Queue`] to interact with a context. The context provides
/// methods for accessing an already-created queue.
///
/// # FFI
///
/// The context is transparently a [`Queue<T>`].
#[repr(transparent)]
pub struct QueueContext<'ctx, T>(Queue<T>, InvariantLifetime<'ctx>);

impl<T> Drop for QueueContext<'_, T> {
    fn drop(&mut self) {
        // If we're dropping the queue, then all (pinned) references to the
        // memory are no longer alive. We're the exclusive owner of the queue.
        //
        // Use a try_receive() so that we don't block forever, and so that we
        // can drop within any execution context. If the queue wasn't created,
        // then we'll immediately error; no harm done.
        //
        // Unfortunately, this is linear time for all types. If the type were Copy,
        // we could use tx_queue_flush to update internal pointers without calling
        // each element's drop, which should be constant time. I don't know how
        // to conveniently express that today, so that's TBD.
        //
        // If the user's drop code panics, we cannot leave the queue in an un-deleted
        // state. We could stop trying to drop the data, effectively leaking elements
        // within the queue slots. But this is a louder way to signal that something
        // went wrong.
        while let Some(elem) = self.0.try_receive() {
            crate::panic::abort_on_panic(core::panic::AssertUnwindSafe(move || drop(elem)));
        }

        // Safety: Created and pinned per GSG-002, or not created per GSG003.
        // Checking lifecycle conditions per GSG-003.
        unsafe {
            let result = crate::tx_sys::tx_queue_delete(self.0.0.get());
            aborting_assert!(
                result == crate::tx_sys::TX_SUCCESS || result == crate::tx_sys::TX_QUEUE_ERROR,
                "Attempt to drop resource in the initialization context"
            );
        }
    }
}

impl<T> Queue<T> {
    /// Allocate a queue.
    ///
    /// This does not create the queue, nor does it register the queue with
    /// the operating system. You'll need to use [`create`](Self::create)
    /// for that.
    ///
    /// After you allocate your queue, you'll need to pin it before you can
    /// call any other methods.
    pub const fn context<'ctx>() -> QueueContext<'ctx, T> {
        QueueContext(
            Queue(ControlBlock::new(), PhantomData),
            InvariantLifetime::mark(),
        )
    }
}

impl<T> Queue<T> {
    /// Create a queue that uses `slots` for element storage.
    ///
    /// This registers the queue with the operating system, enabling communication
    /// services.
    pub fn create<'ctx, 'q>(
        context: Pin<&'q QueueContext<'ctx, T>>,
        slots: &'ctx mut [QueueSlot<T>],
        opts: &'_ QueueOptions<'ctx>,
    ) -> Result<&'q Queue<T>, CreateError> {
        // Safety: by taking a mutable reference to the slots, we take
        // an exclusive borrow of that memory. The lifetime of the slots
        // must outlive the context, thanks to the lifetime setup.
        unsafe {
            let slots_len = slots.len();
            let slots_ptr = slots.as_mut_ptr();
            Self::create_unchecked(context, slots_ptr, slots_len, opts)
        }
    }
}

impl<T> Queue<T> {
    /// Create a queue using an external storage allocation.
    ///
    /// This registers the queue with the operating system, enabling communication
    /// services. Unlike [`create`](Self::create), this method doesn't know the
    /// lifetime of the storage allocation.
    ///
    /// # Safety
    ///
    /// `slots_ptr` and `slots_len` must describe a valid storage allocation. The
    /// storage must remain valid and exclusively borrowed by the queue until the queue
    /// is dropped. The size of that allocation must be at least `slots_len * sizeof(QueueSlots<T>)`.
    pub unsafe fn create_unchecked<'ctx, 'q>(
        queue: Pin<&'q QueueContext<'ctx, T>>,
        slots_ptr: *mut QueueSlot<T>,
        slots_len: usize,
        opts: &'_ QueueOptions<'ctx>,
    ) -> Result<&'q Queue<T>, CreateError> {
        // Safety: Queue context pinned per GSG-001. Context tracking the lifetime
        // of the borrowed name per GSG-000. The caller claims that the slot allocation
        // lives at least as long as the context, and that it's exclusively borrowed
        // by the context.
        unsafe {
            let queue = &queue.get_ref().0;

            let message_size: crate::tx_sys::ULONG = QueueSlot::<T>::message_size()
                .try_into()
                .map_err(|_| CreateError::InvalidSize)?;

            let queue_size = size_of::<QueueSlot<T>>()
                .checked_mul(slots_len)
                .ok_or(CreateError::InvalidSize)?
                .try_into()
                .map_err(|_| CreateError::InvalidSize)?;

            let result = crate::tx_sys::tx_queue_create(
                queue.0.get(),
                crate::threadx_string(opts.name),
                message_size,
                slots_ptr.cast(),
                queue_size,
            );
            CreateError::try_from_result(result)?;
            Ok(queue)
        }
    }

    /// Acquire runtime queue information.
    pub fn info(&self) -> QueueInfo<'_> {
        // Safety: GSG-002. No pointers are held beyond the call.
        // The info call returns a c-string for the name. We tie
        // the lifetime of that name to the queue, a lifetime
        // less than the context.
        unsafe {
            let mut info = QueueInfo::default();
            let mut name: *mut core::ffi::c_char = core::ptr::null_mut();

            let result = crate::tx_sys::tx_queue_info_get(
                self.0.get(),
                &mut name,
                &mut info.enqueued,
                &mut info.available_storage,
                core::ptr::null_mut(),
                core::ptr::null_mut(),
                core::ptr::null_mut(),
            );

            debug_assert_eq!(result, crate::tx_sys::TX_SUCCESS);
            info.name = crate::from_threadx_string(name);
            info
        }
    }

    /// Push data into the queue, blocking until the element is accepted.
    ///
    /// This is effectively [`send_with_wait`](Self::send_with_wait) with a
    /// "wait forever" wait option. This method can only be used from thread
    /// execution contexts.
    ///
    /// If an error occurs, the error path returns `elem` to you.
    pub fn send(&self, elem: T) -> Result<(), (SendError, T)> {
        // Safety: if we're waiting forever, then we'll never see TX_QUEUE_FULL.
        // If we never see TX_QUEUE_FULL, then we'll never return Some(elem).
        unsafe {
            match self.send_with_wait(elem, WaitOption::wait_forever())? {
                None => Ok(()),
                Some(_) => fusible_unreachable!(),
            }
        }
    }

    /// Try to push data into the queue.
    ///
    /// This is effectively [`send_with_wait`](Self::send_with_wait) with a
    /// "no wait" wait option. This method can be used in all non-thread execution
    /// contexts, like ISRs.
    ///
    /// # Timeouts are OK
    ///
    /// If the queue is full and there is no other error, then this call returns
    /// immediately. To understand if your `elem` was sent, check the value wrapped
    /// in `Ok`.
    ///
    /// If `elem` could not be enqueued in the queue, then the success path contains
    /// your `elem`, represented as `Ok(Some(elem))`. Otherwise, if `elem` was enqueued,
    /// then the succes path contains nothing, represented as `Ok(None)`.
    pub fn try_send(&self, elem: T) -> Option<T> {
        // Safety: see inline comments. We exhaustively match existing / future errors.
        unsafe {
            match self.send_with_wait(elem, WaitOption::no_wait()) {
                // The "no wait" option is valid for all calling contexts.
                // Since it's valid for all calling contexts, we'll never see
                // this error.
                Err((SendError::InvalidWait, _)) => fusible_unreachable!(),
                // This call does not wait. Since it does not wait, it cannot
                // be aborted.
                Err((SendError::WaitAborted, _)) => fusible_unreachable!(),
                Ok(value) => value,
            }
        }
    }

    /// Push data into the queue with configurable timeouts.
    ///
    /// For a simpler send interface, use [`try_send`](Self::try_send) or [`send`](Self::send).
    /// This interface exposes the wait option, allowing callers to handle timeouts.
    ///
    /// If an error occurs, the error path returns `elem` to you.
    ///
    /// # Timeouts are OK
    ///
    /// If the queue is full and there is no other error, then this call returns
    /// once the timeout expires. To understand if your `elem` was sent, check the
    /// value wrapped in `Ok`.
    ///
    /// If `elem` could not be enqueued in the queue, then the success path contains
    /// your `elem`, represented as `Ok(Some(elem))`. Otherwise, if `elem` was enqueued,
    /// then the succes path contains nothing, represented as `Ok(None)`.
    pub fn send_with_wait(
        &self,
        mut elem: T,
        wait_option: WaitOption,
    ) -> Result<Option<T>, (SendError, T)> {
        // Safety: pinned and created per GSG-002. Send performs a bitwise
        // copy of the data into a queue slot, only on success. We simulate
        // a move into that queue slot by forgetting the element in the
        // success path.
        unsafe {
            let result = crate::tx_sys::tx_queue_send(
                self.0.get(),
                core::ptr::from_mut::<T>(&mut elem).cast(),
                wait_option.into(),
            );

            if crate::tx_sys::TX_QUEUE_FULL == result {
                return Ok(Some(elem));
            }

            if let Err(err) = SendError::try_from_result(result) {
                Err((err, elem))
            } else {
                // The element is now owned by the queue.
                core::mem::forget(elem);
                Ok(None)
            }
        }
    }

    /// Pop data from the queue, blocking until data is available.
    ///
    /// This is effectively [`receive_with_wait`](Self::receive_with_wait) with a
    /// "wait forever" wait option. This method can only be used from thread execution
    /// contexts.
    pub fn receive(&self) -> Result<T, ReceiveError> {
        // Safety: Since we're waiting forever, we'll never see TX_QUEUE_EMPTY.
        // Since we never see TX_QUEUE_EMPTY, the option is always Some.
        Ok(unsafe {
            let maybe = self.receive_with_wait(WaitOption::wait_forever())?;
            maybe.unwrap_unchecked()
        })
    }

    /// Try to receive data from the queue.
    ///
    /// This is effectively [`receive_with_wait`](Self::receive_with_wait) with a
    /// "no wait" wait option. This method can be used in all non-thread execution
    /// contexts, like ISRs.
    ///
    /// If there is nothing available in the queue, then the result is `Ok(None)`.
    /// Otherwise, the result is `Ok(Some(elem))`.
    pub fn try_receive(&self) -> Option<T> {
        // Safety: see inline comments. We exhaustively match existing / future errors.
        unsafe {
            match self.receive_with_wait(WaitOption::no_wait()) {
                // The "no wait" option is valid for all calling contexts.
                // Since it's always valid, we'll never see this error.
                Err(ReceiveError::InvalidWait) => fusible_unreachable!(),
                // The "no wait" option never waits. Since it never waits,
                // it cannot be aborted.
                Err(ReceiveError::WaitAborted) => fusible_unreachable!(),
                Ok(value) => value,
            }
        }
    }

    /// Pop data from this queue with configurable timeouts.
    ///
    /// This interface exposes the wait option, allowing callers
    /// to handle timeouts. For a simpler receive interface, use
    /// [`try_receive`](Self::try_receive) or [`receive`](Self::try_receive).
    ///
    /// If the timeout expires and there's nothing available in the queue, then
    /// the result is `Ok(None)`. On the other hand, if something becomes available
    /// before the timeout expires, then the result is `Ok(Some(elem))`.
    pub fn receive_with_wait(&self, wait_option: WaitOption) -> Result<Option<T>, ReceiveError> {
        // Safety: Pinned and created per GSG-002. We only release the value
        // from the queue slot in the success path, the path which will initialize
        // the uninitialized memory.
        unsafe {
            let mut elem: MaybeUninit<T> = MaybeUninit::uninit();

            let result = crate::tx_sys::tx_queue_receive(
                self.0.get(),
                elem.as_mut_ptr().cast(),
                wait_option.into(),
            );

            if crate::tx_sys::TX_QUEUE_EMPTY == result {
                return Ok(None);
            }

            ReceiveError::try_from_result(result)?;

            // Result is success, so the memory is initialized.
            Ok(Some(elem.assume_init()))
        }
    }
}

impl<T> QueueContext<'_, T> {
    impl_common_context!(Queue<T>);
}

/// An element of type `T`, used for queue storage.
///
/// Allocate these in an array to use as the backing storage for your
/// [`Queue`]. If you need to allocate slots statically, use
/// [`StaticQueueSlots`].
///
/// # Example
///
/// ```no_run
/// use fusible::queue::QueueSlot;
///
/// # struct MyObject(u32);
/// let mut slots: [QueueSlot<MyObject>; 64] = [const { QueueSlot::new() }; 64];
/// ```
///
/// # Memory size and alignment
///
/// Queues require their storage to be four-byte aligned. `QueueSlot` realizes
/// this requirement. However, this means that a `QueueSlot<T>` may be larger than
/// what's required for `T`.
///
/// `T` cannot be larger than 64 bytes. This is checked at compile time.
#[repr(C, align(4))]
pub struct QueueSlot<T>(MaybeUninit<T>);

impl<T> Default for QueueSlot<T> {
    fn default() -> Self {
        Self::new()
    }
}

impl<T> QueueSlot<T> {
    /// Describe the message size in units of 32-bit words.
    ///
    /// Since Self is align(4), sizeof(Self) is at least four.
    /// See the compile-time tests, elsewhere, for a demonstration.
    const fn message_size() -> usize {
        size_of::<Self>() / size_of::<u32>()
    }

    // From Message Queues - Message Size documentation:
    //
    //      "The available message sizes are 1 through 16 32-bit words inclusive.""
    const MSG_TOO_BIG: () = assert!(Self::message_size() <= 16);
    const MSG_TOO_SMALL: () = assert!(1 <= Self::message_size());

    /// Allocate a queue slot.
    pub const fn new() -> Self {
        #[allow(clippy::let_unit_value)] // Force evaluation to catch compile-time errors.
        {
            let _ = Self::MSG_TOO_BIG;
            let _ = Self::MSG_TOO_SMALL;
        }
        Self(MaybeUninit::uninit())
    }
}

// The tests below assume a u32 is four-byte aligned.
const _: () = assert!(align_of::<u32>() == 4);
const _: () = const {
    // Bytes are rounded up, since the slot introduces padding
    // to meet alignment.
    assert!(QueueSlot::<[u8; 1]>::message_size() == 1);
    assert!(QueueSlot::<[u8; 3]>::message_size() == 1);
    assert!(QueueSlot::<[u8; 4]>::message_size() == 1);
    assert!(QueueSlot::<[u8; 5]>::message_size() == 2);
    assert!(QueueSlot::<[u8; 7]>::message_size() == 2);
    assert!(QueueSlot::<[u8; 8]>::message_size() == 2);
    assert!(QueueSlot::<[u8; 9]>::message_size() == 3);

    // There's no padding here, so the message size is perfect.
    assert!(QueueSlot::<[u32; 1]>::message_size() == 1);
    assert!(QueueSlot::<[u32; 3]>::message_size() == 3);
    assert!(QueueSlot::<[u32; 4]>::message_size() == 4);
    assert!(QueueSlot::<[u32; 5]>::message_size() == 5);
    assert!(QueueSlot::<[u32; 7]>::message_size() == 7);
    assert!(QueueSlot::<[u32; 8]>::message_size() == 8);
    assert!(QueueSlot::<[u32; 9]>::message_size() == 9);

    // Requires eight bytes (seven bytes of padding) to maintain alignment.
    // That's two u32s per type.
    #[repr(align(8))]
    struct NeedsMoreAlignment(u8);
    assert!(QueueSlot::<[NeedsMoreAlignment; 1]>::message_size() == 2);
    assert!(QueueSlot::<[NeedsMoreAlignment; 2]>::message_size() == 4);
    assert!(QueueSlot::<[NeedsMoreAlignment; 3]>::message_size() == 6);
    assert!(QueueSlot::<[NeedsMoreAlignment; 57]>::message_size() == 57 * 2);
};

/// Statically allocated `N` slots for objects.
///
/// This manages a static storage allocation sized for `N` objects of type `T`.
/// It also manages a "taken" flag used to track storage ownership. Use
/// [`take`](Self::take) to acquire the storage.
///
/// This internally uses [`QueueSlot`]. Therefore, your type `T` should be the
/// type of elements sent across the queue.
///
/// # Example
///
/// ```no_run
/// use fusible::queue::StaticQueueSlots;
///
/// static SLOTS: StaticQueueSlots<[u32; 5], 47> = StaticQueueSlots::new();
///
/// # (|| -> Option<()> {
/// let slots = SLOTS.take()?;
/// # Some(()) })().unwrap();
/// ```
pub struct StaticQueueSlots<T, const N: usize>(StaticCell<[QueueSlot<T>; N]>);

impl<T, const N: usize> Default for StaticQueueSlots<T, N> {
    fn default() -> Self {
        Self::new()
    }
}

impl<T, const N: usize> StaticQueueSlots<T, N> {
    /// Allocate static slots.
    pub const fn new() -> Self {
        Self(StaticCell::new([const { QueueSlot::new() }; N]))
    }

    /// Take a static, mutable reference to these queue slots.
    ///
    /// If the slots have already been taken, then this returns `None`.
    /// Otherwise, you can use this to create a [`Queue`].
    ///
    /// This implementation takes a brief critical section to swap a `bool`.
    pub fn take(&'static self) -> Option<&'static mut [QueueSlot<T>]> {
        self.0.take().map(<[QueueSlot<T>; N]>::as_mut_slice)
    }
}

/// Information about a queue.
///
/// This information is always tracked by a queue. It is not affected
/// by build configurations. Use [`Queue::info`] to query this information.
#[derive(Debug, Default)]
#[cfg_attr(feature = "defmt", derive(defmt::Format))]
#[non_exhaustive]
pub struct QueueInfo<'r> {
    /// What's the queue's name?
    pub name: crate::ResourceName<'r>,
    /// How many elements are in the queue?
    pub enqueued: u32,
    /// How many elements are available?
    pub available_storage: u32,
}
