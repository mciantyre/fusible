// SPDX-License-Identifier: MPL-2.0
// SPDX-FileCopyrightText: Copyright 2024 Ian McIntyre

//! Fusible provides high-level Rust bindings for ThreadX.
//!
//! This documentation covers the usage and design of Fusible.
//! For build instructions, see the project README.
//!
//! # Getting started
//!
//! A Fusible application starts with a call to [`kernel_enter`].
//! Supply the entrypoint with a callback that creates the system's resources.
//! You must initialize at least one thread; otherwise, your system won't do anything!
//! See the [`thread`] module documentation for more information on threads.
//!
//! A minimal Fusible application is shown below.
//! This application performs no setup in `main()`, but it could.
//!
//! ```
//! use fusible::thread::{Thread, StaticStack};
//! use core::pin::pin;
//!
//! static STACK: StaticStack<4096> = StaticStack::new();
//! fn my_thread_entry() {
//!     // TODO: Your thread's work goes here.
//! #   std::process::exit(0);
//! }
//!
//! fn main() {
//!     let thread = pin!(Thread::context());
//!     fusible::kernel_enter(|_| {
//!         Thread::create(
//!             thread.into_ref(),
//!             STACK.take().unwrap(),
//!             &Default::default(),
//!             my_thread_entry,
//!         ).unwrap();
//!     })
//! }
//! ```
//!
//! # ThreadX services
//!
//! Fusible provides bindings for all ThreadX services.
//! They're separated into modules, like [`mutex`] and [`queue`], in the top of the package.
//! See each service's module documentation for more information.
//!
//! # Design
//!
//! Fusible services (try to) follow a consistent API design.
//! For example, the creation of a thread resource is similar to the creation of a queue or a block pool.
//! Additionally, the (non-)blocking actions performed on a queue are similar to the (non-)blocking actions performed on a block pool.
//! This section summarizes the design patterns you'll see throughout this package.
//!
//! ## Resource creation
//!
//! There are various operation system resources you can allocate, create, and use.
//! Examples of OS resources include [`Thread`](thread::Thread), [`Queue`](queue::Queue), and [`BlockPool`](block_pool::BlockPool).
//! Resources may borrow additional state, like arrays or stacks, that you also allocate.
//!
//! You allocate OS resources with a call to `context`.
//! `context` allocates a _context_ for the resource; namely,
//!
//! - a [`ThreadContext`](thread::ThreadContext) for a thread,
//! - a [`QueueContext`](queue::QueueContext) for a queue,
//! - a [`BlockPoolContext`](block_pool::BlockPoolContext) for a block pool,
//! - etc.
//!
//! The context tracks any references that the resource borrows.
//! The context also provides access to the _created_ resource.
//!
//! In order to create and use the resource, you first need to [pin](core::pin) its context.
//! Once pinned, you can call your resource's respective `create` function.
//! On success, `create` will provide a handle to the resource.
//!
//! ### Locally-allocated resources
//!
//! The example below demonstrates the simplest way to allocate and create a queue, block pool, and thread.
//! The resource contexts are locally allocated and pinned on `main`'s stack.
//! Additionally, the resources used by the queue and block pool are locally allocated.
//! Each resource is created within the kernel entry using a call to `create`.
//! Since the thread captures local memory, it's created through [`AppDefine`].
//!
//! ```
//! use fusible::{
//!     thread::{self, Thread, StaticStack},
//!     queue::{Queue, QueueSlot},
//!     block_pool::{BlockPool, BlockOf, Block},
//! };
//! use core::pin::pin;
//!
//! static STACK: StaticStack<4096> = StaticStack::new();
//!
//! struct MyObject {
//!     // ...
//!     # stuff: u32,
//! }
//! # impl MyObject { fn new() -> Self { Self { stuff: 0 } } }
//!
//! fn my_thread(
//!     pool: &BlockPool<MyObject>,
//!     queue: &Queue<Block<MyObject>>,
//! ) {
//!     loop {
//!         let my_object = pool.allocate(|| MyObject::new()).unwrap();
//!         assert!(queue.send(my_object).is_ok());
//!         thread::sleep(10).unwrap();
//! #       queue.try_receive().unwrap();
//! #       std::process::exit(0);
//!     }
//! }
//!
//! fn main() {
//!     let mut storage = [const { BlockOf::<MyObject>::new() }; 32];
//!     let mut slots = [const { QueueSlot::<Block<MyObject>>::new() }; 16];
//!
//!     let thread = pin!(Thread::context());
//!     let queue = pin!(Queue::context());
//!     let pool = pin!(BlockPool::context());
//!
//!     fusible::kernel_enter(|app_define| {
//!         let queue = Queue::create(queue.into_ref(), &mut slots, &Default::default()).unwrap();
//!         let pool = BlockPool::create(pool.into_ref(), &mut storage, &Default::default()).unwrap();
//!
//!         app_define.create_thread(
//!             thread.into_ref(),
//!             STACK.take().unwrap(),
//!             &Default::default(),
//!             move || my_thread(pool, queue),
//!         ).unwrap();
//!     });
//! }
//! ```
//!
//! ### Globally-allocated resources
//!
//! As the previous example shows, you can allocate resources in local memory.
//! You can also allocate resources in global memory.
//!
//! When a context object is allocated in global memory, any resource it borrows must also be allocated in global memory.
//! Fusible provides `Static*` objects, like
//!
//! - [`StaticStack`](thread::StaticStack)
//! - [`StaticQueueSlots`](queue::StaticQueueSlots)
//! - [`StaticBlocks`](block_pool::StaticBlocks)
//! - etc.
//!
//! to provide convenient `&'static mut` access to associated resources.
//!
//! The example below shows how to allocate all contexts and associated resources in global memory.
//! As before, the each resource is created within the kernel entry, using a call to `create`.
//! Associated resources are `take`n to prevent aliases to global, mutable state.
//!
//! ```
//! use fusible::{
//!     thread::{self, Thread, StaticStack, ThreadContext},
//!     queue::{Queue, QueueSlot, QueueContext, StaticQueueSlots},
//!     block_pool::{BlockPool, BlockOf, Block, BlockPoolContext, StaticBlocks},
//! };
//! use core::pin::Pin;
//!
//! static STACK: StaticStack<4096> = StaticStack::new();
//! static THREAD: ThreadContext = Thread::context();
//!
//! static QUEUE: QueueContext<Block<MyObject>> = Queue::context();
//! static QUEUE_SLOTS: StaticQueueSlots<Block<MyObject>, 16> = StaticQueueSlots::new();
//!
//! static BLOCK_POOL: BlockPoolContext<MyObject> = BlockPool::context();
//! static BLOCK_POOL_STORAGE: StaticBlocks<MyObject, 32> = StaticBlocks::new();
//! # struct MyObject(u32);
//! # impl MyObject { fn new() -> Self { Self(0) } }
//!
//! fn my_thread(
//!     pool: &BlockPool<MyObject>,
//!     queue: &Queue<Block<MyObject>>,
//! ) {
//!     loop {
//!         let my_object = pool.allocate(|| MyObject::new()).unwrap();
//!         assert!(queue.send(my_object).is_ok());
//!         thread::sleep(10).unwrap();
//! #       queue.try_receive().unwrap();
//! #       std::process::exit(0);
//!     }
//! }
//!
//! fn main() {
//!     fusible::kernel_enter(|_| {
//!         let queue = Queue::create(
//!             Pin::static_ref(&QUEUE),
//!             QUEUE_SLOTS.take().unwrap(),
//!             &Default::default(),
//!         ).unwrap();
//!
//!         let pool = BlockPool::create(
//!             Pin::static_ref(&BLOCK_POOL),
//!             BLOCK_POOL_STORAGE.take().unwrap(),
//!             &Default::default(),
//!         ).unwrap();
//!
//!         Thread::create(
//!             Pin::static_ref(&THREAD),
//!             STACK.take().unwrap(),
//!             &Default::default(),
//!             move || my_thread(pool, queue),
//!         ).unwrap();
//!     });
//! }
//! ```
//!
//! ### Access resources through contexts
//!
//! There are times where a thread should directly access a global OS resource through its context.
//! To support this pattern, all contexts have `try_created` methods for accessing the created resource.
//! See each context's API documentation for the full interface.
//!
//! The following example rewrites the `my_thread` function to access the queue and block pool in global memory.
//!
//! ```
//! # use fusible::{
//! #     thread::{self, Thread, StaticStack, ThreadContext},
//! #     queue::{Queue, QueueSlot, QueueContext, StaticQueueSlots},
//! #     block_pool::{BlockPool, BlockOf, Block, BlockPoolContext, StaticBlocks},
//! # };
//! # use core::pin::Pin;
//! # static STACK: StaticStack<4096> = StaticStack::new();
//! # static THREAD: ThreadContext = Thread::context();
//! # static QUEUE: QueueContext<Block<MyObject>> = Queue::context();
//! # static QUEUE_SLOTS: StaticQueueSlots<Block<MyObject>, 16> = StaticQueueSlots::new();
//! # static BLOCK_POOL: BlockPoolContext<MyObject> = BlockPool::context();
//! # static BLOCK_POOL_STORAGE: StaticBlocks<MyObject, 32> = StaticBlocks::new();
//! # struct MyObject(u32);
//! # impl MyObject { fn new() -> Self { Self(0) } }
//! fn my_thread() {
//!     let queue = Pin::static_ref(&QUEUE).try_created().unwrap();
//!     let pool = Pin::static_ref(&BLOCK_POOL).try_created().unwrap();
//!
//!     loop {
//!         let my_object = pool.allocate(|| MyObject::new()).unwrap();
//!         assert!(queue.send(my_object).is_ok());
//!         thread::sleep(10).unwrap();
//! #       queue.try_receive().unwrap();
//! #       std::process::exit(0);
//!     }
//! }
//!
//! fn main() {
//!     fusible::kernel_enter(|_| {
//!         Queue::create(
//!             Pin::static_ref(&QUEUE),
//!             QUEUE_SLOTS.take().unwrap(),
//!             &Default::default(),
//!         ).unwrap();
//!
//!         BlockPool::create(
//!             Pin::static_ref(&BLOCK_POOL),
//!             BLOCK_POOL_STORAGE.take().unwrap(),
//!             &Default::default(),
//!         ).unwrap();
//!
//!         Thread::create(
//!             Pin::static_ref(&THREAD),
//!             STACK.take().unwrap(),
//!             &Default::default(),
//!             my_thread,
//!         ).unwrap();
//!     });
//! }
//! ```
//!
//! ## Method naming conventions
//!
//! To realize your program, you perform actions on operating system resources.
//! The specific _action_ depends on the OS resource:
//!
//! - a queue can _send_ and _receive_ data.
//! - a mutex can _lock_ its shared state.
//! - a block / byte pool can _allocate_ memory.
//! - a semaphore can _get_ a count.
//! - etc.
//!
//! These actions could indefinitely block, never block, or temporarily block the calling thread.
//!
//! Fusible uses a consistent naming convention to express how an action indefinite blocks, never blocks, or temporarily blocks the calling thread.
//! When the method name is
//!
//! - simply the _action_, then the call **blocks indefinitely**.
//!   For example, [`Mutex::lock`](mutex::Mutex::lock) will block the calling thread until it can acquire the lock.
//!   Similarly, [`Queue::receive`](queue::Queue::receive) will block until a value is available.
//! - the _action_ prefixed with `try_*`, then the call is **non-blocking**.
//!   For example, [`Mutex::try_lock`](mutex::Mutex::try_lock) will immediately return if it cannot acquire the lock.
//!   Similarly, [`Queue::try_receive`](queue::Queue::try_receive) will immediately return if the queue is empty.
//! - the _action_ suffixed with `*_with_wait`, then the call **blocks for the given [`WaitOption`]**.
//!   For example, [`Mutex::lock_with_wait`](mutex::Mutex::lock_with_wait) will block until the resource is available or the timeout expires.
//!   Similarly, [`Queue::receive_with_wait`](queue::Queue::receive_with_wait) will block until a value is available or the timeout expires.
//!
//! Only a thread can perform an action that temporarily or indefinitely blocks.
//! If you're performing an action from a non-thread execution context, then you must use a non-blocking method.
//! And even if you're using an non-blocking method, your execution context might still be incorrect.
//! For complete information on calling contexts, see each method's documentation.
//!
//! This naming convention applies unless otherwise specified in a method's API documentation.
//!
//! ## Timeouts are OK
//!
//! There are different ways to signal that an action timed out.
//! You could signal the timeout in the error path of a `Result` with a "timed out" value.
//! Or, you could signal it in the success path of a `Result` with an option.
//!
//! Fusible believes that a timeout is not an error; in fact, it's exactly what you asked for.
//! Therefore, Fusible  signals a timeout through the `Ok(...)` variant of a `Result`.
//! Typically, `Ok(None)` means that the action timed out, and `Ok(Some(...))` means that the action completed before the timeout.
//! However, this convention change when sending on a [`Queue`](queue::Queue)!
//! For more information on how to interpret a return value, see each method's documentation.
//!
//! # Porting
//!
//! Fusible is expected to work across various MCU and host platforms.
//! However, Fusible doesn't provide everything necessary to support all ports.
//! To port Fusible to your target, you'll need to bring a few extra things.
//!
//! ## `tx_initialize_low_level`
//!
//! You must provide a `tx_initialize_low_level` routine for your port.
//! This routine must globally disable interrupts.
//! This routine should, at a minimum, up your system's periodic timer, but this is optional.
//! It may also need to associate your runtime's exceptions / interrupts with ThreadX functions.
//! See the official ThreadX documentation and examples for more information on low-level system initialization.
//!
//! ThreadX typically provides `tx_initialize_low_level` when targeting host ports, like Linux.
//! Consult your ThreadX build for more information.
//!
//! ## Embedded system runtime
//!
//! Fusible does not provide any life-before-`main` support for MCU ports.
//! If you're porting Fusible to a MCU, you must select a runtime that supports your MCU.

/*
General Safety Guidance
=======================

Fusible uses the same design to manage different types of ThreadX resources.
These patterns affect the safety of the API. The general safety guidance (GSG)
documents the safety considerations that are considered across the package. The
labels appear in the safety comments throughout the code.

GSG-000: Contexts track borrowed lifetimes
------------------------------------------

A context object uses an invariant lifetime to track the borrows provided to
a resource's `create` method. This invariant lifetime, along with the drop check,
ensure that the context cannot outlive any of its borrows.

A name, represented as a CStr, is commonly borrowed borrow by resources. If the
context could outlive the name, a query for resource information could return a
dangling pointer to that name, violating memory safety. Similarly, storage allocations
are borrowed by queues and pools. If the context outlived the storage, using the
resource would utilize dangling memory, also violating memory safety.

The implementation uses an invariant lifetime and the drop check to reduce memory
utilization. An alternate design could track the borrows within the context object.
However, this is wasteful; the control block already has that reference, so this
duplicates memory. Additionally, this design is inflexible, since it requires borrows
to be known during context allocation (unless there's an Optional with interior
mutibility, which requires more space). Requiring known borrows during allocation
complicates static resource allocation, given today's const evaluation capabilities.

If a safety comment links you here, make sure that any borrows are tagged with the
appropriate lifetime.

GSG-001: Contexts are pinned in order to be useful
--------------------------------------------------

"Creation" is the registration of a resource with the ThreadX operating system, along
with the initialization of that resource. Whenever Fusible allows resource creation,
the context is pinned in memory. Furthermore, all non-allocating context methods require
a pinned shared reference.

ThreadX control blocks have pointers to other control blocks of the same type. These
pointers represent neighbors in a doubly-linked list. If the contexts could be mutated
or moved after creation, the mutation / movement permits linked list node corruption,
affecting the operating system. The operating system could traverse the list, encounter
an invalid pointer, yet nonetheless follow the invalid pointer.

Contexts are !Unpin; they include a ControlBlock<T>, which is always !Unpin. Since they're
!Unpin, clients must follow the pinning safety requirements to correctly use a Context;
see the pin module in the Rust documentation for more information.

If a safety comment links you here, make sure that the context is pinned in its `create`
method, and in all methods that are non-allocating.

GSG-002: Resource handles must be created and pinned
----------------------------------------------------

A "resource handle" describes a reference to a resource that's owned by a context.
For examples, a `&Queue<T>` is the resource handle exposed by a `QueueContext<T, '_>`.
The handle provides manipulation of the resource (those with access to the `&Queue<T>`)
can send / receive Ts using the queue.)

If a user can access the resource handle, then the resource must have been created.
Furthermore, that resource handle must have a stable location in memory, despite the
type signature not including a Pin.

When we ensure that resource handles always point to created resources, we can assume
that ThreadX will never return "object not created" errors from most service calls.
(Handling Drop behaviors is a special case, documented later). This is convenient for
us and for our users.

Not projecting the context's pin through the resource handle is a matter of convenience.
Users do not have to design APIs that include pinned shared references. And since those
references are immutable, there's no safe way for users to move / invalidation the control
block through the reference handle.

If a safety comment links you here, make sure that the contexts only safely release
resource handles after they determine the resource is created. Additionally make sure
that the resource handle exposed by the context is pinned before it releases the
handle to the caller.

GSG-003: Context lifecycle occurs in one execution context
----------------------------------------------------------

An "execution context" is either initialization, thread, ISR, or timer. For more
information, see the ThreadX documentation.

A context object is created in one execution context. When the context is dropped,
it is dropped in that same execution context.

This restriction prevents a user from creating a resource in a thread, sending it
to an ISR, then dropping the resource in the ISR. (Think "block pool in a block pool"
usage pattern.) No resource can be destroyed in an ISR, per ThreadX requirements.
If this were attempted, the resource's delete service would fail, and there would
be nothing we could do but panic. If we ignored the error and concluded the drop, the
control block wouldn't be removed from the OS-managed linked list, which could lead
to memory unsafety.

All context objects are !Send, so they cannot move across execution contexts (i.e. between
threads, between threads and ISRs). This also means the cannot move from the initialization
to the thread context. That's an accepted limitation. We catch at runtime, in the context's
drop, the user who allocates, creates, then drops a resource solely within the initialization
context.

All create methods defend against creation in an ISR. Since a user cannot create a resource
in an ISR, and since a user cannot move an already-created resource into an ISR, a caller
error returned from a delete service does not signal deletion in an ISR context.

If a safety comment links you here, make sure that the context's drop panics if invoked
within the initialization context. This is achieved by checking for caller errors. Given
the above, we know that the caller error only represents a drop in the initialization context.
A sound drop will guarantee that the resource is removed from the OS-managed linked list
before returning.

One more note: A user is free to allocate a context and never call create. In this
circumstance, the context's drop should produce a "resource not created" error. This error can
be ignored.

If the object was never created, then it is not know to the ThreadX operating system. If it's
not known to ThreadX, then it is not in an OS-managed linked list.
*/

#![no_std]
#![warn(
    elided_lifetimes_in_paths,
    explicit_outlives_requirements,
    let_underscore_drop,
    missing_docs,
    semicolon_in_expressions_from_macros,
    single_use_lifetimes,
    trivial_numeric_casts,
    unsafe_op_in_unsafe_fn,
    unreachable_pub,
    unused_qualifications,
    clippy::cast_possible_truncation,
    clippy::map_unwrap_or,
    clippy::manual_assert,
    clippy::missing_safety_doc,
    clippy::ref_as_ptr,
    clippy::redundant_closure_for_method_calls,
    clippy::semicolon_if_nothing_returned,
    clippy::single_match_else,
    clippy::undocumented_unsafe_blocks,
    clippy::used_underscore_binding
)]
// TODO(mciantyre) Eventually promote these into warnings...
#![allow(
    missing_debug_implementations,
    clippy::missing_errors_doc,
    clippy::must_use_candidate
)]

mod tx_sys {
    pub(crate) use ::libthreadx_sys::error_checked::*;
    pub(crate) use ::libthreadx_sys::*;
}

/// Defines an enumeration that represents a ThreadX result value.
///
/// The enum uses a `u32` representation. It includes a `try_from_result`
/// method that converts the raw ThreadX result into an enum variant.
macro_rules! option_enum {
    (
        $(#[$enum_meta:meta])*
        $vis:vis enum $name:ident {
            $(
                $(#[$variant_meta:meta])*
                $variant:ident = $constant:path
            ),* $(,)?
        }
    ) => {
        $(#[$enum_meta])*
        #[repr(u32)]
        $vis enum $name {
            $(
                $(#[$variant_meta])*
                $variant = $constant,
            )*
        }

        impl $name {
            /// Try to convert a raw value into this enum.
            ///
            /// Returns `None` if there is no conversion.
            const fn try_from_raw(raw: u32) -> Option<Self> {
                match raw {
                    $(
                    $constant => Some(Self::$variant),
                    )*
                    _ => None,
                }
            }
        }
    };
}

/// Defines an enumeration that represents a ThreadX result value.
///
/// The enum uses a `u32` representation. It includes a `try_from_result`
/// method that converts the raw ThreadX result into an enum variant.
macro_rules! error_enum {
    (
        $(#[$enum_meta:meta])*
        $vis:vis enum $name:ident {
            $(
                $(#[$variant_meta:meta])*
                $variant:ident = $constant:path
            ),* $(,)?
        }
    ) => {
        $(#[$enum_meta])*
        #[repr(u32)]
        $vis enum $name {
            $(
                $(#[$variant_meta])*
                $variant = $constant,
            )*
        }

        impl $name {
            /// # Panics
            ///
            /// Panics if the result code cannot be converted into one of the
            /// enum variants.
            const fn try_from_result(result: u32) -> Result<(), Self> {
                match result {
                    $crate::tx_sys::TX_SUCCESS => Ok(()),
                    $(
                    $constant => Err(Self::$variant),
                    )*
                    _ => unreachable!(),
                }
            }
        }
    };
}

macro_rules! impl_common_context {
    ($Resource:ty) => {
        /// Returns `true` if this resource is created.
        ///
        /// To avoid using this check, keep hold of the reference produced during creation.
        #[inline]
        pub fn is_created(self: core::pin::Pin<&Self>) -> bool {
            self.0.0.is_created()
        }

        /// Returns the resource if it's created.
        ///
        /// To avoid using this check, keep hold of the reference produced during creation.
        #[inline]
        pub fn try_created(self: core::pin::Pin<&Self>) -> Option<&'_ $Resource> {
            // Safety: We check for creation before assuming creation.
            //
            // It might seem there's a race condition here: We observe `is_created()`,
            // and take the branch. Suddenly, we're deleted through another execution
            // path! We then call `assume_created()`, even though we're deleted.
            //
            // This isn't possible. Once we're created, we're always created until we're
            // dropped. Dropping requires an exclusive reference, which can't co-exist
            // with the (pinned) shared reference that we hold.
            unsafe { self.is_created().then(|| self.assume_created()) }
        }

        /// Assume that the resource is already created.
        ///
        /// # Safety
        ///
        /// If the resource is not created, then other safe methods on the resource can exhibit undefined behavior.
        /// Consider using [`try_created`](Self::try_created) for a safer interface.
        #[inline]
        pub unsafe fn assume_created(self: core::pin::Pin<&Self>) -> &'_ $Resource {
            &self.get_ref().0
        }
    };
}

/// Claim that the execution path is unreachable.
///
/// This always requires an `unsafe` block, since the "panic
/// if taken" guarantee may not exist for a given build.
macro_rules! fusible_unreachable {
    ($($arg:tt)*) => {{
        #[allow(unreachable_code)]
        {
            #[cfg(debug_assertions)]
            { ::core::unreachable!($($arg)*); }
            ::core::hint::unreachable_unchecked();
        }
    }};
}

#[cfg(test)]
extern crate std;

mod app_define;
mod callback_dispatch;
#[macro_use]
mod panic;
mod pool;

use core::{cell::UnsafeCell, marker::PhantomPinned, mem::MaybeUninit};

pub use app_define::{AppDefine, is_initializing, kernel_enter};

pub mod block_pool;
pub mod byte_pool;
pub mod event_flags;
pub mod interrupt_control;
pub mod mutex;
pub mod queue;
pub mod semaphore;
pub mod thread;
pub mod timer;

/// Your ThreadX operating system was not built with this feature.
///
/// Check the build settings for your TheadX library to understand how it was built.
/// You might need to re-build your library to enable the feature.
#[derive(Debug)]
pub struct FeatureNotEnabledError(());

/// Get the relative time, in timer ticks, from the periodic timer.
///
/// The relative time increments every time the periodic timer interrupt activates.
/// The frequency depends on your port's periodic timer configuration.
/// It can also change due to a call to [`set_time`].
#[inline]
pub fn get_time() -> u32 {
    // Safety: Call does not modify any global state. It simply
    // reads a u32 managed by the OS. Read occurs within a critical
    // section implemented by the operating system.
    unsafe { tx_sys::tx_time_get() }
}

/// Set the relative time, in timer ticks.
///
/// The next activation of the periodic timer interrupt will increment `ticks` by one.
/// The return of [`get_time`] will reflect the newly-updated relative time.
#[inline]
pub fn set_time(ticks: u32) {
    // Safety: The operating system uses a critical section guard
    // against a race on this value.
    unsafe { tx_sys::tx_time_set(ticks) };
}

/// How many ticks to wait for an operation.
///
/// This wraps a `u32` that describes the system ticks to wait
/// for an operation to produce a result. For convenience,
/// use [`no_wait()`](Self::no_wait) to signal a non-blocking
/// operation. Or, use [`wait_forever()`](Self::wait_forever)
/// to signal a blocking operation.
///
/// You may use ranges `1` through `(!0 - 1)`, inclusive, to
/// specify the number of ticks. A wait option of zero is
/// equivalent to "no wait," and a wait option of `!0` is
/// "wait forever."
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
#[repr(transparent)]
pub struct WaitOption(pub u32);

impl WaitOption {
    /// Do not wait for the operation to complete.
    ///
    /// This typically is the only valid option when using a kernel
    /// object from a non-thread context, like an interrupt. When
    /// used as the wait option, the thread will usually not provide
    /// a preemption opportunity; but, check your kernel object's
    /// documentation for more information.
    pub const fn no_wait() -> Self {
        Self(libthreadx_sys::TX_NO_WAIT)
    }

    /// Returns `true` if constructed via [`no_wait()`](Self::no_wait).
    pub const fn is_no_wait(self) -> bool {
        self.0 == libthreadx_sys::TX_NO_WAIT
    }

    /// Wait forever for the operation to complete.
    ///
    /// Note that an operation using this wait option can still
    /// be aborted by another thread. Consult your kernel object's
    /// documentation for more information.
    pub const fn wait_forever() -> Self {
        Self(libthreadx_sys::TX_WAIT_FOREVER)
    }

    /// Returns `true` if constructed via [`wait_forever()`](Self::wait_forever).
    pub const fn is_wait_forever(self) -> bool {
        self.0 == libthreadx_sys::TX_WAIT_FOREVER
    }
}

impl From<WaitOption> for u32 {
    fn from(value: WaitOption) -> Self {
        value.0
    }
}

mod marker {
    use core::{cell::Cell, marker::PhantomData};

    /// A zero-sized type that's neither `Send` nor `Sync`.
    ///
    /// Use this marker when you have no other way to mark `!Send` or
    /// `!Sync` for your type. This type is valid to construct in a
    /// const context.
    pub(crate) struct NotSendOrSync(PhantomData<*mut ()>);
    impl NotSendOrSync {
        pub(crate) const fn mark() -> Self {
            Self(PhantomData)
        }
    }

    /// A zero-sized type that's not `Send`.
    pub(crate) struct NotSend(NotSendOrSync);
    impl NotSend {
        pub(crate) const fn mark() -> Self {
            Self(NotSendOrSync::mark())
        }
    }

    // Safety: This type introduces Sync to NotSendOrSync, thereby
    // blocking Send.
    unsafe impl Sync for NotSend {}

    /// A zero-sized type that forces `'wat` to be lifetime invariant.
    ///
    /// This type is still Send and Sync. If you need to block those
    /// implementations, seek another marker type.
    ///
    /// This type can be constructed in a const context. It's extra
    /// convoluted to support const construction.
    pub(crate) struct InvariantLifetime<'wat> {
        /// This type is Send, but not Sync.
        invariant_lifetime: PhantomData<Cell<&'wat ()>>,
        /// Re-introduce Send and Sync later...
        _not_send_or_sync: NotSendOrSync,
    }
    impl InvariantLifetime<'_> {
        pub(crate) const fn mark() -> Self {
            Self {
                _not_send_or_sync: NotSendOrSync::mark(),
                invariant_lifetime: PhantomData,
            }
        }
    }
    // Safety: this type isn't responsible for blocking Send.
    unsafe impl Send for InvariantLifetime<'_> {}
    // Safety: this type isn't responsible for blocking Sync.
    unsafe impl Sync for InvariantLifetime<'_> {}

    /// A zero-sized type that allows covariance up to `'wat`.
    ///
    /// This type still implements Send and Sync. If you need to block
    /// those implementations, seek another marker type.
    ///
    /// This type can be constructed in a const context.
    pub(crate) struct CovariantLifetime<'wat> {
        covariant_lifetime: PhantomData<&'wat ()>,
    }

    impl CovariantLifetime<'_> {
        pub(crate) const fn mark() -> Self {
            Self {
                covariant_lifetime: PhantomData,
            }
        }
    }
}

/// A kernel object's control block.
///
/// This is separated so we can incrementally add Send and Sync
/// for control block types that we care about.
#[repr(transparent)]
struct ControlBlock<T> {
    /// Should already be blocked by the T type. But if it's not,
    /// we want to catch that.
    _not_send_or_sync: marker::NotSendOrSync,
    /// We rarely look at the T within this cell.
    /// We're normally passing its pointer directly into
    /// ThreadX functions.
    control_block: UnsafeCell<T>,
    /// ThreadX maintains internal linked lists
    /// of pointers to control blocks. If control
    /// blocks move, then ThreadX will be sad.
    /// This isn't a problem for statically-allocated
    /// objects, but it is a problem for any object
    /// allocated on a local stack.
    _pin: PhantomPinned,
}

impl<T> ControlBlock<T> {
    /// Returns a control block with a zero bit pattern.
    const fn new() -> Self {
        Self {
            _not_send_or_sync: marker::NotSendOrSync::mark(),
            // Safety: A zero bitpattern is OK for all types T used throughout
            // this package. The control block is a C structure composed of
            // primitives and pointers, all which can be zero.
            control_block: UnsafeCell::new(unsafe { MaybeUninit::zeroed().assume_init() }),
            _pin: PhantomPinned,
        }
    }

    /// Get the pointer to the control block.
    const fn get(&self) -> *mut T {
        self.control_block.get()
    }
}

//
// On Sync safety of ControlBlock<T>
// ---------------------------------
//
// ThreadX objects are allowed to be allocated into global memory.
// In fact, the ThreadX documentation recommends this. Generally,
// ThreadX APIs take critical sections when manipulating these
// objects. These critical sections, along with internal management
// of scheduler preemption, make these objects Sync. We're prevented
// from (safely) observing or modifying the internals of control
// blocks; all members are private.
//
// There is an exception: 'create' functions may modify members of the
// control block outside of a critical section. However, creation
// methods will also return an error if the ThreadX object has already
// been registered, and that "already registered" evaluation occurs
// in a critical section. Similarly, creation fails if called from
// an interrupt context. So despite there being a race possibility,
// we'll catch these errors.
//
// The above exception relies on the error-checked ThreadX API calls!
// If those are disabled, then all bets are off. Inspection of this
// package shows that we're always using error-checked APIs.
//

/// Safety: see above.
unsafe impl Sync for ControlBlock<libthreadx_sys::TX_BLOCK_POOL> {}

/// Safety: see above.
unsafe impl Sync for ControlBlock<libthreadx_sys::TX_BYTE_POOL> {}

/// Safety: see above.
unsafe impl Sync for ControlBlock<libthreadx_sys::TX_EVENT_FLAGS_GROUP> {}

/// Safety: see above.
unsafe impl Sync for ControlBlock<libthreadx_sys::TX_MUTEX> {}

/// Safety: see above.
unsafe impl Sync for ControlBlock<libthreadx_sys::TX_QUEUE> {}

// Safety: see above.
unsafe impl Sync for ControlBlock<libthreadx_sys::TX_SEMAPHORE> {}

/// Safety: see above.
unsafe impl Sync for ControlBlock<libthreadx_sys::TX_THREAD> {}

/// Safety: see above.
unsafe impl Sync for ControlBlock<libthreadx_sys::TX_TIMER> {}

//
// On Send safety of ControlBlock<T>
// ---------------------------------
//
// We prevent sending a control block across execution contexts.
// This lets us rule out programs where a control block is
// created in the initialization or thread context, then destroyed
// in an interrupt context. We perform a runtime check for the (unlikely)
// usage in which a resource is created then destroyed completely
// in the initialization context.
//

/// Generalizes how we query for a control block's (creation) ID.
trait Identified {
    const CREATION_ID: tx_sys::ULONG;
    fn creation_id(&self) -> tx_sys::ULONG;
}

macro_rules! impl_identified {
    ($ControlBlock:ty, $CREATION_ID:path) => {
        impl Identified for $ControlBlock {
            const CREATION_ID: $crate::tx_sys::ULONG = $CREATION_ID;
            fn creation_id(&self) -> crate::tx_sys::ULONG {
                <$ControlBlock>::id(self)
            }
        }
    };
}

impl_identified!(
    libthreadx_sys::TX_BLOCK_POOL,
    libthreadx_sys::TX_BLOCK_POOL_ID
);
impl_identified!(
    libthreadx_sys::TX_BYTE_POOL,
    libthreadx_sys::TX_BYTE_POOL_ID
);
impl_identified!(
    libthreadx_sys::TX_EVENT_FLAGS_GROUP,
    libthreadx_sys::TX_EVENT_FLAGS_ID
);
impl_identified!(libthreadx_sys::TX_MUTEX, libthreadx_sys::TX_MUTEX_ID);
impl_identified!(libthreadx_sys::TX_QUEUE, libthreadx_sys::TX_QUEUE_ID);
impl_identified!(
    libthreadx_sys::TX_SEMAPHORE,
    libthreadx_sys::TX_SEMAPHORE_ID
);
impl_identified!(libthreadx_sys::TX_THREAD, libthreadx_sys::TX_THREAD_ID);
impl_identified!(libthreadx_sys::TX_TIMER, libthreadx_sys::TX_TIMER_ID);

impl<CB: Identified> ControlBlock<CB> {
    /// Returns `true` if this control block has been created.
    fn is_created(&self) -> bool {
        // Safety: all control blocks are created with a zero bit pattern.
        // See the implementation of ControlBlock::new(). That bit pattern
        // is valid for all representations of all control blocks. It's
        // valid for the creation ID, which is simply a u32.
        unsafe { (*self.get()).creation_id() == CB::CREATION_ID }
    }
}

struct StaticCell<T> {
    data: UnsafeCell<T>,
    taken: interrupt_control::InterruptFreeCell<bool>,
}

// Safety: We guard access to the data with a runtime flag. The
// flag guarantees that only one execution context can access
// the managed data.
unsafe impl<T: Send> Sync for StaticCell<T> {}

impl<T> StaticCell<T> {
    const fn new(value: T) -> Self {
        Self {
            data: UnsafeCell::new(value),
            taken: interrupt_control::InterruptFreeCell::new(false),
        }
    }

    /// Take a mutable reference to this cell's data.
    ///
    /// Returns `Some(...)` for the first call, then `None` on
    /// any subsequent call.
    fn take(&'static self) -> Option<&'static mut T> {
        // Safety: The flag replacement happens in a critical section.
        // The flag ensures that there is only one mutable reference
        // acquired from this call.
        unsafe {
            let already_taken = self.taken.replace(true);
            if already_taken {
                None
            } else {
                Some(&mut *self.data.get())
            }
        }
    }
}

fn threadx_string(name: Option<&core::ffi::CStr>) -> *mut core::ffi::c_char {
    name.map_or(core::ptr::null_mut(), |name| name.as_ptr().cast_mut())
}

/// Convert a ThreadX resource name into something nice.
///
/// It's OK if `name` is null.
///
/// # Safety
///
/// `name` must point to a nul-terminated string. You must make sure
/// the lifetime is correct.
unsafe fn from_threadx_string<'c>(name: *mut core::ffi::c_char) -> ResourceName<'c> {
    // Safety: `name` is not NULL. Caller swears that `name` points to a nul-terminated
    // string.
    ResourceName((!name.is_null()).then(|| unsafe { core::ffi::CStr::from_ptr(name) }))
}

/// The name assigned to an operating system resource.
///
/// This newtype helps you render the name for debugging.
/// Use [`as_c_str`](Self::as_c_str) to access the underlying
/// string.
#[derive(Clone, Copy, PartialEq, Eq, Default)]
pub struct ResourceName<'r>(Option<&'r core::ffi::CStr>);

impl<'r> ResourceName<'r> {
    /// Returns the underlying string, if it exists.
    #[inline]
    pub const fn as_c_str(self) -> Option<&'r core::ffi::CStr> {
        self.0
    }
}

#[cfg(feature = "defmt")]
impl defmt::Format for ResourceName<'_> {
    fn format(&self, fmt: defmt::Formatter<'_>) {
        defmt::write!(
            fmt,
            "{=[u8]:a}",
            self.0.map(core::ffi::CStr::to_bytes).unwrap_or(b"")
        );
    }
}

impl core::fmt::Display for ResourceName<'_> {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        self.0.map_or(Ok(()), |c_str| {
            core::fmt::Display::fmt(&c_str.to_bytes().escape_ascii(), f)
        })
    }
}

impl core::fmt::Debug for ResourceName<'_> {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        core::fmt::Debug::fmt(&self.0, f)
    }
}
