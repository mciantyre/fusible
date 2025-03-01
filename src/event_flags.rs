// SPDX-License-Identifier: MPL-2.0
// SPDX-FileCopyrightText: Copyright 2024 Ian McIntyre

//! Event flag services.
//!
//! An [`EventFlags`] manages a set of 32 bits. You can atomically set, get, and clear
//! bits in the set. You can also block until any or all bits are set by another thread.
//!
//! You can allocate [`EventFlags`] in global or local memory. After allocation, you'll
//! need to [`create`](EventFlags::create) the object before you can manipulate the bit
//! set.
//!
//! # Example
//!
//! A globally-allocated event flag group.
//!
//! ```no_run
//! use fusible::event_flags::{EventFlagsContext, EventFlags, GetOption, SetOption};
//! use core::{pin::Pin, num::NonZero};
//!
//! # (|| -> Result<(), fusible::event_flags::CreateError> {
//! static EVENTS: EventFlagsContext = EventFlags::context();
//!
//! const MY_EVENT: NonZero<u32> = // ...
//! # unsafe { NonZero::new_unchecked(0x4) };
//!
//! let events = EventFlags::create(Pin::static_ref(&EVENTS), &Default::default())?;
//!
//! # (|| -> Result<(), fusible::event_flags::GetError> {
//! events.set(MY_EVENT.get(), SetOption::Or);
//! let flags = events.get(MY_EVENT, GetOption::OrClear)?;
//! # Ok(()) })().unwrap();
//! # Ok(()) })().unwrap();
//! ```
//!
//! A locally-allocated event flag group.
//!
//! ```no_run
//! use fusible::event_flags::{EventFlags, GetOption, SetOption};
//! use core::{pin::pin, num::NonZero};
//!
//! # (|| -> Result<(), fusible::event_flags::CreateError> {
//! let events = pin!(EventFlags::context());
//! let events = EventFlags::create(events.into_ref(), &Default::default())?;
//!
//! const MY_EVENT: NonZero<u32> = // ...
//! # unsafe { NonZero::new_unchecked(0x4) };
//!
//! # (|| -> Result<(), fusible::event_flags::GetError> {
//! events.set(MY_EVENT.get(), SetOption::Or);
//! let flags = events.get(MY_EVENT, GetOption::OrClear)?;
//! # Ok(()) })().unwrap();
//! # Ok(()) })().unwrap();
//! ```

use core::ffi::CStr;
use core::num::NonZero;
use core::pin::Pin;

use crate::marker::InvariantLifetime;
use crate::tx_sys::TX_EVENT_FLAGS_GROUP;

use crate::{ControlBlock, WaitOption};

error_enum! {
    /// An error when creating event flags.
    #[derive(Debug, Clone, Copy, PartialEq, Eq)]
    #[cfg_attr(feature = "defmt", derive(defmt::Format))]
    pub enum CreateError {
        /// The flags are already created.
        AlreadyCreated = crate::tx_sys::TX_GROUP_ERROR,

        /// The caller is invalid.
        ///
        /// You can only create event flags in the initialization or
        /// thread execution contexts.
        Caller = crate::tx_sys::TX_CALLER_ERROR,
    }
}

error_enum! {
    /// An error when trying to get event flags.
    #[derive(Debug, Clone, Copy, PartialEq, Eq)]
    #[cfg_attr(feature = "defmt", derive(defmt::Format))]
    pub enum GetError {
        // Not handling TX_DELETED. Users cannot delete the control
        // block while references are live.

        // Not handling TX_NO_EVENTS. We'll use Option in the success path.

        /// The call was aborted by another entity.
        ///
        /// This happens when your software chooses to abort a thread's
        /// blocking call.
        WaitAborted = crate::tx_sys::TX_WAIT_ABORTED,

        // Not handling TX_GROUP_ERROR. Types and pinning ensure pointers
        // are always valid. Types also ensure that groups are created.

        // Not handling TX_PTR_ERROR. We always supply a valid pointer for
        // receiving flags.

        /// The wait option is invalid for the execution context.
        ///
        /// If you're getting flags from a non-thread execution context, then you must
        /// use a `try_*` method, or supply "no wait" as the wait option.
        InvalidWait = crate::tx_sys::TX_WAIT_ERROR,

        // Not handling TX_OPTION_ERROR. Enums represent valid options.
    }
}

/// Creation options for event flags.
#[derive(Default)]
#[non_exhaustive]
pub struct EventFlagsOptions<'ctx> {
    /// The name of the resource.
    pub name: Option<&'ctx CStr>,
}

/// A set of event flags for thread signaling.
///
/// To retrieve flags from the group, use
///
/// - [`get`](Self::get) to block until any / all bits are set.
/// - [`try_get`](Self::try_get) to check if any / all bits are set without blocking.
/// - [`get_with_wait`](Self::get_with_wait) to check for any / all bits with a timeout.
///
/// To set bits in the group, use [`set`](Self::set).
///
/// See [the module-level documentation](crate::event_flags) for examples.
///
/// # FFI
///
/// This object is transparently a `TX_EVENT_FLAGS_GROUP`.
#[repr(transparent)]
pub struct EventFlags(ControlBlock<TX_EVENT_FLAGS_GROUP>);

/// Manages the event flags and its borrows.
///
/// Use [`EventFlags`] to interact with the bit set. The methods on the
/// context let you access an already-created event flags.
///
/// # FFI
///
/// The context is transparently an [`EventFlags`].
#[repr(transparent)]
pub struct EventFlagsContext<'ctx>(EventFlags, InvariantLifetime<'ctx>);

impl Drop for EventFlagsContext<'_> {
    #[inline]
    fn drop(&mut self) {
        // Safety: Created and pinned per GSG-002, or not created per GSG003.
        // Checking lifecycle conditions per GSG-003.
        unsafe {
            let result = crate::tx_sys::tx_event_flags_delete(self.0.0.get());
            aborting_assert!(
                result == crate::tx_sys::TX_SUCCESS || result == crate::tx_sys::TX_GROUP_ERROR,
                "Attempt to drop resource in the initialization context"
            );
        }
    }
}

impl EventFlags {
    /// Allocate a group of event flags.
    ///
    /// The object is inert; you'll need to pin it and call [`create`](Self::create) before
    /// you can use it.
    #[inline]
    pub const fn context<'ctx>() -> EventFlagsContext<'ctx> {
        EventFlagsContext(EventFlags(ControlBlock::new()), InvariantLifetime::mark())
    }

    /// Create the event flags.
    ///
    /// This registers the group with the operating system, enabling you to get and
    /// set bits in the set. Use the returned reference to manipulate the flags.
    #[inline]
    pub fn create<'ctx, 'e>(
        context: Pin<&'e EventFlagsContext<'ctx>>,
        opts: &'_ EventFlagsOptions<'ctx>,
    ) -> Result<&'e Self, CreateError> {
        // Safety: Context pinned per GSG-001. Tracking lifetime of
        // borrowed name per CSG-000.
        unsafe {
            let group = &context.get_ref().0;
            let result = crate::tx_sys::tx_event_flags_create(
                group.0.get(),
                crate::threadx_string(opts.name),
            );

            CreateError::try_from_result(result)?;
            Ok(group)
        }
    }

    /// Get any / all available flags within a timeout.
    ///
    /// `requested_flags` represents the flags of interest. If any / all of
    /// these flags match the available flags, then the return is `Ok(Some(flags))`.
    ///
    /// If the wait option expires, then the return is `Ok(None)`.
    ///
    /// If called from a non-thread execution context, then `wait_option` must
    /// represent "no wait." Consider using [`try_get`](Self::try_get) for
    /// these situations.
    ///
    /// If `wait_option` represents "wait forever," and if called from a thread
    /// execution context, then the result will always have flags. Consider
    /// using [`get`](Self::get) for these situations.
    #[inline]
    pub fn get_with_wait(
        &self,
        requested_flags: NonZero<u32>,
        get_option: GetOption,
        wait_option: WaitOption,
    ) -> Result<Option<NonZero<u32>>, GetError> {
        let mut actual_flags: u32 = 0;

        // Safety: Pinned and created per GSG-002.
        // Call doesn't stash any pointers that could
        // later dangle.
        let result = unsafe {
            crate::tx_sys::tx_event_flags_get(
                self.0.get(),
                requested_flags.get(),
                get_option as _,
                &mut actual_flags,
                wait_option.into(),
            )
        };

        if result == crate::tx_sys::TX_NO_EVENTS {
            return Ok(None);
        }

        GetError::try_from_result(result)?;
        Ok(NonZero::new(actual_flags))
    }

    /// Set or clear flags in the group.
    ///
    /// `flags` is either ANDed or ORed into the group, depending on the `set_option`.
    #[inline]
    pub fn set(&self, flags: u32, set_option: SetOption) {
        // Not handling TX_GROUP_ERROR. Types and pinning ensure that
        // pointers are always valid. Types also ensure that groups are
        // always created.
        //
        // Not handling TX_OPTION. Enums represent valid options.

        // Safety: the group is pinned and assumed to be created. Given
        // the above comment, there are no errors to handle that would
        // affect safety.
        let _ = unsafe { crate::tx_sys::tx_event_flags_set(self.0.get(), flags, set_option as _) };
    }

    /// Block until any / all flags are available.
    ///
    /// This will always return a non-zero bit mask, since it will block
    /// until the `get_option` is satisfied. This can only be used in
    /// thread execution contexts.
    ///
    /// If you need a non-blocking get, use [`try_get`](Self::try_get).
    /// If you need a timeout, use [`get_with_wait`](Self::get_with_wait).
    #[inline]
    pub fn get(
        &self,
        requested_flags: NonZero<u32>,
        get_option: GetOption,
    ) -> Result<NonZero<u32>, GetError> {
        // Safety: Since we're waiting forever, we'll never see TX_NO_EVENTS. Since we never see TX_NO_EVENTS,
        // we'll never take the branch that returns `None`.
        unsafe {
            let flags =
                self.get_with_wait(requested_flags, get_option, WaitOption::wait_forever())?;
            Ok(flags.unwrap_unchecked())
        }
    }

    /// Check for any / all flags.
    ///
    /// If the `get_option` is not satisfied with the `requested_flags`, then
    /// this call returns immediately. Since it doesn't block, this call can
    /// be used from non-thread execution contexts, like ISRs.
    ///
    /// If you're willing to wait for flags, use [`get_with_wait`](Self::get_with_wait)
    /// or [`get`](Self::get).
    #[inline]
    pub fn try_get(
        &self,
        requested_flags: NonZero<u32>,
        get_option: GetOption,
    ) -> Option<NonZero<u32>> {
        // Safety: See inline comments. We exhaustively check existing / future errors.
        unsafe {
            match self.get_with_wait(requested_flags, get_option, WaitOption::no_wait()) {
                // The "no wait" option (above) is valid for all calling contexts.
                // We'll never see this error.
                Err(GetError::InvalidWait) => fusible_unreachable!(),
                // The "no wait" option (above) does not wait. Since it does not
                // wait, it cannot be aborted.
                Err(GetError::WaitAborted) => fusible_unreachable!(),
                Ok(flags) => flags,
            }
        }
    }
}

impl EventFlagsContext<'_> {
    impl_common_context!(EventFlags);
}

/// The criteria for checking event flags.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[repr(u32)]
pub enum GetOption {
    /// The available flags must match *all* requested flags.
    ///
    /// If any of the requested flags isn't set, then the `get*`
    /// will either block or return nothing.
    And = crate::tx_sys::TX_AND,
    /// Like [`And`](GetOption::And), but atomically clears *all* matching flags.
    ///
    /// Once a match occurs, all matching bits are cached for the return. Then,
    /// the group atomically clears all matching flags.
    AndClear = crate::tx_sys::TX_AND_CLEAR,
    /// The available flags must match *any* requested flags.
    ///
    /// If there are multiple flags set, then the `get*` will return multiple
    /// set flags. If no flags are set, then `get*` will either block or return
    /// nothing.
    Or = crate::tx_sys::TX_OR,
    /// Like [`Or`](GetOption::Or), but atomically clears *any* matching flags.
    ///
    /// Once a match occurs, all matching bits are cached for the return. Then,
    /// the group automatically clears any flag that matched.
    OrClear = crate::tx_sys::TX_OR_CLEAR,
}

/// How to manipulate bits in the event group.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[repr(u32)]
pub enum SetOption {
    /// Bitwise AND the requested flags into the event flags.
    ///
    /// You can use this to clear one or more flags in the group.
    And = crate::tx_sys::TX_AND,
    /// Bitwise OR the requested flags into the event flags.
    ///
    /// You can use this to set one or more flags in the group.
    Or = crate::tx_sys::TX_OR,
}
