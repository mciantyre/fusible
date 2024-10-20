// SPDX-License-Identifier: MPL-2.0
// SPDX-FileCopyrightText: Copyright 2024 Ian McIntyre

//! Support code for dispatching through ThreadX callbacks.
//!
//! Callbacks like thread entrypoints and timer expiration functions
//! accept a `ULONG` argument. Most of the time, we want to stuff a
//! pointer as that input argument. We should be able to do that on
//! 32 bit systems, where pointers and `ULONG`s are the same size.
//! But on emulated systems like Linux and Windows, we can't stuff
//! this pointer; the pointer could be 64 bits wide.
//!
//! This module provides a compatibility layer for 64-bit targets.
//! A `CallbackDispatch<ULONG>` produced through [`make`] will track
//! a 64 bit pointer through ThreadX by indirecting through a lookup
//! table. On the other hand, if the target has 32 bit pointers,
//! the same `CallbackDispatch<ULONG>` will directly invoke your
//! callback.
//!
//! The 64-bit implementation assumes that you never need to clean up
//! the indirection table.

use libthreadx_sys::ULONG;

/// Invokes a `fn(T)` callback with a provided input.
pub(crate) struct CallbackDispatch<T> {
    callback: unsafe extern "C" fn(_: T),
    input: T,
}

impl CallbackDispatch<ULONG> {
    /// Access the callback.
    pub(crate) fn callback(&self) -> unsafe extern "C" fn(_: ULONG) {
        self.callback
    }
    /// Access the input.
    pub(crate) fn input(&self) -> ULONG {
        self.input
    }
}

impl<T> CallbackDispatch<*mut T> {
    /// Produce a callback that does nothing.
    ///
    /// This is always safe to invoke.
    pub(crate) const fn no_op() -> Self {
        Self {
            callback: {
                extern "C" fn no_op<T>(_: *mut T) {}
                no_op::<T>
            },
            input: core::ptr::null_mut(),
        }
    }

    /// Create a dispatch that will directly invoke `callback` with `input`.
    ///
    /// # Safety
    ///
    /// Caller must make sure that `input` is valid whenever this callback
    /// is invoked. Note that the callback may be invoked multiple times.
    pub(crate) unsafe fn direct(callback: unsafe extern "C" fn(_: *mut T), input: *mut T) -> Self {
        Self { callback, input }
    }
}

impl<T> CallbackDispatch<T> {
    /// Invoke the managed callback.
    pub(crate) fn invoke(self) {
        // Safety: call is responsible for making sure the input remains
        // valid while this CallbackDispatch exists.
        unsafe { (self.callback)(self.input) };
    }
}

/// Makes a callback dispatch that can always be used with ThreadX.
///
/// This is zero cost on targets with 32 bit pointers. For targets
/// with 64 bit pointers, the dispatch will indirect through a pointer
/// to find your original callback and input.
///
/// # Safety
///
/// You must ensure that `input` is valid whenever the callback is
/// invoked. Note that the callback can be invoked multiple times.
///
/// You must make sure that it's safe to access the input across another
/// execution context. Namely, your input should be Send.
///
/// The calling convention for targets with 32 bit pointers must not
/// distinguish between address and data when passing function arguments.
pub(crate) unsafe fn make(
    callback: unsafe extern "C" fn(*mut ()),
    input: *mut (),
) -> CallbackDispatch<ULONG> {
    // The easy case: we can use the 32 bit pointer as the callback's argument.
    // Assume that the same calling convention is used when passing data and
    // addresses.
    #[cfg(target_pointer_width = "32")]
    {
        const _: () = assert!(size_of::<ULONG>() == size_of::<*mut ()>());
        const _: () = assert!(align_of::<ULONG>() == align_of::<*mut ()>());
        CallbackDispatch {
            // Safety: Caller swears that the calling convention is the same for
            // addresses and data.
            callback: unsafe {
                core::mem::transmute::<unsafe extern "C" fn(*mut ()), unsafe extern "C" fn(ULONG)>(
                    callback,
                )
            },
            input: input as ULONG,
        }
    }

    // Harder case: indirect through a table. Again, assume that the same
    // calling convention applies when passing data and addresses.
    //
    // We never clean up the table, even if the associated data is dropped
    // or invalidated. This is considered OK; this component isn't responsible
    // for deactivating any ThreadX resource that might invoke the callback.
    // As long as other software (thread, timer, etc.) deactivate the resource,
    // then the callback dispatch will be leaked in the table.
    #[cfg(all(target_pointer_width = "64", any(unix, windows)))]
    {
        extern crate std;
        use std::sync::RwLock;
        use std::vec::Vec;

        struct HostDispatch(RwLock<Vec<CallbackDispatch<*mut ()>>>);
        // Safety: The inner type is a RwLock, which is Sync.
        // Clients of callback_dispatch must make sure that their
        // types are safe to Send across execution contexts.
        unsafe impl Sync for HostDispatch {}

        static LOOKUP_TABLE: HostDispatch = HostDispatch(RwLock::new(Vec::new()));

        // Notice how the table only grows. Since the table is managed through
        // the writer lock, the index is always unique.
        let index = {
            let mut table = LOOKUP_TABLE.0.write().unwrap();
            // Safety: Caller must make sure that this callback and input remain valid for
            // all invocations of the callback. Caller must make sure that the input
            // is treated as Send.
            table.push(unsafe { CallbackDispatch::direct(callback, input) });
            table.len().saturating_sub(1)
        };

        extern "C" fn through_table_with_index(index: ULONG) {
            {
                let table = LOOKUP_TABLE.0.read().unwrap();
                let dispatch = &table[index as usize];
                CallbackDispatch {
                    callback: dispatch.callback,
                    input: dispatch.input,
                }
            }
            .invoke();
        }

        CallbackDispatch {
            callback: through_table_with_index,
            input: index.try_into().unwrap(),
        }
    }

    // Unaccounted for case: let it fail to compile.
}

#[cfg(test)]
mod tests {
    #![allow(clippy::undocumented_unsafe_blocks)]

    use core::sync::atomic::{AtomicUsize, Ordering};
    use std::vec::Vec;

    #[test]
    fn simple_dispatch() {
        static COUNTER: AtomicUsize = AtomicUsize::new(0);
        unsafe extern "C" fn callback(flag: *mut ()) {
            let flag: &AtomicUsize = unsafe { &*(flag.cast()) };
            flag.fetch_add(1, Ordering::Relaxed);
        }

        let input = core::ptr::from_ref(&COUNTER) as *mut ();
        let dispatch = unsafe { super::make(callback, input) };

        let count = COUNTER.load(Ordering::Relaxed);
        dispatch.invoke();
        assert_eq!(COUNTER.load(Ordering::Relaxed), count + 1);
    }

    #[test]
    fn multi_dispatch() {
        static COUNTER: AtomicUsize = AtomicUsize::new(0);
        unsafe extern "C" fn callback(flag: *mut ()) {
            let flag: &AtomicUsize = unsafe { &*(flag.cast()) };
            flag.fetch_add(1, Ordering::Relaxed);
        }

        let input = core::ptr::from_ref(&COUNTER) as *mut ();

        let mut dispatches = Vec::new();
        for _ in 0..100 {
            dispatches.push(unsafe { super::make(callback, input) });
        }

        let count = COUNTER.load(Ordering::Relaxed);

        for dispatch in dispatches {
            dispatch.invoke();
        }
        assert_eq!(COUNTER.load(Ordering::Relaxed), count + 100);
    }
}
