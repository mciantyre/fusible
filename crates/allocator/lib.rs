// SPDX-License-Identifier: MPL-2.0
// SPDX-FileCopyrightText: Copyright 2024 Ian McIntyre

//! A Fusible global allocator, using a byte pool.
//!
//! Use [`initialize`] to provide the global allocator with a memory
//! allocation. Once initialized, the initialization context and thread
//! execution context can access the heap. The allocator considers the
//! thread priority when performing allocations.
//!
//! The package registers the global allocator for only those targets
//! that require it.
//!
//! # Panics
//!
//! Your program panics if it tries to access the heap before [`initialize`]
//! is called. It also panics if an ISR attempts to allocate.
//!
//! # Examples
//!
//! Initialize the global allocator within your custom kernel entrance. Once
//! initialized, subsequent code in `app_define` can access the heap.
//!
//! ```no_run
//! use fusible::AppDefine;
//!
//! fn my_kernel_enter<'pke, F>(app_define: F) -> !
//! where
//!     F: for<'ad> FnOnce(&'ad AppDefine<'ad, 'pke>) + 'pke,
//! {
//!     fusible::kernel_enter(|ctx| {
//!         let heap_start = // ...
//! #           core::ptr::null_mut();
//!         let heap_len = // ...
//! #           32;
//!         unsafe { fusible_allocator::initialize(ctx, heap_start, heap_len) }.unwrap();
//!         app_define(ctx);
//!     })
//! }
//! ```

#![no_std]

extern crate alloc;

use core::pin::Pin;

pub use fusible::byte_pool::{BytePoolInfo as AllocatorInfo, CreateError};
use fusible::{
    AppDefine, WaitOption,
    byte_pool::{self, BytePool, BytePoolContext, BytePoolOptions},
};

#[cfg_attr(all(target_arch = "arm", target_os = "none"), global_allocator)]
#[unsafe(no_mangle)]
static GLOBAL_ALLOCATOR: BytePoolAllocator = BytePoolAllocator {
    byte_pool: BytePool::context(),
};

struct BytePoolAllocator {
    byte_pool: BytePoolContext<'static>,
}

/// Initialize the allocator.
///
/// On success, you're given a function lets allows an application definition
/// access the heap with non-blocking calls. Consider using this if your system
/// needs to perform heap allocations before threads are available.
///
/// See [the module-level documentation](crate) for an example.
///
/// # Safety
///
/// The allocator's storage must outlive the allocator. The memory for
/// the allocator must not be used for anything else.
#[inline]
pub unsafe fn initialize<'ad, 'pke>(
    _: &'ad AppDefine<'ad, 'pke>,
    start: *mut u32,
    len: usize,
) -> Result<(), CreateError> {
    let mut opts = BytePoolOptions::default();
    opts.name = Some(c"global-allocator");
    unsafe {
        BytePool::create_unchecked(
            Pin::static_ref(&GLOBAL_ALLOCATOR.byte_pool),
            start.cast(),
            len,
            &opts,
        )?;
    }

    Ok(())
}

fn byte_pool() -> &'static BytePool {
    BytePoolContext::try_created(Pin::static_ref(&GLOBAL_ALLOCATOR.byte_pool)).unwrap()
}

/// Retrieve runtime information regarding the allocator.
///
/// # Panics
///
/// Panics if the allocator hasn't been initialized.
pub fn info() -> AllocatorInfo<'static> {
    byte_pool().info()
}

unsafe impl core::alloc::GlobalAlloc for BytePoolAllocator {
    unsafe fn alloc(&self, layout: core::alloc::Layout) -> *mut u8 {
        let wait_option = if fusible::is_initializing() {
            WaitOption::no_wait()
        } else {
            WaitOption::wait_forever()
        };

        byte_pool::allocate(&byte_pool(), layout, wait_option).unwrap_or(core::ptr::null_mut())
    }

    unsafe fn dealloc(&self, ptr: *mut u8, layout: core::alloc::Layout) {
        byte_pool().prioritize();
        let result = unsafe { byte_pool::release(ptr, layout) };

        if result.is_err() {
            alloc::alloc::handle_alloc_error(layout);
        }
    }
}
