// SPDX-License-Identifier: MPL-2.0
// SPDX-FileCopyrightText: Copyright 2024 Ian McIntyre

//! Make sure that a thread cannot capture the AppDefine reference.
//!
//! If a thread were able to capture the AppDefine reference, it would
//! be able to signal to callees that we're executing in the application
//! definition callback. That wouldn't be true; we'd be executing in
//! a thread!
//!
//! With a little bit of unsafe code, we make sure that this is true
//! no matter the Send and Sync bounds on AppDefine.

use core::pin::pin;
use fusible::thread::{StaticStack, Thread};

static STACK: StaticStack<512> = StaticStack::new();

#[derive(Clone, Copy)]
struct UnsafeAppDefine<'ad, 'pke>(&'ad fusible::AppDefine<'ad, 'pke>);
unsafe impl Sync for UnsafeAppDefine<'_, '_> {}
unsafe impl Send for UnsafeAppDefine<'_, '_> {}
impl<'ad, 'pke> core::ops::Deref for UnsafeAppDefine<'ad, 'pke> {
    type Target = &'ad fusible::AppDefine<'ad, 'pke>;
    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

fn main() {
    let thread = pin!(Thread::context());
    fusible::kernel_enter(|app_define| {
        let app_define = UnsafeAppDefine(app_define);
        app_define
            .create_thread(
                thread.into_ref(),
                STACK.take().unwrap(),
                &Default::default(),
                move || {
                    let _app_define = app_define;
                },
            )
            .unwrap();
        let _app_define = app_define;
    });
}
