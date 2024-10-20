// SPDX-License-Identifier: MPL-2.0
// SPDX-FileCopyrightText: Copyright 2024 Ian McIntyre

//! The application entrypoint.

use core::{
    cell::UnsafeCell,
    mem::ManuallyDrop,
    sync::atomic::{AtomicBool, Ordering},
};

use crate::interrupt_control;

/// A handle to the [`kernel_enter`] initialization context.
///
/// When you have access to an `AppDefine` reference, you're
/// executing in a ThreadX initialization context.
///
/// While this object exists, no application thread or timer will execute.
/// Any threads or timers you create will execute at a later point, sometime
/// after you lose access to this object. Additionally, interrupts
/// are globally disabled while this reference is accessible.
///
/// `'pke` is the "pre-kernel enter" lifetime, or the lifetime of
/// references before the diverging call to [`kernel_enter`](crate::kernel_enter). `'ad`
/// is the application define lifetime, or the lifetime of references
/// generated during the initialization context.
///
/// Since [`kernel_enter`](crate::kernel_enter) diverges, any objects placed on the stack
/// before its invocation are live. Therefore, it is safe for threads and timers
/// created during the initialization context to capture these values.
///
/// # Example
///
/// ```
/// use fusible::{
///     AppDefine,
///     thread::{StaticStack, Thread},
///     timer::{Timer, TimerSchedule},
/// };
/// use core::{pin::pin, num::NonZero};
///
/// static STACK: StaticStack<2048> = StaticStack::new();
/// # fn my_thread(_: &str) { std::process::exit(0); }
/// # fn my_timer(_: &str) {}
///
/// fn main() {
///     let my_resource = String::from("hello world");
///     let timer_runnable = || my_timer(&my_resource);
///
///     let thread = pin!(Thread::context());
///     let timer = pin!(Timer::context());
///
///     fusible::kernel_enter(|app_define: &AppDefine| {
///         app_define.create_thread(
///             thread.into_ref(),
///             STACK.take().unwrap(),
///             &Default::default(),
///             || my_thread(&my_resource),
///         ).unwrap();
///
///         app_define.create_timer(
///             timer.into_ref(),
///             TimerSchedule::periodic(NonZero::new(10).unwrap()),
///             &Default::default(),
///             &timer_runnable,
///         ).unwrap();
///     });
/// }
/// ```
pub struct AppDefine<'ad, 'pke: 'ad> {
    _env: crate::marker::InvariantLifetime<'pke>,
    _ad: crate::marker::InvariantLifetime<'ad>,
    _not_send_or_sync: crate::marker::NotSendOrSync,
}

impl AppDefine<'_, '_> {
    const fn new() -> Self {
        AppDefine {
            _env: crate::marker::InvariantLifetime::mark(),
            _ad: crate::marker::InvariantLifetime::mark(),
            _not_send_or_sync: crate::marker::NotSendOrSync::mark(),
        }
    }
}

/// Enter the kernel and create the system's initial resources.
///
/// The callable `app_define` gives you the chance to create your initial
/// resources. Note that threads do not start until sometime after `app_define`
/// returns, so you're free to create resources in any order you prefer.
///
/// A application must have at least one thread that you create! If you don't
/// create _and start_ a thread, then your application concludes once the kernel
/// enters its scheduling loop.
///
/// If you're calling methods on OS resources within `app_define`, you'll need
/// to use non-blocking actions. Failure to use non-blocking actions will likely
/// result in a caller error. If you need to select (non-)blocking I/O depending
/// on the initialization / thread execution context, check [`is_initializing`].
///
/// For more information on `'pke` and `'ad`, see [`AppDefine`].
///
/// # Example
///
/// ```
/// use fusible::{
///     thread::{Thread, StaticStack, ThreadContext},
///     semaphore::{Semaphore, SemaphoreContext},
/// };
/// use core::pin::Pin;
///
/// static STACK: StaticStack<4096> = StaticStack::new();
/// static THREAD: ThreadContext = Thread::context();
/// static SEMA: SemaphoreContext = Semaphore::context();
/// # fn my_thread(_: &Semaphore) { std::process::exit(0); }
///
/// fn main() {
///     fusible::kernel_enter(|app_define| {
///         let sema = Semaphore::create(
///             Pin::static_ref(&SEMA),
///             &Default::default(),
///         ).unwrap();
///         Thread::create(
///             Pin::static_ref(&THREAD),
///             STACK.take().unwrap(),
///             &Default::default(),
///             move || my_thread(sema),
///         ).unwrap();
///     });
/// }
/// ```
///
/// # Only enter the kernel once
///
/// You should only enter the kernel once in your program. The behavior
/// of multiple entry depends on your port's configuration.
///
/// Fusible defends against a reentrant call to `kernel_enter` by
/// protecting the (global) memory that it allocates. However, it will
/// not prevent you from making multiple `kernel_enter` calls.
pub fn kernel_enter<'pke, F>(app_define: F) -> !
where
    F: for<'ad> FnOnce(&'ad AppDefine<'ad, 'pke>) + 'pke,
{
    use crate::callback_dispatch::CallbackDispatch;

    // Notice how this object is allocated on a stack frame before the
    // diverging call to tx_kernel_enter. This is a stack leak. Since
    // tx_kernel_enter never returns, we'll never (implicitly) invoke
    // this object's drop. Nevertheless, we wrap this in ManuallyDrop
    // to signal that we'll drop this somewhere else.
    let mut app_define = ManuallyDrop::new(app_define);

    /// A specialized static mut that holds a callback dispatch.
    struct AppDefineCallback(UnsafeCell<CallbackDispatch<*mut ()>>);

    /// Exposes a pointer to the stack allocated app_define for the ThreadX
    /// tx_application_define callback.
    static APP_DEFINE_CALLBACK: AppDefineCallback =
        AppDefineCallback(UnsafeCell::new(CallbackDispatch::no_op()));

    // Safety: AppDefineCallback is always accessed while interrupts are
    // disabled. Since interrupts are disabled (and nothing in this function
    // would cause a scheduling change), there is no preemption that would
    // produce multiple mutable references to the dispatch.
    //
    // tx_kernel_enter does not have any reentrant calls that
    // would produce two mutable references to this data.
    unsafe impl Sync for AppDefineCallback {}

    // Safety: See unsafe impl Sync for AppDefine for more information.
    //
    // We clarified earlier that the app_define object remains live on the
    // stack before calling tx_kernel_enter. The app_define_trampoline
    // knows the precise type of the app_define callback.
    unsafe {
        interrupt_control::with_disabled(|| {
            APP_DEFINE_CALLBACK.0.get().write(CallbackDispatch::direct(
                app_define_trampoline::<F>,
                core::ptr::from_mut::<F>(&mut *app_define).cast::<()>(),
            ));
        });
    }

    extern "C" fn app_define_trampoline<'pke, F>(app_define: *mut ())
    where
        F: for<'ad> FnOnce(&'ad AppDefine<'ad, 'pke>) + 'pke,
    {
        // Safety: We know the pointer is of type *mut F, since that's how the
        // callback dispatch typed the function. Read-then-call will drop the
        // closure. We know that the pointer is valid; it lives on a stack
        // frame before the diverging tx_kernel_enter call. We prevent a
        // double call and double-drop by the access pattern on APP_DEFINE_CALLBACK.
        crate::panic::catch_unwind_init(|| unsafe {
            core::ptr::read(app_define.cast::<F>())(&AppDefine::new());
        });
    }

    // Safety: Strong symbol expected to only be defined once
    // per application.
    #[unsafe(no_mangle)]
    extern "C" fn tx_application_define(_: *mut core::ffi::c_void) {
        IN_APP_DEFINE.store(true, Ordering::SeqCst);

        // Safety: tx_application_define executes while interrupts are disabled.
        // This copy of the dispatch object will execute without contention. Once we
        // complete the copy, we release our exclusive mutable access to the static.
        //
        // tx_application_define executes within the tx_kernel_enter call. If we
        // entered tx_kernel_enter from Fusible's kernel_enter, then we observe
        // the write to APP_DEFINE_CALLBACK.
        //
        // If some C user has directly invoked tx_kernel_enter to execute this
        // tx_application_define, we always observe a no-op callback dispatch object
        // because (1) that's how the static is initialized, and (2) we always replace
        // the callback dispatch with that sentinel.
        let dispatch = unsafe {
            APP_DEFINE_CALLBACK
                .0
                .get()
                .replace(CallbackDispatch::no_op())
        };

        dispatch.invoke();

        IN_APP_DEFINE.store(false, Ordering::SeqCst);
    }

    // Safety: Our tx_application_define is safe against multiple calls.
    // The user is responsible for making sure that the higher-level kernel
    // enter isn't called multiple times.
    unsafe { crate::tx_sys::tx_kernel_enter() }
}

static IN_APP_DEFINE: AtomicBool = AtomicBool::new(false);

/// Returns `true` if the caller is executing within the initialization context.
///
/// The initialization context describes execution within the [`kernel_enter`] app define
/// callback.
///
/// # Example
///
/// ```
/// use fusible::thread::{StaticStack, Thread};
/// use core::pin::pin;
///
/// static STACK: StaticStack<4096> = StaticStack::new();
///
/// fn main() {
///     assert!(!fusible::is_initializing());
///
///     let thread = pin!(Thread::context());
///     fusible::kernel_enter(|_| {
///         assert!(fusible::is_initializing());
///
///         Thread::create(
///             thread.into_ref(),
///             STACK.take().unwrap(),
///             &Default::default(),
///             || {
///                 assert!(!fusible::is_initializing());
/// #               std::process::exit(0);
///             },
///         ).unwrap();
///
///         assert!(fusible::is_initializing());
///     });
/// }
/// ```
#[inline]
pub fn is_initializing() -> bool {
    IN_APP_DEFINE.load(Ordering::Relaxed)
}
