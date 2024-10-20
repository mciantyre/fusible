// SPDX-License-Identifier: MPL-2.0
// SPDX-FileCopyrightText: Copyright 2024 Ian McIntyre

//! Demonstrates the multi-producer, multi-consumer queue.
//!
//! A pool of producers send values to a pool of transformers.
//! These pools share a single queue.
//!
//! The pool of transformers transform the data, then send it to
//! a verifier service. The pool and the verifier share another queue.

use std::pin::Pin;

use fusible::{
    queue::{Queue, QueueContext, StaticQueueSlots},
    thread::{Stack, Thread, ThreadContext},
};

type TestQueue = Queue<Vec<u32>>;

/// Bridges the producer and transformer pools
static QUEUE_PROD_TRANS: QueueContext<Vec<u32>> = Queue::context();
/// Bridges the transformer pool and the verifier.
static QUEUE_TRANS_VERIFY: QueueContext<Vec<u32>> = Queue::context();

const PROD_SIZE: usize = 4;
const TRANS_SIZE: usize = 9;

static PROD_SLOTS: StaticQueueSlots<Vec<u32>, PROD_SIZE> = StaticQueueSlots::new();
static TRANS_SLOTS: StaticQueueSlots<Vec<u32>, TRANS_SIZE> = StaticQueueSlots::new();

/// Send chunks of the iterator through the queue.
fn producer(queue: &TestQueue, mut iter: impl Iterator<Item = u32>, chunks: usize) {
    let iter = iter.by_ref();
    let mut values = Vec::from_iter(iter.take(chunks));
    while !values.is_empty() {
        queue
            .send(std::mem::replace(
                &mut values,
                Vec::from_iter(iter.take(chunks)),
            ))
            .unwrap();
    }
}

/// Transform the values.
///
/// These threads will die when the process exits.
fn transform(inputs: &TestQueue, outputs: &TestQueue) {
    loop {
        let values = inputs.receive().unwrap();
        let values = values.into_iter().map(|v| v * 10);
        outputs.send(values.collect()).unwrap();
    }
}

/// This thread verifies the results.
fn verify(results: &TestQueue, expectation: Vec<u32>) {
    let mut actual = Vec::with_capacity(expectation.len());
    while actual.len() != expectation.len() {
        let batch = results.receive().unwrap();
        actual.extend(batch)
    }

    actual.sort();
    assert_eq!(actual, expectation);
    std::process::exit(0);
}

fn thread_resources() -> (
    Pin<&'static ThreadContext<'static>>,
    &'static mut Stack<1024>,
) {
    (
        Pin::static_ref(Box::leak(Box::new(Thread::context()))),
        Box::leak(Box::new(Stack::new())),
    )
}

#[test]
fn mpmc() {
    let producers: Vec<_> = (0..7).map(|_| thread_resources()).collect();
    let transformers: Vec<_> = (0..4).map(|_| thread_resources()).collect();
    let (verifier_thread, verifier_stack) = thread_resources();

    fusible::kernel_enter(|app_define| {
        let prod_trans = Pin::static_ref(&QUEUE_PROD_TRANS);
        let trans_verify = Pin::static_ref(&QUEUE_TRANS_VERIFY);

        let prod_trans =
            Queue::create(prod_trans, PROD_SLOTS.take().unwrap(), &Default::default()).unwrap();
        let trans_verify = Queue::create(
            trans_verify,
            TRANS_SLOTS.take().unwrap(),
            &Default::default(),
        )
        .unwrap();

        let info = prod_trans.info();
        assert_eq!(info.enqueued, 0);
        assert_eq!(info.available_storage, PROD_SIZE as _);

        let info = trans_verify.info();
        assert_eq!(info.enqueued, 0);
        assert_eq!(info.available_storage, TRANS_SIZE as _);

        let mut start = 1;
        let mut end = 5;
        let mut chunks = 3;
        let mut values: Vec<u32> = Vec::new();

        for (thread, stack) in producers.into_iter() {
            let range = start..end;
            values.extend(range.clone());
            app_define
                .create_thread(
                    thread,
                    stack.as_mut_slice(),
                    &Default::default(),
                    move || producer(prod_trans, range, chunks),
                )
                .unwrap();

            start += 13;
            end += 17;
            chunks *= 7;
        }

        for (thread, stack) in transformers.into_iter() {
            app_define
                .create_thread(
                    thread,
                    stack.as_mut_slice(),
                    &Default::default(),
                    move || transform(prod_trans, trans_verify),
                )
                .unwrap();
        }

        let mut expectations: Vec<_> = values.into_iter().map(|v| v * 10).collect();
        expectations.sort();

        app_define
            .create_thread(
                verifier_thread,
                verifier_stack.as_mut_slice(),
                &Default::default(),
                move || verify(trans_verify, expectations),
            )
            .unwrap();
    });
}
