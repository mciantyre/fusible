// SPDX-License-Identifier: MPL-2.0
// SPDX-FileCopyrightText: Copyright 2024 Ian McIntyre

#include "tx_api.h"

#include <stdint.h>

extern TX_SEMAPHORE THREAD_FINISHED;

TX_QUEUE msg_queue;
TX_THREAD sender_thread;
TX_THREAD receiver_thread;

void sender_thread_entry(TX_SEMAPHORE *finished)
{
    for (uint32_t i = 0; i < 10; ++i)
    {
        tx_queue_send(&msg_queue, &i, TX_WAIT_FOREVER);
        tx_thread_sleep(10);
    }

    tx_semaphore_put(finished);
}

TX_QUEUE block_xform_input;
TX_QUEUE block_xform_output;

#define UINT32_PER_BLOCK 12
typedef uint32_t my_block[UINT32_PER_BLOCK];
typedef my_block *my_block_ptr;

extern TX_BLOCK_POOL BLOCK_POOL;

static my_block_ptr block_input_storage[1];
static my_block_ptr block_output_storage[4];

static uint32_t block_xform_stack[1024];
static TX_THREAD block_xform_thread;

static void block_xform(uint32_t x)
{
    (void)x;

    uint32_t count = 18;
    while (count > 0)
    {
        --count;

        my_block_ptr incremented;
        tx_queue_receive(
            &block_xform_input,
            &incremented,
            TX_WAIT_FOREVER);

        my_block_ptr bitflipped;
        tx_block_allocate(
            &BLOCK_POOL,
            (void *)&bitflipped,
            TX_WAIT_FOREVER);

        for (size_t idx = 0; idx < UINT32_PER_BLOCK; ++idx)
        {
            (*incremented)[idx] += 37;
            (*bitflipped)[idx] = ~(*incremented)[idx];
        }

        tx_queue_send(
            &block_xform_output,
            &bitflipped,
            TX_WAIT_FOREVER);
        tx_queue_send(
            &block_xform_output,
            &incremented,
            TX_WAIT_FOREVER);
    }

    tx_semaphore_put(&THREAD_FINISHED);
}

static struct MutexU32
{
    TX_MUTEX control_block;
    uint32_t data;
} antipattern;

TX_EVENT_FLAGS_GROUP pattern_flags;
extern void run_from_c(TX_EVENT_FLAGS_GROUP *pattern_flags, struct MutexU32 *antipattern, TX_THREAD *other);
extern TX_THREAD FLAG_SIGNAL_THREAD;
extern TX_THREAD FLAG_RETRIEVAL_THREAD;

static void flag_signal_entrypoint(uint32_t x)
{
    (void)x;
    uint32_t count = 37;
    while (count > 0)
    {
        --count;

        const uint32_t pattern = UINT32_C(1) | (count ^ (count << UINT32_C(8)));

        tx_mutex_get(&antipattern.control_block, TX_WAIT_FOREVER);
        antipattern.data = ~pattern;
        tx_mutex_put(&antipattern.control_block);

        tx_event_flags_set(&pattern_flags, pattern, TX_OR);
        tx_thread_suspend(&FLAG_SIGNAL_THREAD);
    }

    tx_semaphore_put(&THREAD_FINISHED);
}

static void flag_retrival_entrypoint(uint32_t x)
{
    (void)x;
    run_from_c(&pattern_flags, &antipattern, &FLAG_SIGNAL_THREAD);
    tx_semaphore_put(&THREAD_FINISHED);
}

static uint32_t flag_signal_stack[1024];
static uint32_t flag_retrival_stack[1024];

uint32_t setup_c(void)
{
    uint32_t result;
    result = tx_queue_create(
        &block_xform_input,
        NULL,
        sizeof(my_block_ptr) / sizeof(uint32_t),
        block_input_storage,
        sizeof(block_input_storage));
    if (TX_SUCCESS != result)
    {
        return result;
    }

    result = tx_queue_create(
        &block_xform_output,
        NULL,
        sizeof(my_block_ptr) / sizeof(uint32_t),
        block_output_storage,
        sizeof(block_output_storage));
    if (TX_SUCCESS != result)
    {
        return result;
    }

    result = tx_thread_create(
        &block_xform_thread,
        NULL,
        block_xform,
        0,
        block_xform_stack,
        sizeof(block_xform_stack),
        31,
        31,
        TX_NO_TIME_SLICE,
        TX_AUTO_START);
    if (TX_SUCCESS != result)
    {
        return result;
    }

    result = tx_thread_create(
        &FLAG_SIGNAL_THREAD,
        NULL,
        flag_signal_entrypoint,
        0,
        flag_signal_stack,
        sizeof(flag_signal_stack),
        31,
        31,
        TX_NO_TIME_SLICE,
        TX_AUTO_START);
    if (TX_SUCCESS != result)
    {
        return result;
    }

    result = tx_thread_create(
        &FLAG_RETRIEVAL_THREAD,
        NULL,
        flag_retrival_entrypoint,
        0,
        flag_retrival_stack,
        sizeof(flag_retrival_stack),
        31,
        31,
        TX_NO_TIME_SLICE,
        TX_AUTO_START);
    if (TX_SUCCESS != result)
    {
        return result;
    }

    result = tx_mutex_create(
        &antipattern.control_block,
        NULL,
        TX_NO_INHERIT);
    if (TX_SUCCESS != result)
    {
        return result;
    }

    return result;
}
