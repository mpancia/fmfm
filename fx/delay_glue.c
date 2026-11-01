/* SPDX-License-Identifier: GPL-3.0-only */
/* The delay send: one line of 32768 16-bit samples. Each sample: read the echo `offset` behind the write
 * position, low-pass it, write the send plus the echo times the feedback, move on. The arithmetic of each step
 * is Lean (Firmware/Delay.lean), included below as inline functions; this file owns the line and the states. */
#include <lean/lean.h>
#include <stddef.h>
#include <stdint.h>

#include "delay.h"

#undef LEAN_EXPORT
#define LEAN_EXPORT static inline
#include "DelayApi.c"

#define RING 32768u
#ifdef FM1_CHIP
static int16_t line[RING] __attribute__((section(".pool")));
#else
static int16_t line[RING];
#endif

static uint32_t write_pos, offset = 11025;
static int32_t k_feedback = 16384, k_tone = 26214, lowpass_state;

static int32_t s32(uint32_t v) { return (int32_t)v; }

void fm1_delay_clear(void)
{
    uint32_t i;
    for (i = 0; i < RING; i++) line[i] = 0;
    lowpass_state = 0;
}

void fm1_delay_tune(uint32_t time, uint32_t bpm, uint32_t rate, uint32_t feedback, uint32_t tone)
{
    offset = fm1_dl_samples(time, bpm, rate);
    k_feedback = s32(fm1_dl_feedback_gain(feedback));
    k_tone = s32(fm1_dl_tone_gain(tone));
}

void fm1_delay_block(const int32_t *send, int32_t *wet, uint32_t count)
{
    uint32_t n;
    for (n = 0; n < count; n++) {
        int32_t echo = s32(fm1_dl_fetch((uint16_t)line[fm1_dl_pos(write_pos, offset)]));
        lowpass_state = s32(fm1_dl_lowpass((uint32_t)lowpass_state, (uint32_t)echo, (uint32_t)k_tone));
        line[write_pos] = (int16_t)fm1_dl_store((uint32_t)fm1_dl_input((uint32_t)send[n], (uint32_t)lowpass_state, (uint32_t)k_feedback));
        write_pos = fm1_dl_next_write(write_pos);
        wet[n] = echo;
    }
}
