/* SPDX-License-Identifier: GPL-3.0-only */
/* The delay send: two lines of 20480 16-bit samples, left and right. Each sample: read each line's echo `offset`
 * behind the write position, low-pass it, write the send plus the right echo times the feedback into the left
 * line and the left echo times the feedback into the right line, move on. So each echo crosses to the other
 * side. The arithmetic of each step is Lean (Firmware/Delay.lean), included below as inline functions; this file
 * owns the lines and the states. */
#include <lean/lean.h>
#include <stddef.h>
#include <stdint.h>

#include "delay.h"

#undef LEAN_EXPORT
#define LEAN_EXPORT static inline
#include "DelayApi.c"

#define RING 20480u
#ifdef FM1_CHIP
static int16_t left[RING] __attribute__((section(".pool"))), right[RING] __attribute__((section(".pool")));
#else
static int16_t left[RING], right[RING];
#endif

static uint32_t write_pos, offset = 11025;
static int32_t k_feedback = 16384, k_tone = 26214, lowpass_left, lowpass_right;

static int32_t s32(uint32_t v) { return (int32_t)v; }

void fm1_delay_clear(void)
{
    uint32_t i;
    for (i = 0; i < RING; i++) left[i] = right[i] = 0;
    lowpass_left = lowpass_right = 0;
}

void fm1_delay_tune(uint32_t time, uint32_t bpm, uint32_t rate, uint32_t feedback, uint32_t tone)
{
    offset = fm1_dl_samples(time, bpm, rate);
    k_feedback = s32(fm1_dl_feedback_gain(feedback));
    k_tone = s32(fm1_dl_tone_gain(tone));
}

void fm1_delay_block(const int32_t *send, int32_t *wet_left, int32_t *wet_right, uint32_t count)
{
    uint32_t n;
    for (n = 0; n < count; n++) {
        uint32_t at = fm1_dl_pos(write_pos, offset);
        int32_t echo_left = s32(fm1_dl_fetch((uint16_t)left[at])), echo_right = s32(fm1_dl_fetch((uint16_t)right[at]));
        lowpass_left = s32(fm1_dl_lowpass((uint32_t)lowpass_left, (uint32_t)echo_right, (uint32_t)k_tone));
        lowpass_right = s32(fm1_dl_lowpass((uint32_t)lowpass_right, (uint32_t)echo_left, (uint32_t)k_tone));
        left[write_pos] = (int16_t)fm1_dl_store((uint32_t)fm1_dl_input((uint32_t)send[n], (uint32_t)lowpass_left, (uint32_t)k_feedback));
        right[write_pos] = (int16_t)fm1_dl_store((uint32_t)fm1_dl_input(0, (uint32_t)lowpass_right, (uint32_t)k_feedback));
        write_pos = fm1_dl_next_write(write_pos);
        wet_left[n] = echo_left; wet_right[n] = echo_right;
    }
}
