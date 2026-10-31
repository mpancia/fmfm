/* SPDX-License-Identifier: GPL-3.0-only */
/* The sample loops of the Braids analog oscillators, with the arithmetic of each sample in Lean
 * (Firmware/Analog.lean). This file owns the buffers, the pointers and the smoothing of the phase step; the
 * Lean code, included below as inline functions, owns everything else. The loops follow
 * `AnalogOscillator::Render*` in Braids (Emilie Gillet, MIT). */
#include <lean/lean.h>
#include <stddef.h>
#include <stdint.h>

#undef LEAN_EXPORT
#define LEAN_EXPORT static inline
#include "AnalogApi.c"

/* The phase step moves in a straight line from the last block's value to this block's. */
static uint32_t step_increment(uint32_t from, uint32_t to, uint32_t size)
{
    return from < to ? (to - from) / size : ~((from - to) / size);
}

void fm1_analog_render_saw(uint32_t *phase, uint32_t *previous_inc, uint32_t inc_target, int32_t *next_sample,
                           const uint8_t *sync_in, int16_t *buffer, uint8_t *sync_out, uint32_t size)
{
    uint32_t inc = *previous_inc, delta = step_increment(*previous_inc, inc_target, size), p = *phase;
    int32_t next = *next_sample;
    while (size--) {
        uint8_t sync = *sync_in++;
        inc += delta;
        *buffer++ = fm1_saw_out(p, inc, next, sync);
        if (sync_out) *sync_out++ = fm1_saw_sync(p, inc, next, sync);
        {
            uint32_t new_phase = fm1_saw_phase(p, inc, next, sync);
            next = fm1_saw_next(p, inc, next, sync);
            p = new_phase;
        }
    }
    *previous_inc = inc; *phase = p; *next_sample = next;
}

void fm1_analog_render_square(uint32_t *phase, uint32_t *previous_inc, uint32_t inc_target, int32_t *next_sample,
                              uint8_t *high_state, uint32_t pw, const uint8_t *sync_in, int16_t *buffer,
                              uint8_t *sync_out, uint32_t size)
{
    uint32_t inc = *previous_inc, delta = step_increment(*previous_inc, inc_target, size), p = *phase;
    int32_t next = *next_sample;
    uint8_t high = *high_state;
    while (size--) {
        uint8_t sync = *sync_in++;
        inc += delta;
        *buffer++ = fm1_square_out(p, inc, pw, next, high, sync);
        if (sync_out) *sync_out++ = fm1_square_sync(p, inc, pw, next, high, sync);
        {
            uint32_t new_phase = fm1_square_phase(p, inc, pw, next, high, sync);
            int32_t new_next = fm1_square_next(p, inc, pw, next, high, sync);
            high = fm1_square_high(p, inc, pw, next, high, sync);
            p = new_phase; next = new_next;
        }
    }
    *previous_inc = inc; *phase = p; *next_sample = next; *high_state = high;
}

void fm1_analog_render_triangle(uint32_t *phase, uint32_t *previous_inc, uint32_t inc_target, const uint8_t *sync_in,
                                int16_t *buffer, uint32_t size)
{
    uint32_t inc = *previous_inc, delta = step_increment(*previous_inc, inc_target, size), p = *phase;
    while (size--) {
        uint8_t sync = *sync_in++;
        inc += delta;
        *buffer++ = fm1_triangle_out(p, inc, sync);
        p = fm1_triangle_phase(p, inc, sync);
    }
    *previous_inc = inc; *phase = p;
}

void fm1_analog_render_sine(uint32_t *phase, uint32_t *previous_inc, uint32_t inc_target, const uint8_t *sync_in,
                            int16_t *buffer, uint32_t size)
{
    uint32_t inc = *previous_inc, delta = step_increment(*previous_inc, inc_target, size), p = *phase;
    while (size--) {
        uint8_t sync = *sync_in++;
        inc += delta;
        *buffer++ = fm1_sine_out(p, inc, sync);
        p = fm1_sine_phase(p, inc, sync);
    }
    *previous_inc = inc; *phase = p;
}
