/* SPDX-License-Identifier: GPL-3.0-only */
/* The mixing loops of the Braids macro oscillator, with the arithmetic of each sample in Lean
 * (Firmware/Macro.lean) and the smoothing of the second parameter across the block in Lean too
 * (Firmware/Smooth.lean). This file owns the buffers. The loops follow `MacroOscillator::Render*` in Braids
 * (Emilie Gillet, MIT). */
#include <lean/lean.h>
#include <stddef.h>
#include <stdint.h>
#include "macro_glue.h"

#undef LEAN_EXPORT
#define LEAN_EXPORT static inline
#include "MacroApi.c"
#define _G_initialized smooth_initialized   /* every generated file names its init flag the same */
#include "SmoothApi.c"
#undef _G_initialized

#define SMOOTH_BEGIN(previous, target, size) \
    int32_t start_ = (previous), target_ = (target), per_sample_ = fm1_smooth_per_sample(size), xfade_ = 0
#define SMOOTH_NEXT() (xfade_ = fm1_smooth_advance(xfade_, per_sample_), fm1_smooth_parameter(start_, target_, xfade_))

void fm1_macro_render_csaw(int16_t *buffer, int32_t shift, uint32_t size)
{
    while (size--) {
        *buffer = fm1_macro_csaw(*buffer, shift);
        buffer++;
    }
}

void fm1_macro_render_morph(int16_t *buffer, const int16_t *other, uint32_t balance, int32_t *lp_state, int32_t f,
                            int32_t fuzz, uint32_t size)
{
    int32_t lp = *lp_state;
    while (size--) {
        int32_t a = *buffer, b = *other++;
        *buffer++ = fm1_macro_morph_out(a, b, balance, lp, f, fuzz);
        lp = fm1_macro_morph_lp(a, b, balance, lp, f, fuzz);
    }
    *lp_state = lp;
}

void fm1_macro_render_saw_square(int16_t *buffer, const int16_t *square, int32_t previous_parameter,
                                 int32_t parameter, uint32_t size)
{
    SMOOTH_BEGIN(previous_parameter, parameter, size);
    while (size--) {
        int32_t p = SMOOTH_NEXT();
        *buffer = fm1_macro_saw_square(*buffer, *square++, p);
        buffer++;
    }
}

void fm1_macro_render_triple_add(int16_t *buffer, const int16_t *other, uint32_t size)
{
    while (size--) {
        *buffer = fm1_macro_triple_add(*buffer, *other++);
        buffer++;
    }
}

void fm1_macro_render_sub(int16_t *buffer, const int16_t *other, int32_t previous_parameter, int32_t parameter,
                          uint32_t size)
{
    SMOOTH_BEGIN(previous_parameter, parameter, size);
    while (size--) {
        int32_t p = SMOOTH_NEXT();
        *buffer = fm1_macro_sub(*buffer, *other++, p);
        buffer++;
    }
}

void fm1_macro_render_dual_sync(int16_t *buffer, const int16_t *other, int32_t previous_parameter,
                                int32_t parameter, uint32_t size)
{
    SMOOTH_BEGIN(previous_parameter, parameter, size);
    while (size--) {
        int32_t p = SMOOTH_NEXT();
        *buffer = fm1_macro_dual_sync(*buffer, *other++, p);
        buffer++;
    }
}

void fm1_macro_render_sine_triangle(int16_t *buffer, const int16_t *other, int32_t previous_parameter,
                                    int32_t parameter, uint32_t size)
{
    SMOOTH_BEGIN(previous_parameter, parameter, size);
    while (size--) {
        int32_t p = SMOOTH_NEXT();
        *buffer = fm1_macro_sine_triangle(*buffer, *other++, p);
        buffer++;
    }
}

void fm1_macro_render_buzz(int16_t *buffer, const int16_t *other, uint32_t size)
{
    while (size--) {
        *buffer = fm1_macro_buzz(*buffer, *other++);
        buffer++;
    }
}
