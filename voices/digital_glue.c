/* SPDX-License-Identifier: GPL-3.0-only */
/* The sample loops of the Braids FM, feedback FM, chaotic FM, ring modulator, toy and digital modulation
 * engines, with the arithmetic of each sample in Lean (Firmware/Digital.lean). This file owns the buffers, the
 * pointers and the smoothing of the parameter; the Lean code, included below as inline functions, owns the rest.
 * The loops follow `DigitalOscillator::Render*` in Braids (Emilie Gillet, MIT). */
#include <lean/lean.h>
#include <stddef.h>
#include <stdint.h>

#undef LEAN_EXPORT
#define LEAN_EXPORT static inline
#include "DigitalApi.c"

/* Parameter 0 moves in a straight line from the last block's value to this block's. */
#define SMOOTH_BEGIN(previous, target, size) \
    int32_t start_ = (previous), change_ = (target) - start_, per_sample_ = 32767 / (int32_t)(size), xfade_ = 0
#define SMOOTH_NEXT() (xfade_ += per_sample_, start_ + (change_ * xfade_ >> 15))

void fm1_digital_render_fm(uint32_t *phase, uint32_t *mod, uint32_t inc, uint32_t mod_inc, int32_t previous_parameter,
                           int32_t parameter, const uint8_t *sync, int16_t *buffer, uint32_t size)
{
    uint32_t p = *phase, m = *mod;
    SMOOTH_BEGIN(previous_parameter, parameter, size);
    while (size--) {
        int32_t index = SMOOTH_NEXT();
        uint8_t s = *sync++;
        *buffer++ = fm1_fm_out(p, m, inc, mod_inc, index, s);
        {
            uint32_t np = fm1_fm_phase(p, m, inc, mod_inc, index, s);
            m = fm1_fm_mod(p, m, inc, mod_inc, index, s);
            p = np;
        }
    }
    *phase = p; *mod = m;
}

void fm1_digital_render_feedback_fm(uint32_t *phase, uint32_t *mod, int16_t *previous, uint32_t inc, uint32_t mod_inc,
                                    int32_t attenuation, int32_t previous_parameter, int32_t parameter,
                                    const uint8_t *sync, int16_t *buffer, uint32_t size)
{
    uint32_t p = *phase, m = *mod;
    int16_t last = *previous;
    SMOOTH_BEGIN(previous_parameter, parameter, size);
    while (size--) {
        int32_t index = SMOOTH_NEXT();
        uint8_t s = *sync++;
        *buffer++ = fm1_feedback_fm_out(p, m, inc, mod_inc, last, index, attenuation, s);
        {
            uint32_t np = fm1_feedback_fm_phase(p, m, inc, mod_inc, last, index, attenuation, s);
            uint32_t nm = fm1_feedback_fm_mod(p, m, inc, mod_inc, last, index, attenuation, s);
            last = fm1_feedback_fm_previous(p, m, inc, mod_inc, last, index, attenuation, s);
            p = np; m = nm;
        }
    }
    *phase = p; *mod = m; *previous = last;
}

void fm1_digital_render_chaotic_fm(uint32_t *phase, uint32_t *mod, int16_t *previous, uint32_t inc, uint32_t mod_inc,
                                   int32_t previous_parameter, int32_t parameter, const uint8_t *sync, int16_t *buffer,
                                   uint32_t size)
{
    uint32_t p = *phase, m = *mod;
    int16_t last = *previous;
    SMOOTH_BEGIN(previous_parameter, parameter, size);
    while (size--) {
        int32_t index = SMOOTH_NEXT();
        uint8_t s = *sync++;
        *buffer++ = fm1_chaotic_fm_out(p, m, inc, mod_inc, index, s);
        {
            uint32_t np = fm1_chaotic_fm_phase(p, m, inc, mod_inc, index, s);
            uint32_t nm = fm1_chaotic_fm_mod(p, m, inc, mod_inc, index, s);
            last = fm1_chaotic_fm_previous(p, m, inc, mod_inc, index, s);
            p = np; m = nm;
        }
    }
    *phase = p; *mod = m; *previous = last;
}

void fm1_digital_render_ring_mod(uint32_t *phase, uint32_t *mod1, uint32_t *mod2, uint32_t inc, uint32_t inc1,
                                 uint32_t inc2, const uint8_t *sync, int16_t *buffer, uint32_t size)
{
    uint32_t p = *phase + (1u << 30), m1 = *mod1, m2 = *mod2;
    while (size--) {
        uint8_t s = *sync++;
        *buffer++ = fm1_ring_mod_out(p, m1, m2, inc, inc1, inc2, s);
        {
            uint32_t np = fm1_ring_mod_phase(p, m1, m2, inc, inc1, inc2, s);
            uint32_t n1 = fm1_ring_mod_mod1(p, m1, m2, inc, inc1, inc2, s);
            m2 = fm1_ring_mod_mod2(p, m1, m2, inc, inc1, inc2, s);
            p = np; m1 = n1;
        }
    }
    *phase = p - (1u << 30); *mod1 = m1; *mod2 = m2;
}

void fm1_digital_render_toy(uint32_t *phase, uint8_t *held, uint16_t *counter, uint32_t inc, uint16_t count, uint8_t x,
                            const uint8_t *sync, int16_t *buffer, uint32_t size)
{
    uint32_t p = *phase;
    uint8_t h = *held;
    uint16_t c = *counter;
    while (size--) {
        uint8_t s = *sync++;
        *buffer++ = fm1_toy_out(p, inc, h, c, count, x, s);
        {
            uint32_t np = fm1_toy_phase(p, inc, h, c, count, x, s);
            uint16_t nc = fm1_toy_counter(p, inc, h, c, count, x, s);
            h = fm1_toy_held(p, inc, h, c, count, x, s);
            p = np; c = nc;
        }
    }
    *phase = p; *held = h; *counter = c;
}

void fm1_digital_render_modulation(uint32_t *phase, uint32_t *symbol_phase, uint16_t *count, int32_t *filter,
                                   uint8_t *data, uint32_t inc, uint32_t symbol_inc, int32_t parameter,
                                   int16_t *buffer, uint32_t size)
{
    uint32_t p = *phase, sp = *symbol_phase;
    uint16_t n = *count;
    int32_t f = *filter;
    uint8_t d = *data;
    while (size--) {
        *buffer++ = fm1_modulation_out(p, inc, sp, symbol_inc, n, f, d, parameter);
        {
            uint32_t np = fm1_modulation_phase(p, inc, sp, symbol_inc, n, f, d, parameter);
            uint32_t nsp = fm1_modulation_symbol(p, inc, sp, symbol_inc, n, f, d, parameter);
            uint16_t nn = fm1_modulation_count(p, inc, sp, symbol_inc, n, f, d, parameter);
            int32_t nf = fm1_modulation_filter(p, inc, sp, symbol_inc, n, f, d, parameter);
            d = fm1_modulation_data(p, inc, sp, symbol_inc, n, f, d, parameter);
            p = np; sp = nsp; n = nn; f = nf;
        }
    }
    *phase = p; *symbol_phase = sp; *count = n; *filter = f; *data = d;
}
