/* SPDX-License-Identifier: GPL-3.0-only */
/* The sample loops of the Braids wavetable, wave map, wave line and paraphonic engines, with the arithmetic of
 * each sample in Lean (Firmware/Wavetables.lean). This file owns the buffers and pointers; the C++ chooses the
 * waves. The loops follow `DigitalOscillator::Render*` in Braids (Emilie Gillet, MIT). */
#include <lean/lean.h>
#include <stddef.h>
#include <stdint.h>

#undef LEAN_EXPORT
#define LEAN_EXPORT static inline
#include "WavetablesApi.c"

void fm1_wavetables_render_table(uint32_t *phase, uint32_t inc, uint32_t wave_a, uint32_t wave_b, uint32_t balance,
                                 const uint8_t *sync, int16_t *buffer, uint32_t size)
{
    uint32_t p = *phase;
    while (size--) {
        uint8_t s = *sync++;
        *buffer++ = fm1_wavetable_out(p, inc, wave_a, wave_b, balance, s);
        p = fm1_wavetable_phase(p, inc, wave_a, wave_b, balance, s);
    }
    *phase = p;
}

void fm1_wavetables_render_map(uint32_t *phase, uint32_t inc, const uint32_t *waves, uint32_t xfade_x,
                               uint32_t xfade_y, const uint8_t *sync, int16_t *buffer, uint32_t size)
{
    uint32_t p = *phase;
    while (size--) {
        uint8_t s = *sync++;
        *buffer++ = fm1_wave_map_out(p, inc, waves[0], waves[1], waves[2], waves[3], xfade_x, xfade_y, s);
        p = fm1_wave_map_phase(p, inc, waves[0], waves[1], waves[2], waves[3], xfade_x, xfade_y, s);
    }
    *phase = p;
}

/* The wave line has four modes by the second parameter: how the "rough" (blocky phase) and "smooth" readings
 * and the two crossfades are combined. */
void fm1_wavetables_render_line(uint32_t *phase, uint32_t inc, uint32_t wave_0, uint32_t wave_1, uint32_t wave_2,
                                uint32_t smooth_xfade, uint32_t rough_step, uint32_t balance, uint32_t mode,
                                const uint8_t *sync, int16_t *buffer, uint32_t size)
{
    uint32_t p = *phase, rough = 0;
    uint32_t a0 = wave_0, a1 = wave_1, xa_step = 0, mask_a = 0xFFFFFFFFu;
    uint32_t b0 = wave_1, b1 = wave_2, xb = smooth_xfade, xb_step = 0, mask_b = 0xFFFFFFFFu;
    uint32_t xa = smooth_xfade;
    int use_rough_a = 0, use_rough_b = 0;
    if (mode == 0) {
        b0 = wave_0; b1 = wave_1; mask_a = 0xFE000000u;
        use_rough_a = use_rough_b = 1; xa_step = xb_step = rough_step;
    } else if (mode == 1) {
        use_rough_a = 1; xa_step = rough_step;
        a0 = wave_0; a1 = wave_1;
    } else if (mode == 2) {
        a0 = wave_1; a1 = wave_2; mask_b = 0xFE000000u;
    } else {
        a0 = wave_1; a1 = wave_2; mask_a = 0xFE000000u; mask_b = 0xF8000000u;
    }
    while (size--) {
        uint8_t s = *sync++;
        uint32_t ra = use_rough_a ? rough : xa, rb = use_rough_b ? rough : xb;
#define ARGS p, inc, a0, a1, ra, xa_step, mask_a, b0, b1, rb, xb_step, mask_b, balance, s
        *buffer++ = fm1_wave_line_out(ARGS);
        p = fm1_wave_line_phase(ARGS);
#undef ARGS
        rough = (rough + 2 * rough_step) & 0xFFFF;
    }
    *phase = p;
}

void fm1_wavetables_render_paraphonic(uint32_t *phases, const uint32_t *inc, uint32_t wave_a, uint32_t wave_b,
                                      uint32_t balance, int16_t *buffer, uint32_t size)
{
    uint32_t p0 = phases[0], p1 = phases[1], p2 = phases[2], p3 = phases[3];
    while (size) {
        int half;
        for (half = 0; half < 2; ++half) {
#define ARGS p0, p1, p2, p3, inc[0], inc[1], inc[2], inc[3], wave_a, wave_b, balance
            *buffer++ = fm1_paraphonic_out(ARGS);
            {
                uint32_t n0 = fm1_paraphonic_p0(ARGS), n1 = fm1_paraphonic_p1(ARGS);
                uint32_t n2 = fm1_paraphonic_p2(ARGS);
                p3 = fm1_paraphonic_p3(ARGS);
                p0 = n0; p1 = n1; p2 = n2;
            }
#undef ARGS
        }
        size -= 2;
    }
    phases[0] = p0; phases[1] = p1; phases[2] = p2; phases[3] = p3;
}
