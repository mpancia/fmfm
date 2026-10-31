/* SPDX-License-Identifier: GPL-3.0-only */
/* The sample loops of the Braids saw swarm, digital filter, vosim and harmonics engines, with the arithmetic of
 * each sample in Lean (Firmware/Filters.lean). This file owns the buffers and pointers. The loops follow
 * `DigitalOscillator::Render*` in Braids (Emilie Gillet, MIT). */
#include <lean/lean.h>
#include <stddef.h>
#include <stdint.h>

#undef LEAN_EXPORT
#define LEAN_EXPORT static inline
#include "FiltersApi.c"

#define HARMONICS 12

void fm1_filters_render_swarm(uint32_t *phase, uint32_t *saws, const uint32_t *inc, int32_t f, int32_t damp,
                              int32_t *bp_state, int32_t *lp_state, const uint8_t *sync, int16_t *buffer, uint32_t size)
{
    uint32_t p = *phase;
    int32_t bp = *bp_state, lp = *lp_state;
    while (size--) {
        int i;
        int32_t sample;
        if (*sync++)
            for (i = 0; i < 6; ++i) saws[i] = 0;
        p += inc[0];
        for (i = 0; i < 6; ++i) saws[i] += inc[i + 1];
        sample = (int16_t)fm1_swarm_shape(p, saws[0], saws[1], saws[2], saws[3], saws[4], saws[5]);
        *buffer++ = fm1_swarm_filter_out(sample, f, damp, bp, lp);
        {
            int32_t nl = fm1_swarm_filter_lp(sample, f, damp, bp, lp);
            bp = fm1_swarm_filter_bp(sample, f, damp, bp, lp);
            lp = nl;
        }
    }
    *phase = p; *bp_state = bp; *lp_state = lp;
}

void fm1_filters_render_digital_filter(uint32_t *phase, uint32_t inc, uint32_t *mod_phase, uint32_t *mod_inc,
                                       uint32_t mod_inc_step, uint32_t *square_phase, int32_t *integrator,
                                       uint8_t *polarity, uint8_t filter_type, int32_t parameter,
                                       const uint8_t *sync, int16_t *buffer, uint32_t size)
{
    uint32_t p = *phase, m = *mod_phase, mi = *mod_inc, sq = *square_phase;
    int32_t integ = *integrator;
    uint8_t pol = *polarity;
    while (size--) {
        uint8_t s = *sync++;
        mi += mod_inc_step;
        *buffer++ = fm1_digital_filter_out(p, inc, m, mi, sq, integ, pol, filter_type, parameter, s);
        {
            uint32_t np = fm1_digital_filter_phase(p, inc, m, mi, sq, integ, pol, filter_type, parameter, s);
            uint32_t nm = fm1_digital_filter_mod(p, inc, m, mi, sq, integ, pol, filter_type, parameter, s);
            uint32_t nsq = fm1_digital_filter_square(p, inc, m, mi, sq, integ, pol, filter_type, parameter, s);
            int32_t ni = fm1_digital_filter_integrator(p, inc, m, mi, sq, integ, pol, filter_type, parameter, s);
            pol = fm1_digital_filter_polarity(p, inc, m, mi, sq, integ, pol, filter_type, parameter, s);
            p = np; m = nm; sq = nsq; integ = ni;
        }
    }
    *phase = p; *mod_phase = m; *mod_inc = mi; *square_phase = sq; *integrator = integ; *polarity = pol;
}

void fm1_filters_render_vosim(uint32_t *phase, uint32_t inc, uint32_t *formants, const uint32_t *formant_inc,
                              const uint8_t *sync, int16_t *buffer, uint32_t size)
{
    uint32_t p = *phase, f0 = formants[0], f1 = formants[1];
    while (size--) {
        uint8_t s = *sync++;
        *buffer++ = fm1_vosim_out(p, inc, f0, f1, formant_inc[0], formant_inc[1], s);
        {
            uint32_t np = fm1_vosim_phase(p, inc, f0, f1, formant_inc[0], formant_inc[1], s);
            uint32_t n0 = fm1_vosim_f0(p, inc, f0, f1, formant_inc[0], formant_inc[1], s);
            f1 = fm1_vosim_f1(p, inc, f0, f1, formant_inc[0], formant_inc[1], s);
            p = np; f0 = n0;
        }
    }
    *phase = p; formants[0] = f0; formants[1] = f1;
}

void fm1_filters_render_harmonics(uint32_t *phase, int16_t *previous, uint32_t inc, int32_t *amplitude,
                                  const int32_t *target, const uint8_t *sync, int16_t *buffer, uint32_t size)
{
    uint32_t p = *phase;
    int16_t last = *previous;
    while (size) {
        int32_t sum = 0;
        uint32_t i;
        p += inc;
        if (*sync++ || *sync++) p = 0;
        for (i = 0; i < HARMONICS; ++i) {
            sum += fm1_harmonic_sine(p, i + 1, amplitude[i]);
            amplitude[i] = fm1_harmonic_glide(amplitude[i], target[i]);
        }
        *buffer++ = fm1_harmonics_mid(sum, last);
        *buffer++ = last = fm1_harmonics_out(sum);
        size -= 2;
    }
    *phase = p; *previous = last;
}
