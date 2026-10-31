/* SPDX-License-Identifier: GPL-3.0-only */
/* The sample loops of the Braids kick, snare, cymbal, struck bell and struck drum, with the arithmetic of each
 * sample in Lean (Firmware/Percussion.lean). This file owns the buffers and the state arrays; the C++ side hands
 * its `Svf` and `Excitation` objects over as plain registers. The loops follow `DigitalOscillator::Render*` in
 * Braids (Emilie Gillet, MIT). */
#include <lean/lean.h>
#include <stddef.h>
#include <stdint.h>
#include "percussion_glue.h"

#undef LEAN_EXPORT
#define LEAN_EXPORT static inline
#include "PercussionApi.c"

int16_t fm1_braids_random_sample(void);

int32_t fm1_svf_cutoff_of(int32_t frequency) { return fm1_svf_cutoff(frequency); }
int32_t fm1_svf_damp_of(int32_t resonance) { return fm1_svf_damp(resonance); }

static int32_t svf_process(fm1_svf_regs *s, int32_t in)
{
    int32_t out = fm1_svf_out(in, s->f, s->damp, s->punch, s->lp, s->bp, s->mode);
    int32_t lp = fm1_svf_lp(in, s->f, s->damp, s->punch, s->lp, s->bp, s->mode);
    s->bp = fm1_svf_bp(in, s->f, s->damp, s->punch, s->lp, s->bp, s->mode);
    s->lp = lp;
    return out;
}

static int32_t excite_process(fm1_excite_regs *e)
{
    int32_t out = fm1_excite_out(e->state, e->decay, e->counter, e->level);
    int32_t state = fm1_excite_state(e->state, e->decay, e->counter, e->level);
    e->counter = fm1_excite_counter(e->state, e->decay, e->counter, e->level);
    e->state = state;
    return out;
}

void fm1_percussion_render_kick(fm1_excite_regs *pulse, fm1_svf_regs *svf, int32_t *lp_state, int32_t pitch,
                                int32_t coefficient, int16_t *buffer, uint32_t size)
{
    int32_t lp = *lp_state, frequency = 0;
    int have_frequency = 0;
    while (size) {
        int32_t excitation = 0, j;
        excitation += excite_process(&pulse[0]);
        excitation += pulse[1].counter != 0 ? 16384 : 0;
        excitation += excite_process(&pulse[1]);
        excite_process(&pulse[2]);
        {
            int32_t f = (int16_t)(pitch + (pulse[2].counter == 0 ? 0 : 17 << 7));
            if (!have_frequency || f != frequency) {
                svf->f = fm1_svf_cutoff(f);
                frequency = f; have_frequency = 1;
            }
        }
        for (j = 0; j < 2; ++j) {
            int32_t resonator = svf_process(svf, excitation);
            *buffer++ = fm1_kick_out(excitation, resonator, lp, coefficient);
            lp = fm1_kick_lp(excitation, resonator, lp, coefficient);
        }
        size -= 2;
    }
    *lp_state = lp;
}

void fm1_percussion_render_snare(fm1_excite_regs *pulse, fm1_svf_regs *svf, int32_t g1, int32_t g2, int16_t *buffer,
                                 uint32_t size)
{
    while (size) {
        int32_t excitation_1 = 0, excitation_2 = 0, noise, f1, f2, f3;
        int16_t sd;
        excitation_1 += excite_process(&pulse[0]);
        excitation_1 += excite_process(&pulse[1]);
        excitation_1 += pulse[1].counter != 0 ? 2621 : 0;
        excitation_2 += excite_process(&pulse[2]);
        excitation_2 += pulse[2].counter != 0 ? 13107 : 0;
        noise = fm1_braids_random_sample() * excite_process(&pulse[3]) >> 15;
        f1 = svf_process(&svf[0], excitation_1);
        f2 = svf_process(&svf[1], excitation_2);
        f3 = svf_process(&svf[2], noise);
        sd = fm1_snare_mix(f1, excitation_1, f2, excitation_2, f3, g1, g2);
        *buffer++ = sd;
        *buffer++ = sd;
        size -= 2;
    }
}

void fm1_percussion_render_cymbal(uint32_t *phase, uint32_t *hat_phase, uint32_t *rng, const uint32_t *inc,
                                  fm1_svf_regs *svf, int32_t xfade, int16_t *buffer, uint32_t size)
{
    uint32_t p = *phase, r = *rng;
    while (size--) {
        int32_t metal, white, i;
        p += inc[6];
        if (p < inc[6]) r = fm1_cymbal_lcg(r);
        for (i = 0; i < 6; ++i) hat_phase[i] += inc[i];
        metal = fm1_cymbal_hat_noise(hat_phase[0], hat_phase[1], hat_phase[2], hat_phase[3], hat_phase[4], hat_phase[5]);
        metal = svf_process(&svf[0], metal);
        white = svf_process(&svf[1], fm1_cymbal_white(r));
        *buffer++ = fm1_cymbal_out(metal, white, xfade);
    }
    *phase = p; *rng = r;
}

#define BELL_PARTIALS 11
#define DRUM_PARTIALS 6

void fm1_percussion_render_bell(uint32_t *phase, const uint32_t *inc, const int32_t *amplitude, int16_t *previous,
                                int16_t *buffer, uint32_t size)
{
    int16_t last = *previous;
    while (size) {
        int32_t sum = 0, i;
        for (i = 0; i < BELL_PARTIALS; ++i) {
            sum += fm1_bell_partial_contribution(phase[i], inc[i], amplitude[i]);
            phase[i] = fm1_bell_partial_phase(phase[i], inc[i], amplitude[i]);
        }
        *buffer++ = fm1_partials_mid(sum, last);
        *buffer++ = last = (int16_t)fm1_partials_out(sum);
        size -= 2;
    }
    *previous = last;
}

int32_t fm1_percussion_decay(int32_t amplitude, int32_t decay_long, int32_t decay_short, int32_t parameter)
{
    return fm1_partial_decay(amplitude, decay_long, decay_short, parameter);
}

void fm1_percussion_render_drum(uint32_t *phase, const uint32_t *inc, const int32_t *amplitude, const int32_t *target,
                                int32_t *lp, int32_t f, int32_t noise_gain, int32_t harmonics_gain, int16_t *previous,
                                int16_t *buffer, uint32_t size)
{
    int16_t last = *previous;
    int32_t fade = 0, fade_increment = 65536 / (int32_t)size;
    while (size) {
        int32_t noise = fm1_braids_random_sample(), harmonics = 0, partial[DRUM_PARTIALS], i;
        int16_t sample;
        fade += fade_increment;
        {
            int32_t a = fm1_drum_noise_lp0(noise, lp[0], lp[1], lp[2], f), b = fm1_drum_noise_lp1(noise, lp[0], lp[1], lp[2], f);
            lp[2] = fm1_drum_noise_lp2(noise, lp[0], lp[1], lp[2], f);
            lp[0] = a; lp[1] = b;
        }
        for (i = 0; i < DRUM_PARTIALS; ++i) {
            partial[i] = fm1_drum_partial_contribution(phase[i], inc[i], amplitude[i], target[i], fade);
            phase[i] = fm1_drum_partial_phase(phase[i], inc[i], amplitude[i], target[i], fade);
            harmonics += partial[i];
        }
        sample = fm1_drum_mix(partial[0], partial[1], partial[3], harmonics, lp[2], noise_gain, harmonics_gain);
        *buffer++ = fm1_partials_mid(sample, last);
        *buffer++ = last = sample;
        size -= 2;
    }
    *previous = last;
}
