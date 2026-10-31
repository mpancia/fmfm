/* SPDX-License-Identifier: GPL-3.0-only */
/* The sample loops of the Braids vowel, FOF vowel and question-mark engines, with the arithmetic of each sample
 * in Lean (Firmware/Vowels.lean). This file owns the buffers, the per-formant state and the calls for random
 * numbers. The loops follow `DigitalOscillator::Render*` in Braids (Emilie Gillet, MIT). */
#include <lean/lean.h>
#include <stddef.h>
#include <stdint.h>

#undef LEAN_EXPORT
#define LEAN_EXPORT static inline
#include "VowelsApi.c"

int16_t fm1_braids_random_sample(void);

void fm1_vowels_render_vowel(uint32_t *phase, uint32_t inc, uint32_t *formant_phase, const uint32_t *formant_inc,
                             const uint32_t *amplitude, int32_t noise, int16_t *buffer, uint32_t size)
{
    uint32_t p = *phase, f0 = formant_phase[0], f1 = formant_phase[1], f2 = formant_phase[2];
    while (size--) {
        int32_t random = fm1_braids_random_sample();
#define ARGS p, inc, f0, f1, f2, formant_inc[0], formant_inc[1], formant_inc[2], amplitude[0], amplitude[1], \
             amplitude[2], noise, random
        *buffer++ = fm1_vowel_out(ARGS);
        {
            uint32_t np = fm1_vowel_phase(ARGS);
            uint32_t n0 = fm1_vowel_f0(ARGS);
            uint32_t n1 = fm1_vowel_f1(ARGS);
            f2 = fm1_vowel_f2(ARGS);
            p = np; f0 = n0; f1 = n1;
        }
#undef ARGS
    }
    *phase = p; formant_phase[0] = f0; formant_phase[1] = f1; formant_phase[2] = f2;
}

void fm1_vowels_render_fof(uint32_t *phase, int16_t *previous, int32_t *next_saw, uint32_t inc, int32_t *lp,
                           int32_t *bp, const int32_t *f, int32_t amplitude, int16_t *buffer, uint32_t size)
{
    uint32_t p = *phase;
    int32_t last = *previous, next = *next_saw;
    while (size) {
        int32_t in, sum = 0;
        int i;
        {
            uint32_t np = fm1_fof_saw_phase(p, inc, next);
            in = fm1_fof_saw_here(p, inc, next);
            next = fm1_fof_saw_next(p, inc, next);
            p = np;
        }
        for (i = 0; i < 5; ++i) {
            int32_t nl = fm1_fof_filter_lp(lp[i], bp[i], f[i], amplitude, in);
            int32_t nb = fm1_fof_filter_bp(lp[i], bp[i], f[i], amplitude, in);
            sum += fm1_fof_filter_contribution(lp[i], bp[i], f[i], amplitude, in);
            lp[i] = nl; bp[i] = nb;
        }
        *buffer++ = fm1_fof_out_mid(sum, last);
        *buffer++ = last = (int16_t)fm1_fof_out_out(sum, last);
        size -= 2;
    }
    *phase = p; *previous = last; *next_saw = next;
}

void fm1_vowels_render_question(uint32_t *phase, uint32_t inc, uint32_t *cycle, uint32_t *index, uint32_t *rng_on,
                                int32_t *seed_state, int16_t *length_state, uint32_t dit, int32_t threshold,
                                int32_t parameter, int16_t *buffer, uint32_t size)
{
    uint32_t p = *phase, c = *cycle, ix = *index;
    uint8_t on = *rng_on != 0;
    int32_t seed = *seed_state;
    int16_t length = *length_state;
    while (size--) {
        int32_t r1 = fm1_braids_random_sample(), r2 = fm1_braids_random_sample();
#define ARGS p, inc, c, ix, on, seed, length, dit, threshold, parameter, r1, r2
        *buffer++ = fm1_question_out(ARGS);
        {
            uint32_t np = fm1_question_phase(ARGS);
            uint32_t nc = fm1_question_cycle(ARGS);
            uint32_t nx = fm1_question_index(ARGS);
            uint8_t no = fm1_question_on(ARGS);
            int32_t ns = fm1_question_seed(ARGS);
            length = (int16_t)fm1_question_length(ARGS);
            p = np; c = nc; ix = nx; on = no; seed = ns;
        }
#undef ARGS
    }
    *phase = p; *cycle = c; *index = ix; *rng_on = on; *seed_state = seed; *length_state = length;
}
