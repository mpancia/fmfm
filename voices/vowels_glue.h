/* SPDX-License-Identifier: GPL-3.0-only */
#ifndef FM1_VOWELS_GLUE_H_
#define FM1_VOWELS_GLUE_H_
#include <stdint.h>
#ifdef __cplusplus
extern "C" {
#endif

void fm1_vowels_render_vowel(uint32_t *phase, uint32_t inc, uint32_t *formant_phase, const uint32_t *formant_inc,
                             const uint32_t *amplitude, int32_t noise, int16_t *buffer, uint32_t size);
void fm1_vowels_render_fof(uint32_t *phase, int16_t *previous, int32_t *next_saw, uint32_t inc, int32_t *lp,
                           int32_t *bp, const int32_t *f, int32_t amplitude, int16_t *buffer, uint32_t size);
void fm1_vowels_render_question(uint32_t *phase, uint32_t inc, uint32_t *cycle, uint32_t *index, uint32_t *rng_on,
                                int32_t *seed_state, int16_t *length_state, uint32_t dit, int32_t threshold,
                                int32_t parameter, int16_t *buffer, uint32_t size);

#ifdef __cplusplus
}
#endif
#endif
