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

/* The per-block setup of the same engines, in vowels_setup_glue.c (Firmware/VowelsSetup.lean). */
void fm1_vowels_setup_vowel(int32_t parameter0, int32_t parameter1, uint32_t *increments, uint32_t *amplitudes);
int32_t fm1_vowels_setup_consonant(int32_t random, int32_t parameter1, uint32_t *increments, uint32_t *amplitudes);
int32_t fm1_vowels_setup_fof(int32_t parameter0, int32_t parameter1, int32_t *cutoffs);
uint32_t fm1_vowels_setup_question_dit_of(int32_t parameter);
int32_t fm1_vowels_setup_question_threshold_of(int32_t parameter);

#ifdef __cplusplus
}
#endif
#endif
