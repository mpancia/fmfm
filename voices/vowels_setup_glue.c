/* SPDX-License-Identifier: GPL-3.0-only */
/* The per-block setup of the Braids vowel, FOF vowel and question-mark engines, with the arithmetic in Lean
 * (Firmware/VowelsSetup.lean), included below as inline functions. `DigitalOscillator::Render*` in
 * voices/braids/digital_oscillator.cc calls these once per block and draws the random sample a consonant
 * needs; the loops are in vowels_glue.c. */
#include <lean/lean.h>
#include <stdint.h>

#undef LEAN_EXPORT
#define LEAN_EXPORT static inline
#include "VowelsSetupApi.c"

void fm1_vowels_setup_vowel(int32_t parameter0, int32_t parameter1, uint32_t *increments, uint32_t *amplitudes)
{
    uint32_t i;
    for (i = 0; i < 3; ++i) {
        increments[i] = fm1_vowels_setup_vowel_increment(parameter0, parameter1, i);
        amplitudes[i] = fm1_vowels_setup_vowel_amplitude(parameter0, i);
    }
}

int32_t fm1_vowels_setup_consonant(int32_t random, int32_t parameter1, uint32_t *increments, uint32_t *amplitudes)
{
    uint32_t i;
    for (i = 0; i < 3; ++i) {
        increments[i] = fm1_vowels_setup_consonant_increment(random, parameter1, i);
        amplitudes[i] = fm1_vowels_setup_consonant_amplitude(random, i);
    }
    return fm1_vowels_setup_consonant_noise(random);
}

int32_t fm1_vowels_setup_fof(int32_t parameter0, int32_t parameter1, int32_t *cutoffs)
{
    uint32_t i;
    for (i = 0; i < 5; ++i) cutoffs[i] = fm1_vowels_setup_fof_cutoff(parameter0, parameter1, i);
    return fm1_vowels_setup_fof_amplitude(parameter0, parameter1, 0);
}

uint32_t fm1_vowels_setup_question_dit_of(int32_t parameter)
{
    return fm1_vowels_setup_question_dit(parameter);
}

int32_t fm1_vowels_setup_question_threshold_of(int32_t parameter)
{
    return fm1_vowels_setup_question_threshold(parameter);
}
