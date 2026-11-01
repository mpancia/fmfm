/* SPDX-License-Identifier: GPL-3.0-only */
/* The per-block setup of the Braids kick, snare, cymbal, struck bell and struck drum, with the arithmetic in Lean
 * (Firmware/PercussionSetup.lean), included below as inline functions. `DigitalOscillator::Render*` in
 * voices/braids/digital_oscillator.cc calls these once per block and stores the results. */
#include <lean/lean.h>
#include <stdint.h>
#include "percussion_setup_glue.h"

#undef LEAN_EXPORT
#define LEAN_EXPORT static inline
#include "PercussionSetupApi.c"

int32_t fm1_percussion_bell_amplitude_of(uint32_t i) { return fm1_percussion_setup_bell_amplitude(i); }
uint32_t fm1_percussion_bell_increment_of(int32_t pitch, int32_t param1, uint32_t i)
{
    return fm1_percussion_setup_bell_increment(pitch, param1, i);
}
int32_t fm1_percussion_bell_decayed_of(int32_t amplitude, int32_t param0, uint32_t i)
{
    return fm1_percussion_setup_bell_decayed(amplitude, param0, i);
}
int32_t fm1_percussion_drum_amplitude_of(uint32_t i) { return fm1_percussion_setup_drum_amplitude(i); }
uint32_t fm1_percussion_drum_increment_of(int32_t pitch, uint32_t i)
{
    return fm1_percussion_setup_drum_increment(pitch, i);
}
int32_t fm1_percussion_drum_decayed_of(int32_t amplitude, int32_t param0, uint32_t i)
{
    return fm1_percussion_setup_drum_decayed(amplitude, param0, i);
}
int32_t fm1_percussion_drum_filter_of(int32_t pitch, int32_t param1)
{
    return fm1_percussion_setup_drum_filter(pitch, param1);
}
int32_t fm1_percussion_drum_harmonics_gain_of(int32_t param1)
{
    return fm1_percussion_setup_drum_harmonics_gain(param1);
}
int32_t fm1_percussion_drum_noise_gain_of(int32_t param1) { return fm1_percussion_setup_drum_noise_gain(param1); }
int32_t fm1_percussion_kick_resonance_of(int32_t param0) { return fm1_percussion_setup_kick_resonance(param0); }
int32_t fm1_percussion_kick_lp_coefficient_of(int32_t param1)
{
    return fm1_percussion_setup_kick_lp_coefficient(param1);
}
int32_t fm1_percussion_snare_resonance_of(int32_t base, int32_t pitch, int32_t param1)
{
    return fm1_percussion_setup_snare_resonance(base, pitch, param1);
}
int32_t fm1_percussion_snare_pulse_decay_of(int32_t pitch, int32_t param1)
{
    return fm1_percussion_setup_snare_pulse_decay(pitch, param1);
}
int32_t fm1_percussion_snare_snappy_of(int32_t param1) { return fm1_percussion_setup_snare_snappy(param1); }
int32_t fm1_percussion_snare_frequency_of(int32_t pitch, int32_t semitones)
{
    return fm1_percussion_setup_snare_frequency(pitch, semitones);
}
int32_t fm1_percussion_snare_gain1_of(int32_t param0) { return fm1_percussion_setup_snare_gain1(param0); }
int32_t fm1_percussion_snare_gain2_of(int32_t param0) { return fm1_percussion_setup_snare_gain2(param0); }
uint32_t fm1_percussion_cymbal_increment_of(int32_t pitch, uint32_t i)
{
    return fm1_percussion_setup_cymbal_increment(pitch, i);
}
int32_t fm1_percussion_cymbal_frequency_of(int32_t param0) { return fm1_percussion_setup_cymbal_frequency(param0); }
