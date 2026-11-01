/* SPDX-License-Identifier: GPL-3.0-only */
#ifndef FM1_PERCUSSION_SETUP_GLUE_H_
#define FM1_PERCUSSION_SETUP_GLUE_H_
#include <stdint.h>
#ifdef __cplusplus
extern "C" {
#endif
/* The per-block setup of the kick, snare, cymbal, struck bell and struck drum (Firmware/PercussionSetup.lean):
 * the numbers the C++ stores before the sample loop. `i` is a partial (bell 0 to 10, drum 0 to 5) or a hat
 * step (0 to 6). */
int32_t fm1_percussion_bell_amplitude_of(uint32_t i);
uint32_t fm1_percussion_bell_increment_of(int32_t pitch, int32_t param1, uint32_t i);
int32_t fm1_percussion_bell_decayed_of(int32_t amplitude, int32_t param0, uint32_t i);
int32_t fm1_percussion_drum_amplitude_of(uint32_t i);
uint32_t fm1_percussion_drum_increment_of(int32_t pitch, uint32_t i);
int32_t fm1_percussion_drum_decayed_of(int32_t amplitude, int32_t param0, uint32_t i);
int32_t fm1_percussion_drum_filter_of(int32_t pitch, int32_t param1);
int32_t fm1_percussion_drum_harmonics_gain_of(int32_t param1);
int32_t fm1_percussion_drum_noise_gain_of(int32_t param1);
int32_t fm1_percussion_kick_resonance_of(int32_t param0);
int32_t fm1_percussion_kick_lp_coefficient_of(int32_t param1);
int32_t fm1_percussion_snare_resonance_of(int32_t base, int32_t pitch, int32_t param1);
int32_t fm1_percussion_snare_pulse_decay_of(int32_t pitch, int32_t param1);
int32_t fm1_percussion_snare_snappy_of(int32_t param1);
int32_t fm1_percussion_snare_frequency_of(int32_t pitch, int32_t semitones);
int32_t fm1_percussion_snare_gain1_of(int32_t param0);
int32_t fm1_percussion_snare_gain2_of(int32_t param0);
uint32_t fm1_percussion_cymbal_increment_of(int32_t pitch, uint32_t i);
int32_t fm1_percussion_cymbal_frequency_of(int32_t param0);
#ifdef __cplusplus
}
#endif
#endif
