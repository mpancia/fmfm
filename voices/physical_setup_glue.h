/* SPDX-License-Identifier: GPL-3.0-only */
#ifndef FM1_PHYSICAL_SETUP_GLUE_H_
#define FM1_PHYSICAL_SETUP_GLUE_H_
#include <stdint.h>
#ifdef __cplusplus
extern "C" {
#endif
/* The per-block setup of the comb filter, plucked string, bowed string, blown pipe and flute
 * (Firmware/PhysicalSetup.lean): the numbers the C++ stores before the sample loop. `delay` is the pitch's delay
 * time in 16.16 samples (`DigitalOscillator::ComputeDelay`), `increment` the plucked string's doubled phase
 * step. */
int16_t fm1_physical_comb_pitch_of(int32_t previous, int32_t pitch, int32_t param0);
uint32_t fm1_physical_comb_delay_integral_of(uint32_t delay);
int32_t fm1_physical_comb_delay_fractional_of(uint32_t delay);
uint32_t fm1_physical_pluck_shift_of(uint32_t increment);
uint32_t fm1_physical_pluck_size_of(uint32_t shift);
uint32_t fm1_physical_pluck_mask_of(uint32_t shift);
uint32_t fm1_physical_pluck_initialization_of(uint32_t shift, int32_t param1);
uint32_t fm1_physical_pluck_update_probability_of(int32_t param0);
int32_t fm1_physical_pluck_loss_of(uint32_t increment, int32_t param0);
int32_t fm1_physical_bowed_bow_of(int32_t param0);
uint32_t fm1_physical_bowed_bridge_delay_of(uint32_t delay, int32_t param1);
uint32_t fm1_physical_bowed_neck_delay_of(uint32_t delay, int32_t param1);
uint32_t fm1_physical_bowed_excitation_clamp_of(uint32_t ptr);
uint32_t fm1_physical_blown_delay_of(uint32_t delay);
int32_t fm1_physical_blown_parameter_of(int32_t param0);
int32_t fm1_physical_blown_filter_coefficient_of(int32_t pitch, int32_t param1);
uint32_t fm1_physical_fluted_bore_delay_of(uint32_t delay, int32_t param1);
uint32_t fm1_physical_fluted_jet_delay_of(uint32_t delay, int32_t param1);
int32_t fm1_physical_fluted_breath_of(int32_t param0);
int32_t fm1_physical_fluted_filter_coefficient_of(int32_t pitch);
uint32_t fm1_physical_fluted_excitation_clamp_of(uint32_t ptr);
#ifdef __cplusplus
}
#endif
#endif
