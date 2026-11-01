/* SPDX-License-Identifier: GPL-3.0-only */
/* The per-block setup of the Braids comb filter, plucked string, bowed string, blown pipe and flute, with the
 * arithmetic in Lean (Firmware/PhysicalSetup.lean), included below as inline functions.
 * `DigitalOscillator::Render*` in voices/braids/digital_oscillator.cc calls these once per block and stores the
 * results. */
#include <lean/lean.h>
#include <stdint.h>
#include "physical_setup_glue.h"

#undef LEAN_EXPORT
#define LEAN_EXPORT static inline
#include "PhysicalSetupApi.c"

int16_t fm1_physical_comb_pitch_of(int32_t previous, int32_t pitch, int32_t param0)
{
    return (int16_t)fm1_physical_setup_comb_pitch(previous, pitch, param0);
}
uint32_t fm1_physical_comb_delay_integral_of(uint32_t delay) { return fm1_physical_setup_comb_delay_integral(delay); }
int32_t fm1_physical_comb_delay_fractional_of(uint32_t delay)
{
    return fm1_physical_setup_comb_delay_fractional(delay);
}
uint32_t fm1_physical_pluck_shift_of(uint32_t increment) { return fm1_physical_setup_pluck_shift(increment); }
uint32_t fm1_physical_pluck_size_of(uint32_t shift) { return fm1_physical_setup_pluck_size(shift); }
uint32_t fm1_physical_pluck_mask_of(uint32_t shift) { return fm1_physical_setup_pluck_mask(shift); }
uint32_t fm1_physical_pluck_initialization_of(uint32_t shift, int32_t param1)
{
    return fm1_physical_setup_pluck_initialization(shift, param1);
}
uint32_t fm1_physical_pluck_update_probability_of(int32_t param0)
{
    return fm1_physical_setup_pluck_update_probability(param0);
}
int32_t fm1_physical_pluck_loss_of(uint32_t increment, int32_t param0)
{
    return fm1_physical_setup_pluck_loss(increment, param0);
}
int32_t fm1_physical_bowed_bow_of(int32_t param0) { return fm1_physical_setup_bowed_bow(param0); }
uint32_t fm1_physical_bowed_bridge_delay_of(uint32_t delay, int32_t param1)
{
    return fm1_physical_setup_bowed_bridge_delay(delay, param1);
}
uint32_t fm1_physical_bowed_neck_delay_of(uint32_t delay, int32_t param1)
{
    return fm1_physical_setup_bowed_neck_delay(delay, param1);
}
uint32_t fm1_physical_bowed_excitation_clamp_of(uint32_t ptr) { return fm1_physical_setup_bowed_excitation_clamp(ptr); }
uint32_t fm1_physical_blown_delay_of(uint32_t delay) { return fm1_physical_setup_blown_delay(delay); }
int32_t fm1_physical_blown_parameter_of(int32_t param0) { return fm1_physical_setup_blown_parameter(param0); }
int32_t fm1_physical_blown_filter_coefficient_of(int32_t pitch, int32_t param1)
{
    return fm1_physical_setup_blown_filter_coefficient(pitch, param1);
}
uint32_t fm1_physical_fluted_bore_delay_of(uint32_t delay, int32_t param1)
{
    return fm1_physical_setup_fluted_bore_delay(delay, param1);
}
uint32_t fm1_physical_fluted_jet_delay_of(uint32_t delay, int32_t param1)
{
    return fm1_physical_setup_fluted_jet_delay(delay, param1);
}
int32_t fm1_physical_fluted_breath_of(int32_t param0) { return fm1_physical_setup_fluted_breath(param0); }
int32_t fm1_physical_fluted_filter_coefficient_of(int32_t pitch)
{
    return fm1_physical_setup_fluted_filter_coefficient(pitch);
}
uint32_t fm1_physical_fluted_excitation_clamp_of(uint32_t ptr) { return fm1_physical_setup_fluted_excitation_clamp(ptr); }
