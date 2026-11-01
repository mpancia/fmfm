/* SPDX-License-Identifier: GPL-3.0-only */
/* The per-block setup of Braids' analog oscillator, with the arithmetic in Lean (Firmware/AnalogSetup.lean),
 * included below as inline functions. voices/braids/analog_oscillator.cc calls these once per block. */
#include <lean/lean.h>
#include <stdint.h>

#undef LEAN_EXPORT
#define LEAN_EXPORT static inline
#include "AnalogSetupApi.c"

int16_t fm1_analog_clamped_pitch(int16_t pitch) { return (int16_t)fm1_analog_setup_clamped_pitch((uint16_t)pitch); }

uint32_t fm1_analog_square_pulse_width(int16_t parameter)
{
    return fm1_analog_setup_square_pulse_width((uint16_t)parameter);
}

uint32_t fm1_analog_variable_saw_pulse_width(int16_t parameter)
{
    return fm1_analog_setup_variable_saw_pulse_width((uint16_t)parameter);
}

uint32_t fm1_analog_buzz_zone(int16_t pitch, int16_t parameter)
{
    return fm1_analog_setup_buzz_zone((uint16_t)pitch, (uint16_t)parameter);
}

uint32_t fm1_analog_buzz_zone2(int16_t pitch, int16_t parameter)
{
    return fm1_analog_setup_buzz_zone2((uint16_t)pitch, (uint16_t)parameter);
}

uint32_t fm1_analog_buzz_crossfade(int16_t pitch, int16_t parameter)
{
    return fm1_analog_setup_buzz_crossfade((uint16_t)pitch, (uint16_t)parameter);
}
