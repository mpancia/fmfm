/* SPDX-License-Identifier: GPL-3.0-only */
/* The per-block setup of Braids' FM, ring modulator, toy and digital modulation engines and its delay-line
 * length, with the arithmetic in Lean (Firmware/DigitalSetup.lean), included below as inline functions.
 * voices/braids/digital_oscillator.cc calls these once per block. */
#include <lean/lean.h>
#include <stdint.h>

#undef LEAN_EXPORT
#define LEAN_EXPORT static inline
#include "DigitalSetupApi.c"

int16_t fm1_digital_fm_quantized_parameter(int16_t parameter)
{
    return (int16_t)fm1_digital_setup_fm_quantized_parameter((uint16_t)parameter);
}

uint32_t fm1_digital_fm_modulator_increment(int16_t pitch, int16_t parameter)
{
    return fm1_digital_setup_fm_modulator_increment((uint16_t)pitch, (uint16_t)parameter);
}

int32_t fm1_digital_feedback_attenuation(int16_t pitch, int16_t parameter)
{
    return (int32_t)fm1_digital_setup_feedback_attenuation((uint16_t)pitch, (uint16_t)parameter);
}

uint32_t fm1_digital_ring_increment(int16_t pitch, int16_t parameter)
{
    return fm1_digital_setup_ring_increment((uint16_t)pitch, (uint16_t)parameter);
}

uint32_t fm1_digital_toy_increment(uint32_t increment)
{
    return fm1_digital_setup_toy_increment(increment);
}

uint16_t fm1_digital_toy_decimation(int16_t parameter)
{
    return fm1_digital_setup_toy_decimation((uint16_t)parameter);
}

uint8_t fm1_digital_toy_bits(int16_t parameter)
{
    return fm1_digital_setup_toy_bits((uint16_t)parameter);
}

uint32_t fm1_digital_modulation_symbol_increment(int16_t pitch, int16_t parameter)
{
    return fm1_digital_setup_modulation_symbol_increment((uint16_t)pitch, (uint16_t)parameter);
}

uint32_t fm1_digital_delay_of(int16_t pitch)
{
    return fm1_digital_setup_delay((uint16_t)pitch);
}
