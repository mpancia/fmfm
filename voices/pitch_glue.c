/* SPDX-License-Identifier: GPL-3.0-only */
/* Braids' pitch to phase step, with the arithmetic in Lean (Firmware/Pitch.lean), included below as inline
 * functions. Both oscillators (voices/braids/analog_oscillator.cc, digital_oscillator.cc) call this once per block. */
#include <lean/lean.h>
#include <stdint.h>

#undef LEAN_EXPORT
#define LEAN_EXPORT static inline
#include "PitchApi.c"

uint32_t fm1_pitch_increment_of(int16_t pitch)
{
    return fm1_pitch_phase_increment((uint16_t)pitch);
}
