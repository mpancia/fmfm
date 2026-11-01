/* SPDX-License-Identifier: GPL-3.0-only */
/* The voice's doorway into Braids, with the arithmetic in Lean (Firmware/VoiceSetup.lean), included below as
 * inline functions. voices/voice.cc calls these once per block. */
#include <lean/lean.h>
#include <stdint.h>

#undef LEAN_EXPORT
#define LEAN_EXPORT static inline
#include "VoiceSetupApi.c"

uint32_t fm1_voice_shape(uint32_t shape) { return fm1_voice_setup_shape(shape); }

int16_t fm1_voice_pitch(int32_t pitch) { return (int16_t)fm1_voice_setup_pitch((uint32_t)pitch); }

int16_t fm1_voice_parameter(int32_t value) { return (int16_t)fm1_voice_setup_parameter((uint32_t)value); }
