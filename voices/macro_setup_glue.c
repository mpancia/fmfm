/* SPDX-License-Identifier: GPL-3.0-only */
/* The per-block setup of Braids' macro oscillator, with the arithmetic in Lean (Firmware/MacroSetup.lean),
 * included below as inline functions. voices/braids/macro_oscillator.cc calls these once per block. */
#include <lean/lean.h>
#include <stdint.h>

#undef LEAN_EXPORT
#define LEAN_EXPORT static inline
#include "MacroSetupApi.c"

int32_t fm1_macro_csaw_shift(int16_t parameter1) { return (int32_t)fm1_macro_setup_csaw_shift((uint16_t)parameter1); }

uint32_t fm1_macro_morph_zone(int16_t parameter0) { return fm1_macro_setup_morph_zone((uint16_t)parameter0); }

uint32_t fm1_macro_morph_balance(int16_t parameter0) { return fm1_macro_setup_morph_balance((uint16_t)parameter0); }

int32_t fm1_macro_morph_parameter(int16_t parameter0)
{
    return (int32_t)fm1_macro_setup_morph_parameter((uint16_t)parameter0);
}

int32_t fm1_macro_morph_cutoff(int16_t pitch, int16_t parameter1)
{
    return (int32_t)fm1_macro_setup_morph_cutoff((uint16_t)pitch, (uint16_t)parameter1);
}

int32_t fm1_macro_morph_fuzz(int16_t pitch, int16_t parameter1)
{
    return (int32_t)fm1_macro_setup_morph_fuzz((uint16_t)pitch, (uint16_t)parameter1);
}

int16_t fm1_macro_triple_pitch(int16_t pitch, int16_t parameter)
{
    return (int16_t)fm1_macro_setup_triple_pitch((uint16_t)pitch, (uint16_t)parameter);
}

int16_t fm1_macro_sub_pitch(int16_t pitch, int16_t parameter1)
{
    return (int16_t)fm1_macro_setup_sub_pitch((uint16_t)pitch, (uint16_t)parameter1);
}

int16_t fm1_macro_dual_sync_pitch(int16_t pitch, int16_t parameter0)
{
    return (int16_t)fm1_macro_setup_dual_sync_pitch((uint16_t)pitch, (uint16_t)parameter0);
}

int32_t fm1_macro_sine_parameter(int16_t pitch, int16_t parameter0)
{
    return (int32_t)fm1_macro_setup_sine_parameter((uint16_t)pitch, (uint16_t)parameter0);
}

int32_t fm1_macro_tri_parameter(int16_t pitch, int16_t parameter0)
{
    return (int32_t)fm1_macro_setup_tri_parameter((uint16_t)pitch, (uint16_t)parameter0);
}

int16_t fm1_macro_buzz_pitch(int16_t pitch, int16_t parameter1)
{
    return (int16_t)fm1_macro_setup_buzz_pitch((uint16_t)pitch, (uint16_t)parameter1);
}
