/* SPDX-License-Identifier: GPL-3.0-only */
/* The per-block setup of the Braids saw swarm, digital filter, vosim and harmonics engines, with the arithmetic in
 * Lean (Firmware/FiltersSetup.lean), included below as inline functions. `DigitalOscillator::Render*` in
 * voices/braids/digital_oscillator.cc calls these once per block; the loops are in filters_glue.c. */
#include <lean/lean.h>
#include <stdint.h>

#undef LEAN_EXPORT
#define LEAN_EXPORT static inline
#include "FiltersSetupApi.c"

void fm1_filters_setup_swarm(int32_t pitch, int32_t detune, int32_t cutoff, uint32_t *increments, int32_t *f)
{
    int32_t i;
    for (i = 0; i < 7; ++i) increments[i] = fm1_filters_setup_swarm_increment(pitch, detune, i);
    *f = fm1_filters_setup_swarm_cutoff(pitch, cutoff);
}

uint32_t fm1_filters_setup_filter_step(int32_t pitch, int32_t parameter, uint32_t current, uint32_t size)
{
    return fm1_filters_setup_filter_increment_step(current, fm1_filters_setup_filter_increment(pitch, parameter),
                                                   size);
}

uint32_t fm1_filters_setup_vosim(int32_t parameter)
{
    return fm1_filters_setup_vosim_increment(parameter);
}

void fm1_filters_setup_harmonics(int32_t parameter0, int32_t parameter1, uint32_t inc, int32_t *target)
{
    int32_t attenuation = fm1_filters_setup_harmonics_attenuation(parameter0, parameter1);
    int32_t i;
    for (i = 0; i < 12; ++i) {
        target[i] = fm1_filters_setup_harmonics_target(parameter0, parameter1, inc, attenuation, i);
    }
}
