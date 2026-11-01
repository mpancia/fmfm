/* SPDX-License-Identifier: GPL-3.0-only */
#ifndef FM1_FILTERS_GLUE_H_
#define FM1_FILTERS_GLUE_H_
#include <stdint.h>
#ifdef __cplusplus
extern "C" {
#endif

void fm1_filters_render_swarm(uint32_t *phase, uint32_t *saws, const uint32_t *inc, int32_t f, int32_t damp,
                              int32_t *bp_state, int32_t *lp_state, const uint8_t *sync, int16_t *buffer, uint32_t size);
void fm1_filters_render_digital_filter(uint32_t *phase, uint32_t inc, uint32_t *mod_phase, uint32_t *mod_inc,
                                       uint32_t mod_inc_step, uint32_t *square_phase, int32_t *integrator,
                                       uint8_t *polarity, uint8_t filter_type, int32_t parameter,
                                       const uint8_t *sync, int16_t *buffer, uint32_t size);
void fm1_filters_render_vosim(uint32_t *phase, uint32_t inc, uint32_t *formants, const uint32_t *formant_inc,
                              const uint8_t *sync, int16_t *buffer, uint32_t size);
void fm1_filters_render_harmonics(uint32_t *phase, int16_t *previous, uint32_t inc, int32_t *amplitude,
                                  const int32_t *target, const uint8_t *sync, int16_t *buffer, uint32_t size);

/* The per-block setup of the same engines, in filters_setup_glue.c (Firmware/FiltersSetup.lean). */
void fm1_filters_setup_swarm(int32_t pitch, int32_t detune, int32_t cutoff, uint32_t *increments, int32_t *f);
uint32_t fm1_filters_setup_filter_step(int32_t pitch, int32_t parameter, uint32_t current, uint32_t size);
uint32_t fm1_filters_setup_vosim(int32_t parameter);
void fm1_filters_setup_harmonics(int32_t parameter0, int32_t parameter1, uint32_t inc, int32_t *target);

#ifdef __cplusplus
}
#endif
#endif
