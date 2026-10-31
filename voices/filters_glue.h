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

#ifdef __cplusplus
}
#endif
#endif
