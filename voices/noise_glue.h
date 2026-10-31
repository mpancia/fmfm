/* SPDX-License-Identifier: GPL-3.0-only */
#ifndef FM1_NOISE_GLUE_H_
#define FM1_NOISE_GLUE_H_
#include <stdint.h>
#ifdef __cplusplus
extern "C" {
#endif

void fm1_noise_render_filtered(int32_t *lp_state, int32_t *bp_state, int32_t f, int32_t damp, int32_t lp_gain,
                               int32_t bp_gain, int32_t hp_gain, int32_t gain, int16_t *buffer, uint32_t size);
void fm1_noise_render_twin_peaks(int32_t *state, int32_t s1, int32_t c1, int32_t s2, int32_t c2, int32_t q2,
                                 int32_t makeup, int16_t *buffer, uint32_t size);
void fm1_noise_render_clocked(uint32_t *phase, uint32_t inc, uint32_t *rng, uint32_t *cycle, uint32_t cycle_inc,
                              uint32_t seed, int16_t *held, uint32_t divider, const uint8_t *sync, int16_t *buffer,
                              uint32_t size);
void fm1_noise_render_cloud(uint32_t *grains, int16_t *buffer, uint32_t size);
void fm1_noise_render_particle(uint16_t *amplitude, int32_t *state, int32_t *scale, int32_t *coefficient,
                               uint32_t density, int32_t pitch, int32_t spread, int16_t *buffer, uint32_t size);

#ifdef __cplusplus
}
#endif
#endif
