/* SPDX-License-Identifier: GPL-3.0-only */
#ifndef FM1_NOISE_SETUP_GLUE_H_
#define FM1_NOISE_SETUP_GLUE_H_
#include <stdint.h>
#ifdef __cplusplus
extern "C" {
#endif

int16_t fm1_parameter_held(int16_t parameter, int16_t previous, int32_t window);
void fm1_noise_setup_filtered(int16_t pitch, int16_t param0, int16_t param1, int32_t *f, int32_t *damp,
                              int32_t *lp_gain, int32_t *bp_gain, int32_t *hp_gain, int32_t *gain);
void fm1_noise_setup_twin_peaks(int16_t pitch, int16_t param0, int16_t param1, int32_t *s1, int32_t *c1,
                                int32_t *s2, int32_t *c2, int32_t *q_squared, int32_t *makeup);
void fm1_noise_setup_clocked(uint32_t inc, int16_t prev0, int16_t prev1, uint32_t *clock_inc, uint32_t *cycle_inc,
                             uint32_t *divider);
void fm1_noise_setup_cloud(uint32_t *grains, uint32_t inc, int16_t param0, int16_t param1);
uint32_t fm1_noise_setup_particle(int16_t param0);

#ifdef __cplusplus
}
#endif
#endif
