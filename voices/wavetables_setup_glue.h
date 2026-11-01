/* SPDX-License-Identifier: GPL-3.0-only */
#ifndef FM1_WAVETABLES_SETUP_GLUE_H_
#define FM1_WAVETABLES_SETUP_GLUE_H_
#include <stdint.h>
#ifdef __cplusplus
extern "C" {
#endif

void fm1_wavetables_setup_table(int16_t param0, int16_t prev1, uint32_t *wave_a, uint32_t *wave_b,
                                uint32_t *balance);
void fm1_wavetables_setup_map(int16_t param0, int16_t param1, uint32_t *waves, uint32_t *xfade_x, uint32_t *xfade_y);
void fm1_wavetables_setup_line(int32_t *smoothed, int16_t prev0, int16_t param0, int16_t param1, uint32_t size,
                               uint32_t *wave_0, uint32_t *wave_1, uint32_t *wave_2, uint32_t *smooth_xfade,
                               uint32_t *rough_step, uint32_t *balance, uint32_t *mode, int16_t *held);
void fm1_wavetables_setup_paraphonic(int16_t pitch, uint32_t inc0, int16_t param0, int16_t param1, uint32_t *inc,
                                     uint32_t *wave_a, uint32_t *wave_b, uint32_t *xfade);

#ifdef __cplusplus
}
#endif
#endif
