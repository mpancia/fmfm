/* SPDX-License-Identifier: GPL-3.0-only */
#ifndef FM1_WAVETABLES_GLUE_H_
#define FM1_WAVETABLES_GLUE_H_
#include <stdint.h>
#ifdef __cplusplus
extern "C" {
#endif

void fm1_wavetables_render_table(uint32_t *phase, uint32_t inc, uint32_t wave_a, uint32_t wave_b, uint32_t balance,
                                 const uint8_t *sync, int16_t *buffer, uint32_t size);
void fm1_wavetables_render_map(uint32_t *phase, uint32_t inc, const uint32_t *waves, uint32_t xfade_x,
                               uint32_t xfade_y, const uint8_t *sync, int16_t *buffer, uint32_t size);
void fm1_wavetables_render_line(uint32_t *phase, uint32_t inc, uint32_t wave_0, uint32_t wave_1, uint32_t wave_2,
                                uint32_t smooth_xfade, uint32_t rough_step, uint32_t balance, uint32_t mode,
                                const uint8_t *sync, int16_t *buffer, uint32_t size);
void fm1_wavetables_render_paraphonic(uint32_t *phases, const uint32_t *inc, uint32_t wave_a, uint32_t wave_b,
                                      uint32_t balance, int16_t *buffer, uint32_t size);

#ifdef __cplusplus
}
#endif
#endif
