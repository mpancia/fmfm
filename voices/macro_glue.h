/* SPDX-License-Identifier: GPL-3.0-only */
#ifndef FM1_MACRO_GLUE_H_
#define FM1_MACRO_GLUE_H_
#include <stdint.h>
#ifdef __cplusplus
extern "C" {
#endif

void fm1_macro_render_csaw(int16_t *buffer, int32_t shift, uint32_t size);
void fm1_macro_render_morph(int16_t *buffer, const int16_t *other, uint32_t balance, int32_t *lp_state, int32_t f,
                            int32_t fuzz, uint32_t size);
void fm1_macro_render_saw_square(int16_t *buffer, const int16_t *square, int32_t previous_parameter,
                                 int32_t parameter, uint32_t size);
void fm1_macro_render_triple_add(int16_t *buffer, const int16_t *other, uint32_t size);
void fm1_macro_render_sub(int16_t *buffer, const int16_t *other, int32_t previous_parameter, int32_t parameter,
                          uint32_t size);
void fm1_macro_render_dual_sync(int16_t *buffer, const int16_t *other, int32_t previous_parameter,
                                int32_t parameter, uint32_t size);
void fm1_macro_render_sine_triangle(int16_t *buffer, const int16_t *other, int32_t previous_parameter,
                                    int32_t parameter, uint32_t size);
void fm1_macro_render_buzz(int16_t *buffer, const int16_t *other, uint32_t size);

#ifdef __cplusplus
}
#endif
#endif
