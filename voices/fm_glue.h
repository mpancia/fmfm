/* SPDX-License-Identifier: GPL-3.0-only */
/* The four-operator FM voice (voices/fm_glue.c, arithmetic in Firmware/Fm.lean): its state and calls. */
#pragma once
#include <stdint.h>

#ifdef __cplusplus
extern "C" {
#endif

#define FM_SHAPES 8u                              /* shapes 48 to 55: FM PIANO, BELL, BASS, BRASS, GLASS, MALLET, ORGAN, CLANG */

typedef struct {
    uint32_t phase[4], inc[4], envelope[4];       /* an operator's phase, phase step a sample, envelope (Q24) */
    int32_t out[4];                               /* an operator's last output (Q15): the modulators of the next */
    uint32_t shape, timbre, colour;
} fm_voice_t;

void fm1_fm_init(fm_voice_t *v);
void fm1_fm_set(fm_voice_t *v, uint32_t shape, int32_t pitch, int32_t timbre, int32_t colour);
void fm1_fm_strike(fm_voice_t *v);
void fm1_fm_render(fm_voice_t *v, int16_t *out, uint32_t count);

#ifdef __cplusplus
}
#endif
