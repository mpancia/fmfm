/* SPDX-License-Identifier: GPL-3.0-only */
/* The 808-style drum voice (voices/drum_glue.c, arithmetic in Firmware/Drum.lean): its state and calls. */
#pragma once
#include <stdint.h>

#ifdef __cplusplus
extern "C" {
#endif

#define DRUM_SHAPES 10u                           /* BD, SD, CP, CH, OH, LT, MT, HT, CB, CY */

static const char *const DRUM_NAME[DRUM_SHAPES] = {
    "808 BD", "808 SD", "808 CP", "808 CH", "808 OH", "808 LT", "808 MT", "808 HT", "808 CB", "808 CY"};

typedef struct {
    uint32_t phase[6], inc[6];                    /* an oscillator's phase and its phase step a sample */
    uint32_t envelope[2];                         /* the body's envelope and the second part's (Q24) */
    uint32_t sweep;                               /* the swept increment of the kick's and toms' sine */
    uint32_t noise;                               /* the shift register, never reset: every hit's noise differs */
    uint32_t age;                                 /* samples since the strike, for the clap's bursts */
    int32_t lp[4];                                /* the one-pole states: two per band-pass */
    uint32_t shape, timbre, colour;
    uint32_t pending;                             /* a strike waiting for the block's settings */
} drum_voice_t;

void fm1_drum_init(drum_voice_t *v);
void fm1_drum_set(drum_voice_t *v, uint32_t shape, int32_t pitch, int32_t timbre, int32_t colour);
void fm1_drum_strike(drum_voice_t *v);
void fm1_drum_render(drum_voice_t *v, int16_t *out, uint32_t count);

#ifdef __cplusplus
}
#endif
