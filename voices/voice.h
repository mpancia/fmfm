/* SPDX-License-Identifier: GPL-3.0-only */
/* A synth voice: one Braids macro oscillator (all 48 shapes of Braids, MIT, Emilie Gillet; see
 * LICENSE-braids.txt) or, for shapes 48 on, the four-operator FM voice (voices/fm_glue.c, Firmware/Fm.lean),
 * behind a small C interface. Pitch is in 1/128 semitone (MIDI note n is n * 128), the two
 * timbre values run 0..32767. Render in blocks of at most BRAIDS_BLOCK samples. */
#pragma once
#include <stdint.h>

#ifdef __cplusplus
extern "C" {
#endif

#define BRAIDS_BLOCK 16u
#define BRAIDS_SHAPES 56u                         /* 48 Braids shapes, then the 8 FM shapes (voices/fm_glue.h) */
#define BRAIDS_VOICE_BYTES 17536u                 /* room for one voice; the C++ side checks it is enough */

void braids_voice_init(void *voice);
void braids_voice_set(void *voice, uint32_t shape, int32_t pitch, int32_t timbre, int32_t color);
void braids_voice_strike(void *voice);            /* start of a note: plucks, drums and bells need it */
void braids_voice_render(void *voice, int16_t *out, uint32_t count);   /* count <= BRAIDS_BLOCK */
const char *braids_shape_name(uint32_t shape);

#ifdef __cplusplus
}
#endif
