/* SPDX-License-Identifier: GPL-3.0-only */
/* The reverb send (Clouds' reverb, Mutable Instruments, MIT): feed it the send bus, take the wet signal.
 * All values are Q15: 32768 is 1.0. The arithmetic of each sample is Lean (Firmware/Reverb.lean); the network and
 * the delay memory are fx/reverb_glue.c. */
#pragma once
#include <stdint.h>

#ifdef __cplusplus
extern "C" {
#endif

#define FM1_REVERB_SCALE_44K 353u       /* delay times scaled from Clouds' 32 kHz to 44.1 kHz (Q8) */
#define FM1_REVERB_BLOCK 256u           /* the most samples one fm1_reverb_block call takes */

/* clear the memory; lfo_phase_step is a half hertz, the second LFO runs at three fifths of it */
void fm1_reverb_init(uint32_t scale, uint32_t lfo_phase_step);
void fm1_reverb_clear(void);        /* forget the tail; not while the block function can run */
void fm1_reverb_tune(uint32_t time, uint32_t bright);        /* decay and brightness, each 0 to 100 */
void fm1_reverb_set(int32_t time_gain, int32_t lowpass, int32_t diffusion, int32_t input_gain);
void fm1_reverb_block(const int32_t *send, int32_t *wet_left, int32_t *wet_right, uint32_t count);

#ifdef __cplusplus
}
#endif
