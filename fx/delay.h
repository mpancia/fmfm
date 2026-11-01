/* SPDX-License-Identifier: GPL-3.0-only */
/* The delay send: a tempo-synced echo on the send bus, fed back through a low-pass. Values are Q15: 32768 is
 * 1.0. The arithmetic of each sample is Lean (Firmware/Delay.lean); the line is fx/delay_glue.c. */
#pragma once
#include <stdint.h>

#ifdef __cplusplus
extern "C" {
#endif

#define FM1_DELAY_TIMES 8u              /* TIME settings 0 to 7: 1/32 to 1/4 (Delay.numerator, Delay.denominator) */

void fm1_delay_clear(void);                                        /* forget the echoes; not while the block runs */
void fm1_delay_tune(uint32_t time, uint32_t bpm, uint32_t rate, uint32_t feedback, uint32_t tone);  /* settings 0..100 */
void fm1_delay_block(const int32_t *send, int32_t *wet, uint32_t count);

#ifdef __cplusplus
}
#endif
