/* SPDX-License-Identifier: GPL-3.0-only */
#ifndef FM1_PERCUSSION_GLUE_H_
#define FM1_PERCUSSION_GLUE_H_
#include <stdint.h>
#ifdef __cplusplus
extern "C" {
#endif

/* A Braids `Svf`, as plain numbers: coefficient, damping, punch, low-pass and band-pass states, mode (0 LP, 1 BP,
 * 2 HP). */
typedef struct {
    int32_t f, damp, punch, lp, bp;
    uint8_t mode;
} fm1_svf_regs;

/* A Braids `Excitation`: decay, delay counter, pulse state, level. */
typedef struct {
    int32_t decay, counter, state, level;
} fm1_excite_regs;

int32_t fm1_svf_cutoff_of(int32_t frequency);
int32_t fm1_svf_damp_of(int32_t resonance);
void fm1_percussion_render_kick(fm1_excite_regs *pulse, fm1_svf_regs *svf, int32_t *lp_state, int32_t pitch,
                                int32_t coefficient, int16_t *buffer, uint32_t size);
void fm1_percussion_render_snare(fm1_excite_regs *pulse, fm1_svf_regs *svf, int32_t g1, int32_t g2, int16_t *buffer,
                                 uint32_t size);
void fm1_percussion_render_cymbal(uint32_t *phase, uint32_t *hat_phase, uint32_t *rng, const uint32_t *inc,
                                  fm1_svf_regs *svf, int32_t xfade, int16_t *buffer, uint32_t size);
void fm1_percussion_render_bell(uint32_t *phase, const uint32_t *inc, const int32_t *amplitude, int16_t *previous,
                                int16_t *buffer, uint32_t size);
void fm1_percussion_render_drum(uint32_t *phase, const uint32_t *inc, const int32_t *amplitude, const int32_t *target,
                                int32_t *lp, int32_t f, int32_t noise_gain, int32_t harmonics_gain, int16_t *previous,
                                int16_t *buffer, uint32_t size);

#ifdef __cplusplus
}
#endif
#endif
