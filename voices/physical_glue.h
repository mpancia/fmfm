/* SPDX-License-Identifier: GPL-3.0-only */
#ifndef FM1_PHYSICAL_GLUE_H_
#define FM1_PHYSICAL_GLUE_H_
#include <stdint.h>
#ifdef __cplusplus
extern "C" {
#endif

/* One plucked string, as plain numbers (Braids' PluckState and its delay line). */
typedef struct {
    int16_t *dl;
    uint32_t phase, phase_increment, shift, mask, size, write_ptr, initialization_ptr;
} fm1_pluck_voice;

/* The state of the bowed, blown and fluted pipes (Braids' PhysicalModellingState). */
typedef struct {
    uint32_t delay_ptr, excitation_ptr;
    int32_t lp, filter0, filter1;
    int16_t previous;
} fm1_pipe_state;

int32_t fm1_physical_comb_resonance(int32_t parameter);
void fm1_physical_render_comb(int16_t *dl, uint32_t *delay_ptr, uint32_t delay_integral, uint32_t delay_fractional,
                              int32_t resonance, int16_t *buffer, uint32_t size);
void fm1_physical_render_plucked(fm1_pluck_voice *voices, uint32_t num_voices, uint32_t update_probability,
                                 int32_t loss, int16_t *previous, int16_t *buffer, uint32_t size);
void fm1_physical_render_bowed(int8_t *bridge, int8_t *neck, fm1_pipe_state *state, uint32_t bridge_delay,
                               uint32_t neck_delay, int32_t bow, int16_t *buffer, uint32_t size);
void fm1_physical_render_blown(int16_t *bore, fm1_pipe_state *state, uint32_t bore_delay, int32_t parameter,
                               int32_t coefficient, int16_t *buffer, uint32_t size);
void fm1_physical_render_fluted(int8_t *bore, int8_t *jet, fm1_pipe_state *state, uint32_t bore_delay,
                                uint32_t jet_delay, int32_t intensity, int32_t coefficient, int16_t *buffer,
                                uint32_t size);

#ifdef __cplusplus
}
#endif
#endif
