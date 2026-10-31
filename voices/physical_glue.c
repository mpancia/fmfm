/* SPDX-License-Identifier: GPL-3.0-only */
/* The sample loops of the Braids comb filter, plucked string, bowed string, blown pipe and flute, with the
 * arithmetic of each sample in Lean (Firmware/Physical.lean). This file owns the delay lines: every load, store
 * and pointer wrap is here, the values go to Lean as numbers. The lines are powers of two long, so the wraps are
 * masks. The loops follow `DigitalOscillator::Render*` in Braids (Emilie Gillet, MIT). */
#include <lean/lean.h>
#include <stddef.h>
#include <stdint.h>
#include "physical_glue.h"

#undef LEAN_EXPORT
#define LEAN_EXPORT static inline
#include "PhysicalApi.c"

int16_t fm1_braids_random_sample(void);
uint32_t fm1_braids_random_word(void);

#define COMB_LENGTH 8192u
#define BRIDGE_LENGTH 1024u
#define NECK_LENGTH 4096u
#define BORE_LENGTH 2048u
#define JET_LENGTH 1024u
#define FLUTE_BORE_LENGTH 4096u

int32_t fm1_physical_comb_resonance(int32_t parameter) { return fm1_comb_resonance(parameter); }

void fm1_physical_render_comb(int16_t *dl, uint32_t *delay_ptr, uint32_t delay_integral, uint32_t delay_fractional,
                              int32_t resonance, int16_t *buffer, uint32_t size)
{
    uint32_t ptr = *delay_ptr;
    while (size--) {
        int32_t in = *buffer;
        uint32_t offset = ptr + 2 * COMB_LENGTH - delay_integral;
        int32_t a = dl[offset & (COMB_LENGTH - 1)], b = dl[(offset - 1) & (COMB_LENGTH - 1)];
        dl[ptr] = fm1_comb_feedback(in, a, b, delay_fractional, resonance);
        *buffer++ = fm1_comb_out(in, a, b, delay_fractional, resonance);
        ptr = (ptr + 1) & (COMB_LENGTH - 1);
    }
    *delay_ptr = ptr;
}

void fm1_physical_render_plucked(fm1_pluck_voice *voices, uint32_t num_voices, uint32_t update_probability,
                                 int32_t loss, int16_t *previous, int16_t *buffer, uint32_t size)
{
    int16_t last = *previous;
    while (size) {
        int32_t sum = 0;
        uint32_t i;
        for (i = 0; i < num_voices; ++i) {
            fm1_pluck_voice *p = &voices[i];
            int16_t *dl = p->dl;
            if (p->initialization_ptr) {
                int16_t fill;
                --p->initialization_ptr;
                fill = fm1_pluck_fill(dl[p->initialization_ptr], fm1_braids_random_sample());
                dl[p->initialization_ptr] = fill;
                sum += fill;
            } else {
                uint32_t read_ptr, write_ptr, phase;
                p->phase += p->phase_increment;
                read_ptr = ((p->phase >> (22 + p->shift)) + 2) & p->mask;
                write_ptr = p->write_ptr;
                while (write_ptr != read_ptr) {
                    uint32_t next = (write_ptr + 1) & p->mask;
                    int32_t a = dl[write_ptr], b = dl[next];
                    if (fm1_pluck_updates(fm1_braids_random_word(), update_probability))
                        dl[write_ptr] = fm1_pluck_average(a, b, loss);
                    if (write_ptr == 0) dl[p->size] = dl[0];
                    write_ptr = next;
                }
                p->write_ptr = write_ptr;
                phase = p->phase >> p->shift;
                sum += fm1_pluck_read(dl[phase >> 22], dl[(phase >> 22) + 1], phase);
            }
        }
        *buffer++ = fm1_physical_mid(sum, last);
        *buffer++ = last = (int16_t)fm1_physical_out(sum);
        size -= 2;
    }
    *previous = last;
}

void fm1_physical_render_bowed(int8_t *bridge, int8_t *neck, fm1_pipe_state *state, uint32_t bridge_delay,
                               uint32_t neck_delay, int32_t bow, int16_t *buffer, uint32_t size)
{
    uint32_t ptr = state->delay_ptr, excitation = state->excitation_ptr;
    uint32_t bridge_integral = bridge_delay >> 16, bridge_fraction = bridge_delay & 0xffff;
    uint32_t neck_integral = neck_delay >> 16, neck_fraction = neck_delay & 0xffff;
    int32_t lp = state->lp, y0 = state->filter0, y1 = state->filter1;
    int16_t last = state->previous;
    while (size) {
        uint32_t bp = ptr + 2 * BRIDGE_LENGTH - bridge_integral, np = ptr + 2 * NECK_LENGTH - neck_integral;
        int32_t ba = bridge[bp & (BRIDGE_LENGTH - 1)], bb = bridge[(bp - 1) & (BRIDGE_LENGTH - 1)];
        int32_t na = neck[np & (NECK_LENGTH - 1)], nb = neck[(np - 1) & (NECK_LENGTH - 1)];
#define ARGS ba, bb, na, nb, bridge_fraction, neck_fraction, lp, excitation, bow, y0, y1
        int16_t out = fm1_bowed_out(ARGS);
        int32_t nlp = fm1_bowed_lp(ARGS), temp = fm1_bowed_biquad(ARGS);
        neck[ptr & (NECK_LENGTH - 1)] = (int8_t)fm1_bowed_neck(ARGS);
        bridge[ptr & (BRIDGE_LENGTH - 1)] = (int8_t)fm1_bowed_bridge(ARGS);
#undef ARGS
        lp = nlp; y1 = y0; y0 = temp;
        ++ptr;
        *buffer++ = fm1_physical_mid(out, last);
        *buffer++ = last = out;
        ++excitation;
        size -= 2;
    }
    state->delay_ptr = ptr; state->excitation_ptr = excitation; state->lp = lp;
    state->filter0 = y0; state->filter1 = y1; state->previous = last;
}

void fm1_physical_render_blown(int16_t *bore, fm1_pipe_state *state, uint32_t bore_delay, int32_t parameter,
                               int32_t coefficient, int16_t *buffer, uint32_t size)
{
    uint32_t ptr = state->delay_ptr, integral = bore_delay >> 16, fraction = bore_delay & 0xffff;
    int32_t lp = state->lp, filter = (int16_t)state->filter0;
    while (size--) {
        int32_t noise = fm1_braids_random_sample();
        uint32_t rp = ptr + 2 * BORE_LENGTH - integral;
        int32_t a = bore[rp & (BORE_LENGTH - 1)], b = bore[(rp - 1) & (BORE_LENGTH - 1)];
#define ARGS noise, a, b, fraction, lp, parameter, filter, coefficient
        bore[ptr & (BORE_LENGTH - 1)] = fm1_blown_bore(ARGS);
        *buffer++ = (int16_t)fm1_blown_filter(ARGS);
        {
            int32_t nlp = fm1_blown_lp(ARGS);
            filter = (int16_t)fm1_blown_filter(ARGS);
            lp = nlp;
        }
#undef ARGS
        ++ptr;
    }
    state->delay_ptr = ptr; state->lp = lp; state->filter0 = filter;
}

void fm1_physical_render_fluted(int8_t *bore, int8_t *jet, fm1_pipe_state *state, uint32_t bore_delay,
                                uint32_t jet_delay, int32_t intensity, int32_t coefficient, int16_t *buffer,
                                uint32_t size)
{
    uint32_t ptr = state->delay_ptr, excitation = state->excitation_ptr;
    uint32_t bore_integral = bore_delay >> 16, bore_fraction = bore_delay & 0xffff;
    uint32_t jet_integral = jet_delay >> 16, jet_fraction = jet_delay & 0xffff;
    int32_t lp = state->lp, dcx = state->filter0, dcy = state->filter1;
    while (size--) {
        int32_t noise = fm1_braids_random_sample();
        uint32_t bp = ptr + 2 * FLUTE_BORE_LENGTH - bore_integral, jp = ptr + 2 * JET_LENGTH - jet_integral;
        int32_t ba = bore[bp & (FLUTE_BORE_LENGTH - 1)], bb = bore[(bp - 1) & (FLUTE_BORE_LENGTH - 1)];
        int32_t ja = jet[jp & (JET_LENGTH - 1)], jb = jet[(jp - 1) & (JET_LENGTH - 1)];
#define ARGS ba, bb, ja, jb, bore_fraction, jet_fraction, excitation, noise, intensity, coefficient, lp, dcx, dcy
        *buffer++ = fm1_fluted_out(ARGS);
        jet[ptr & (JET_LENGTH - 1)] = (int8_t)fm1_fluted_jet(ARGS);
        bore[ptr & (FLUTE_BORE_LENGTH - 1)] = (int8_t)fm1_fluted_bore(ARGS);
        {
            int32_t nlp = fm1_fluted_lp(ARGS), nx = fm1_fluted_dcx(ARGS);
            dcy = fm1_fluted_dcy(ARGS);
            lp = nlp; dcx = nx;
        }
#undef ARGS
        ++ptr;
        if (size & 3) ++excitation;
    }
    state->delay_ptr = ptr; state->excitation_ptr = excitation; state->lp = lp;
    state->filter0 = dcx; state->filter1 = dcy;
}
