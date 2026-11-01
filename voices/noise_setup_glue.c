/* SPDX-License-Identifier: GPL-3.0-only */
/* The per-block setup of the Braids noise engines, with the arithmetic in Lean (Firmware/NoiseSetup.lean),
 * included below as inline functions. voices/braids/digital_oscillator.cc calls these once per block; this file
 * draws the random numbers a grain restart needs, so the sequence stays Braids'. */
#include <lean/lean.h>
#include <stdint.h>

#undef LEAN_EXPORT
#define LEAN_EXPORT static inline
#include "NoiseSetupApi.c"

int16_t fm1_braids_random_sample(void);
uint32_t fm1_braids_random_word(void);

int16_t fm1_parameter_held(int16_t parameter, int16_t previous, int32_t window)
{
    return fm1_noise_setup_held((uint16_t)parameter, (uint16_t)previous, (uint32_t)window);
}

void fm1_noise_setup_filtered(int16_t pitch, int16_t param0, int16_t param1, int32_t *f, int32_t *damp,
                              int32_t *lp_gain, int32_t *bp_gain, int32_t *hp_gain, int32_t *gain)
{
    *f = fm1_noise_setup_cutoff((uint16_t)pitch);
    *damp = fm1_noise_setup_damp((uint16_t)param0);
    *lp_gain = fm1_noise_setup_lp_gain((uint16_t)param1);
    *bp_gain = fm1_noise_setup_bp_gain((uint16_t)param1);
    *hp_gain = fm1_noise_setup_hp_gain((uint16_t)param1);
    *gain = fm1_noise_setup_gain_correction((uint16_t)pitch, (uint16_t)param0);
}

void fm1_noise_setup_twin_peaks(int16_t pitch, int16_t param0, int16_t param1, int32_t *s1, int32_t *c1,
                                int32_t *s2, int32_t *c2, int32_t *q_squared, int32_t *makeup)
{
    *s1 = fm1_noise_setup_peak_s1((uint16_t)pitch);
    *c1 = fm1_noise_setup_peak_c1((uint16_t)pitch, (uint16_t)param0);
    *s2 = fm1_noise_setup_peak_s2((uint16_t)pitch, (uint16_t)param1);
    *c2 = fm1_noise_setup_peak_c2((uint16_t)pitch, (uint16_t)param0, (uint16_t)param1);
    *q_squared = fm1_noise_setup_peak_q_squared((uint16_t)param0);
    *makeup = fm1_noise_setup_peak_makeup((uint16_t)param0);
}

void fm1_noise_setup_clocked(uint32_t inc, int16_t prev0, int16_t prev1, uint32_t *clock_inc, uint32_t *cycle_inc,
                             uint32_t *divider)
{
    *clock_inc = fm1_noise_setup_clock_increment(inc);
    *cycle_inc = fm1_noise_setup_cycle_increment((uint16_t)prev0);
    *divider = fm1_noise_setup_quantizer_divider((uint16_t)prev1);
}

/* `grains` holds, per grain, phase, phase increment, envelope phase, envelope increment (Braids' Grain). A grain
 * whose envelope has ended draws a word; if it starts again it draws a sample for its detune. */
void fm1_noise_setup_cloud(uint32_t *grains, uint32_t inc, int16_t param0, int16_t param1)
{
    int i;
    for (i = 0; i < 4; ++i) {
        uint32_t *g = grains + 4 * i;
        uint32_t envelope = g[2], env_inc = g[3];
        if (!fm1_noise_setup_grain_done(envelope, env_inc))
            continue;
        {
            uint32_t word = fm1_braids_random_word();
            g[3] = fm1_noise_setup_grain_rate_start(envelope, env_inc, word, (uint16_t)param0);
            g[2] = fm1_noise_setup_grain_envelope_start(envelope, env_inc, word);
            if (fm1_noise_setup_grain_starts(word))
                g[1] = fm1_noise_setup_grain_increment(inc, (uint16_t)fm1_braids_random_sample(), (uint16_t)param1);
        }
    }
}

uint32_t fm1_noise_setup_particle(int16_t param0)
{
    return fm1_noise_setup_particle_density((uint16_t)param0);
}
