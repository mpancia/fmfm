/* SPDX-License-Identifier: GPL-3.0-only */
/* The sample loops of the Braids noise engines, with the arithmetic of each sample in Lean
 * (Firmware/Noise.lean). This file owns the buffers, the state arrays and the calls for random numbers. The loops
 * follow `DigitalOscillator::Render*` in Braids (Emilie Gillet, MIT). */
#include <lean/lean.h>
#include <stddef.h>
#include <stdint.h>

#undef LEAN_EXPORT
#define LEAN_EXPORT static inline
#include "NoiseApi.c"

int16_t fm1_braids_random_sample(void);
uint32_t fm1_braids_random_word(void);

void fm1_noise_render_filtered(int32_t *lp_state, int32_t *bp_state, int32_t f, int32_t damp, int32_t lp_gain,
                               int32_t bp_gain, int32_t hp_gain, int32_t gain, int16_t *buffer, uint32_t size)
{
    int32_t lp = *lp_state, bp = *bp_state;
    while (size--) {
        int32_t in = fm1_braids_random_sample() >> 1;
#define ARGS in, f, damp, bp, lp, lp_gain, bp_gain, hp_gain, gain
        *buffer++ = fm1_filtered_noise_out(ARGS);
        {
            int32_t nl = fm1_filtered_noise_lp(ARGS);
            bp = fm1_filtered_noise_bp(ARGS);
            lp = nl;
        }
#undef ARGS
    }
    *lp_state = lp; *bp_state = bp;
}

/* `state` holds y11, y12, y21, y22 (Braids' filter_state[2][2]). */
void fm1_noise_render_twin_peaks(int32_t *state, int32_t s1, int32_t c1, int32_t s2, int32_t c2, int32_t q2,
                                 int32_t makeup, int16_t *buffer, uint32_t size)
{
    int32_t y11 = state[0], y12 = state[1], y21 = state[2], y22 = state[3];
    while (size) {
        int32_t in = fm1_braids_random_sample() >> 1;
#define ARGS in, s1, c1, s2, c2, q2, makeup, y11, y12, y21, y22
        int16_t out = fm1_twin_peaks_out(ARGS);
        int32_t n11 = fm1_twin_peaks_y11(ARGS), n12 = fm1_twin_peaks_y12(ARGS);
        int32_t n21 = fm1_twin_peaks_y21(ARGS), n22 = fm1_twin_peaks_y22(ARGS);
#undef ARGS
        y11 = n11; y12 = n12; y21 = n21; y22 = n22;
        *buffer++ = out;
        *buffer++ = out;
        size -= 2;
    }
    state[0] = y11; state[1] = y12; state[2] = y21; state[3] = y22;
}

void fm1_noise_render_clocked(uint32_t *phase, uint32_t inc, uint32_t *rng, uint32_t *cycle, uint32_t cycle_inc,
                              uint32_t seed, int16_t *held, uint32_t divider, const uint8_t *sync, int16_t *buffer,
                              uint32_t size)
{
    uint32_t p = *phase, r = *rng, c = *cycle;
    int16_t h = *held;
    while (size--) {
        uint8_t s = *sync++;
#define ARGS p, inc, r, c, cycle_inc, seed, h, divider, s
        *buffer++ = fm1_clocked_noise_out(ARGS);
        {
            uint32_t np = fm1_clocked_noise_phase(ARGS), nr = fm1_clocked_noise_rng(ARGS);
            uint32_t nc = fm1_clocked_noise_cycle(ARGS);
            h = fm1_clocked_noise_held(ARGS);
            p = np; r = nr; c = nc;
        }
#undef ARGS
    }
    *phase = p; *rng = r; *cycle = c; *held = h;
}

/* `grains` holds, per grain, phase, phase increment, envelope phase, envelope increment (Braids' Grain). */
void fm1_noise_render_cloud(uint32_t *grains, int16_t *buffer, uint32_t size)
{
    while (size--) {
        int32_t sum = 0;
        int i;
        for (i = 0; i < 4; ++i) {
            uint32_t *g = grains + 4 * i;
            sum += fm1_grain_contribution(g[0], g[1], g[2], g[3]);
            {
                uint32_t np = fm1_grain_phase(g[0], g[1], g[2], g[3]);
                g[2] = fm1_grain_envelope(g[0], g[1], g[2], g[3]);
                g[0] = np;
            }
        }
        *buffer++ = fm1_cloud_out(sum);
    }
}

/* `state` holds y11, y12, y21, y22, y31, y32; `scale` and `coefficient` one value per resonator. */
void fm1_noise_render_particle(uint16_t *amplitude, int32_t *state, int32_t *scale, int32_t *coefficient,
                               uint32_t density, int32_t pitch, int32_t spread, int16_t *buffer, uint32_t size)
{
    uint16_t amp = *amplitude;
    int32_t y11 = state[0], y12 = state[1], y21 = state[2], y22 = state[3], y31 = state[4], y32 = state[5];
    int32_t s1 = scale[0], s2 = scale[1], s3 = scale[2], c1 = coefficient[0], c2 = coefficient[1], c3 = coefficient[2];
    while (size) {
        uint32_t noise = fm1_braids_random_word();
        if ((noise & 0x7fffff) < density) {
            amp = 65535;
            c1 = fm1_particle_hit_c1(noise, pitch, spread); s1 = fm1_particle_hit_s1(noise, pitch, spread);
            c2 = fm1_particle_hit_c2(noise, pitch, spread); s2 = fm1_particle_hit_s2(noise, pitch, spread);
            c3 = fm1_particle_hit_c3(noise, pitch, spread); s3 = fm1_particle_hit_s3(noise, pitch, spread);
        }
        {
#define ARGS noise, amp, s1, c1, s2, c2, s3, c3, y11, y12, y21, y22, y31, y32
            int16_t out = fm1_particle_out(ARGS);
            int32_t n11 = fm1_particle_y11(ARGS), n12 = fm1_particle_y12(ARGS), n21 = fm1_particle_y21(ARGS);
            int32_t n22 = fm1_particle_y22(ARGS), n31 = fm1_particle_y31(ARGS), n32 = fm1_particle_y32(ARGS);
            amp = fm1_particle_amplitude(ARGS);
#undef ARGS
            y11 = n11; y12 = n12; y21 = n21; y22 = n22; y31 = n31; y32 = n32;
            *buffer++ = out;
            *buffer++ = out;
        }
        size -= 2;
    }
    *amplitude = amp;
    state[0] = y11; state[1] = y12; state[2] = y21; state[3] = y22; state[4] = y31; state[5] = y32;
    scale[0] = s1; scale[1] = s2; scale[2] = s3; coefficient[0] = c1; coefficient[1] = c2; coefficient[2] = c3;
}
