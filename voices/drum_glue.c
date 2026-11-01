/* SPDX-License-Identifier: GPL-3.0-only */
/* The 808-style drum voice (shapes 56 on): the state and the sample loop are here, the arithmetic of every
 * sample and the shapes' tables are Lean (Firmware/Drum.lean), included below as inline functions. Each
 * shape family has its own loop with the state in registers; the chains here are the ones
 * Proofs/Drum.lean bounds (drum_output_never_wraps), stage for stage. voices/voice.cc hands the firmware's
 * calls here for a drum shape. */
#include <lean/lean.h>
#include <stdint.h>

#undef LEAN_EXPORT
#define LEAN_EXPORT static inline
#include "DrumApi.c"

#include "drum_glue.h"

uint32_t fm1_pitch_increment_of(int16_t pitch);
int16_t fm1_voice_pitch(int32_t pitch);

#define DRUM_FULL (1u << 24)

void fm1_drum_init(drum_voice_t *v)
{
    uint32_t i;
    for (i = 0; i < 6u; i++) { v->phase[i] = 0; v->inc[i] = 0; }
    for (i = 0; i < 4u; i++) v->lp[i] = 0;
    v->envelope[0] = 0; v->envelope[1] = 0;
    v->sweep = 0; v->noise = 1; v->age = 65535;
    v->shape = 0; v->timbre = 16384; v->colour = 16384; v->pending = 0;
}

void fm1_drum_set(drum_voice_t *v, uint32_t shape, int32_t pitch, int32_t timbre, int32_t colour)
{
    uint32_t base = fm1_pitch_increment_of(fm1_voice_pitch(pitch)), osc;
    v->shape = shape % DRUM_SHAPES;
    v->timbre = timbre < 0 ? 0u : (uint32_t)timbre;
    v->colour = colour < 0 ? 0u : (uint32_t)colour;
    for (osc = 0; osc < 6u; osc++) v->inc[osc] = fm1_drum_tuning(v->shape, osc, base);
}

/* The envelopes restart and the oscillators line up (the sine from zero, the squares spread round the cycle
 * so the metal's first sample is not six edges at once). The sweep's start needs the block's tuning, which
 * the firmware sets after the strike, so render takes it from there. The noise and the filters run on. */
void fm1_drum_strike(drum_voice_t *v)
{
    uint32_t i;
    for (i = 0; i < 6u; i++) v->phase[i] = i * 0x2AAAAAAAu;
    v->envelope[0] = DRUM_FULL; v->envelope[1] = DRUM_FULL;
    v->age = 0; v->pending = 1;
}

/* The kick and the toms: a sine on a swept increment, plus noise through a low-pass on a short envelope. */
static void drum_render_tuned(drum_voice_t *v, int16_t *out, uint32_t count, uint32_t rateA, uint32_t rateB,
                              uint32_t levelA, uint32_t levelB, uint32_t aL)
{
    const uint32_t sweepRate = fm1_drum_sweep_rate(v->shape), target = v->inc[0];
    uint32_t p = v->phase[0], sw = v->sweep, n = v->noise, e0 = v->envelope[0], e1 = v->envelope[1];
    int32_t lp = v->lp[0];
    while (count--) {
        int32_t tone = (int32_t)fm1_drum_sine(p), mix;
        lp = (int32_t)fm1_drum_one_pole(lp, fm1_drum_noise(n), aL);
        mix = (int32_t)fm1_drum_scale(tone, fm1_drum_gain(e0, levelA)) +
              (int32_t)fm1_drum_scale(lp, fm1_drum_gain(e1, levelB));
        *out++ = (int16_t)fm1_drum_saturate(mix);
        sw = fm1_drum_sweep(sw, target, sweepRate); p += sw; n = fm1_drum_lfsr(n);
        e0 = fm1_drum_envelope(e0, rateA); e1 = fm1_drum_envelope(e1, rateB);
    }
    v->phase[0] = p; v->sweep = sw; v->noise = n; v->envelope[0] = e0; v->envelope[1] = e1; v->lp[0] = lp;
}

/* The snare: two sines, plus noise through a high-pass on its own envelope. */
static void drum_render_snare(drum_voice_t *v, int16_t *out, uint32_t count, uint32_t rateA, uint32_t rateB,
                              uint32_t levelA, uint32_t levelB, uint32_t aH)
{
    const uint32_t i0 = v->inc[0], i1 = v->inc[1];
    uint32_t p0 = v->phase[0], p1 = v->phase[1], n = v->noise, e0 = v->envelope[0], e1 = v->envelope[1];
    int32_t lp = v->lp[0];
    while (count--) {
        int32_t tone = (int32_t)fm1_drum_sine(p0) + (int32_t)fm1_drum_sine(p1), nz = (int32_t)fm1_drum_noise(n), mix;
        lp = (int32_t)fm1_drum_one_pole(lp, nz, aH);
        mix = (int32_t)fm1_drum_scale(tone, fm1_drum_gain(e0, levelA)) +
              (int32_t)fm1_drum_scale((int32_t)fm1_drum_high_pass(lp, nz), fm1_drum_gain(e1, levelB));
        *out++ = (int16_t)fm1_drum_saturate(mix);
        p0 += i0; p1 += i1; n = fm1_drum_lfsr(n);
        e0 = fm1_drum_envelope(e0, rateA); e1 = fm1_drum_envelope(e1, rateB);
    }
    v->phase[0] = p0; v->phase[1] = p1; v->noise = n; v->envelope[0] = e0; v->envelope[1] = e1; v->lp[0] = lp;
}

/* The clap: noise through a band-pass, on three bursts 10 ms apart (the burst envelope restarts) and a
 * tail. */
static void drum_render_clap(drum_voice_t *v, int16_t *out, uint32_t count, uint32_t rateA, uint32_t rateB,
                             uint32_t levelA, uint32_t levelB, uint32_t aH, uint32_t aL)
{
    uint32_t n = v->noise, e0 = v->envelope[0], e1 = v->envelope[1], age = v->age;
    int32_t lp0 = v->lp[0], lp1 = v->lp[1];
    while (count--) {
        int32_t nz = (int32_t)fm1_drum_noise(n), mix;
        if (fm1_drum_clap_retrigger(age)) e1 = DRUM_FULL;
        lp0 = (int32_t)fm1_drum_one_pole(lp0, nz, aH);
        lp1 = (int32_t)fm1_drum_one_pole(lp1, (int32_t)fm1_drum_high_pass(lp0, nz), aL);
        mix = (int32_t)fm1_drum_scale(lp1, fm1_drum_gain(e0, levelA)) +
              (int32_t)fm1_drum_scale(lp1, fm1_drum_gain(e1, levelB));
        *out++ = (int16_t)fm1_drum_saturate(mix);
        n = fm1_drum_lfsr(n); age = fm1_drum_age_step(age);
        e0 = fm1_drum_envelope(e0, rateA); e1 = fm1_drum_envelope(e1, rateB);
    }
    v->noise = n; v->envelope[0] = e0; v->envelope[1] = e1; v->age = age; v->lp[0] = lp0; v->lp[1] = lp1;
}

/* The hi-hats and the cowbell: squares summed, through a band-pass, on one envelope. */
static void drum_render_metal(drum_voice_t *v, int16_t *out, uint32_t count, uint32_t rateA, uint32_t levelA,
                              uint32_t aH, uint32_t aL, int cowbell)
{
    const uint32_t i0 = v->inc[0], i1 = v->inc[1], i2 = v->inc[2], i3 = v->inc[3], i4 = v->inc[4], i5 = v->inc[5];
    uint32_t p0 = v->phase[0], p1 = v->phase[1], p2 = v->phase[2], p3 = v->phase[3], p4 = v->phase[4],
             p5 = v->phase[5], e0 = v->envelope[0];
    int32_t lp0 = v->lp[0], lp1 = v->lp[1];
    while (count--) {
        int32_t s = cowbell ? (int32_t)fm1_drum_square(p0) + (int32_t)fm1_drum_square(p1)
                            : (int32_t)fm1_drum_metal(p0, p1, p2, p3, p4, p5);
        lp0 = (int32_t)fm1_drum_one_pole(lp0, s, aH);
        lp1 = (int32_t)fm1_drum_one_pole(lp1, (int32_t)fm1_drum_high_pass(lp0, s), aL);
        *out++ = (int16_t)fm1_drum_saturate((int32_t)fm1_drum_scale(lp1, fm1_drum_gain(e0, levelA)));
        p0 += i0; p1 += i1; p2 += i2; p3 += i3; p4 += i4; p5 += i5;
        e0 = fm1_drum_envelope(e0, rateA);
    }
    v->phase[0] = p0; v->phase[1] = p1; v->phase[2] = p2; v->phase[3] = p3; v->phase[4] = p4; v->phase[5] = p5;
    v->envelope[0] = e0; v->lp[0] = lp0; v->lp[1] = lp1;
}

/* The cymbal: the six squares through two band-passes, the lower on a long envelope, the upper on a shorter. */
static void drum_render_cymbal(drum_voice_t *v, int16_t *out, uint32_t count, uint32_t rateA, uint32_t rateB,
                               uint32_t levelA, uint32_t levelB, uint32_t aH, uint32_t aL)
{
    const uint32_t i0 = v->inc[0], i1 = v->inc[1], i2 = v->inc[2], i3 = v->inc[3], i4 = v->inc[4], i5 = v->inc[5];
    const uint32_t uH = fm1_drum_upper_coefficient(0), uL = fm1_drum_upper_coefficient(1);
    uint32_t p0 = v->phase[0], p1 = v->phase[1], p2 = v->phase[2], p3 = v->phase[3], p4 = v->phase[4],
             p5 = v->phase[5], e0 = v->envelope[0], e1 = v->envelope[1];
    int32_t lp0 = v->lp[0], lp1 = v->lp[1], lp2 = v->lp[2], lp3 = v->lp[3];
    while (count--) {
        int32_t s = (int32_t)fm1_drum_metal(p0, p1, p2, p3, p4, p5), mix;
        lp0 = (int32_t)fm1_drum_one_pole(lp0, s, aH);
        lp1 = (int32_t)fm1_drum_one_pole(lp1, (int32_t)fm1_drum_high_pass(lp0, s), aL);
        lp2 = (int32_t)fm1_drum_one_pole(lp2, s, uH);
        lp3 = (int32_t)fm1_drum_one_pole(lp3, (int32_t)fm1_drum_high_pass(lp2, s), uL);
        mix = (int32_t)fm1_drum_scale(lp1, fm1_drum_gain(e0, levelA)) +
              (int32_t)fm1_drum_scale(lp3, fm1_drum_gain(e1, levelB));
        *out++ = (int16_t)fm1_drum_saturate(mix);
        p0 += i0; p1 += i1; p2 += i2; p3 += i3; p4 += i4; p5 += i5;
        e0 = fm1_drum_envelope(e0, rateA); e1 = fm1_drum_envelope(e1, rateB);
    }
    v->phase[0] = p0; v->phase[1] = p1; v->phase[2] = p2; v->phase[3] = p3; v->phase[4] = p4; v->phase[5] = p5;
    v->envelope[0] = e0; v->envelope[1] = e1; v->lp[0] = lp0; v->lp[1] = lp1; v->lp[2] = lp2; v->lp[3] = lp3;
}

void fm1_drum_render(drum_voice_t *v, int16_t *out, uint32_t count)
{
    const uint32_t shape = v->shape, timbre = v->timbre, colour = v->colour;
    const uint32_t rateA = fm1_drum_rate(shape, timbre), rateB = fm1_drum_second_rate(shape, timbre);
    const uint32_t levelA = fm1_drum_level(shape, colour), levelB = fm1_drum_second_level(shape, colour);
    const uint32_t aH = fm1_drum_high_coefficient(shape, colour), aL = fm1_drum_low_coefficient(shape);
    if (v->pending) { v->pending = 0; v->sweep = fm1_drum_sweep_start(v->inc[0], colour); }
    switch (shape) {
    case 1: drum_render_snare(v, out, count, rateA, rateB, levelA, levelB, aH); break;
    case 2: drum_render_clap(v, out, count, rateA, rateB, levelA, levelB, aH, aL); break;
    case 3: case 4: drum_render_metal(v, out, count, rateA, levelA, aH, aL, 0); break;
    case 8: drum_render_metal(v, out, count, rateA, levelA, aH, aL, 1); break;
    case 9: drum_render_cymbal(v, out, count, rateA, rateB, levelA, levelB, aH, aL); break;
    default: drum_render_tuned(v, out, count, rateA, rateB, levelA, levelB, aL); break;
    }
}
