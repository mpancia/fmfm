/* SPDX-License-Identifier: GPL-3.0-only */
/* The four-operator FM voice (shapes 48 on): the state and the sample loop are here (the envelopes move once a
 * block of 16 samples), the arithmetic of every
 * sample, the algorithms and the shapes are Lean (Firmware/Fm.lean), included below as inline functions.
 * voices/voice.cc hands the firmware's calls here for an FM shape. */
#include <lean/lean.h>
#include <stdint.h>

#undef LEAN_EXPORT
#define LEAN_EXPORT static inline
#include "FmApi.c"

#include "fm_glue.h"

uint32_t fm1_pitch_increment_of(int16_t pitch);
int16_t fm1_voice_pitch(int32_t pitch);

void fm1_fm_init(fm_voice_t *v)
{
    uint32_t op;
    for (op = 0; op < 4u; op++) { v->phase[op] = 0; v->inc[op] = 0; v->envelope[op] = 0; v->out[op] = 0; }
    v->shape = 0; v->timbre = 16384; v->colour = 0;
}

void fm1_fm_set(fm_voice_t *v, uint32_t shape, int32_t pitch, int32_t timbre, int32_t colour)
{
    uint32_t base = fm1_pitch_increment_of(fm1_voice_pitch(pitch)), op;
    v->shape = shape;
    v->timbre = timbre < 0 ? 0u : (uint32_t)timbre;
    v->colour = colour < 0 ? 0u : (uint32_t)colour;
    for (op = 0; op < 4u; op++) v->inc[op] = fm1_fm_increment(base, fm1_fm_ratio(shape, op + 1u));
}

void fm1_fm_strike(fm_voice_t *v)
{
    uint32_t op;
    for (op = 0; op < 4u; op++) { v->envelope[op] = 1u << 24; v->out[op] = 0; }
}

void fm1_fm_render(fm_voice_t *v, int16_t *out, uint32_t count)
{
    const uint32_t shape = v->shape, alg = fm1_fm_algorithm(shape), feedback = fm1_fm_feedback(shape, v->colour);
    uint32_t depth[4], level[4], rate[4], carries[4], modulates[4][4], op, src;
    for (op = 0; op < 4u; op++) {                            /* the shape's tables, once a block */
        depth[op] = fm1_fm_depth(shape, op + 1u, v->timbre);
        level[op] = fm1_fm_level(shape, op + 1u);
        rate[op] = fm1_fm_rate(shape, op + 1u);
        carries[op] = fm1_fm_carries(alg, op + 1u);
        for (src = 0; src < 4u; src++) modulates[op][src] = fm1_fm_modulates(alg, op + 1u, src + 1u);
    }
    {   /* the state in registers for the loop; operators 4 to 1 in turn so every modulator is this sample's */
        uint32_t p0 = v->phase[0], p1 = v->phase[1], p2 = v->phase[2], p3 = v->phase[3];
        uint32_t e0 = v->envelope[0], e1 = v->envelope[1], e2 = v->envelope[2], e3 = v->envelope[3];
        int32_t o0 = v->out[0], o1 = v->out[1], o2 = v->out[2], o3 = v->out[3];
        const uint32_t i0 = v->inc[0], i1 = v->inc[1], i2 = v->inc[2], i3 = v->inc[3];
        const uint32_t m01 = modulates[0][1], m02 = modulates[0][2], m03 = modulates[0][3], m12 = modulates[1][2],
                       m13 = modulates[1][3], m23 = modulates[2][3];
        while (count--) {
            int32_t sum = 0;
            uint32_t push;
            o3 = fm1_fm_operator(p3, fm1_fm_push(0, o3, feedback), e3);
            push = m23 ? fm1_fm_push(0, o3, depth[3]) : 0u;
            o2 = fm1_fm_operator(p2, push, e2);
            push = m12 ? fm1_fm_push(0, o2, depth[2]) : 0u;
            if (m13) push = fm1_fm_push(push, o3, depth[3]);
            o1 = fm1_fm_operator(p1, push, e1);
            push = m01 ? fm1_fm_push(0, o1, depth[1]) : 0u;
            if (m02) push = fm1_fm_push(push, o2, depth[2]);
            if (m03) push = fm1_fm_push(push, o3, depth[3]);
            o0 = fm1_fm_operator(p0, push, e0);
            if (carries[0]) sum += fm1_fm_carry(o0, level[0]);
            if (carries[1]) sum += fm1_fm_carry(o1, level[1]);
            if (carries[2]) sum += fm1_fm_carry(o2, level[2]);
            if (carries[3]) sum += fm1_fm_carry(o3, level[3]);
            p0 += i0; p1 += i1; p2 += i2; p3 += i3;
            *out++ = fm1_fm_saturate(sum);
        }
        v->phase[0] = p0; v->phase[1] = p1; v->phase[2] = p2; v->phase[3] = p3;
        v->envelope[0] = fm1_fm_envelope_step(e0, rate[0]); v->envelope[1] = fm1_fm_envelope_step(e1, rate[1]);
        v->envelope[2] = fm1_fm_envelope_step(e2, rate[2]); v->envelope[3] = fm1_fm_envelope_step(e3, rate[3]);
        v->out[0] = o0; v->out[1] = o1; v->out[2] = o2; v->out[3] = o3;
    }
}
