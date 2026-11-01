/* SPDX-License-Identifier: GPL-3.0-only */
/* Spec/Reverb.lean against fx/reverb_glue.c: the spec says what the glue's sequence of calls computes for one
 * sample, given the samples the glue reads from its memory. This program drives the glue, takes those reads just
 * before each sample (the same positions the glue is about to use), and prints them with the glue's two outputs;
 * tests/reverb_spec.lean recomputes the outputs from the spec and compares. One line a sample:
 *   send kInput kDiffusion kTime kLowpass state0 o1 o2 o3 o4 tail oA oB wetLeft state1 tail2 oA2 oB2 wetRight */
#include <stdio.h>

#include "../fx/reverb_glue.c"

static int32_t peek(uint32_t wp, uint32_t line, uint32_t offset)
{
    return s32(fm1_rv_decompress(ring[fm1_rv_pos(wp, start[line], offset)]));
}
static int32_t oldest(uint32_t wp, uint32_t line) { return peek(wp, line, length[line] - 1u); }

int main(void)
{
    uint32_t rng = 7, n;
    fm1_reverb_init(256, 0x8000000u);
    for (n = 0; n < 20000; n++) {
        uint32_t wp = fm1_rv_next_write(write_pos), lfo1 = lfo_now[1], q16, whole;
        int32_t send, tail, left, right;
        rng = rng * 1664525u + 1013904223u;
        send = n < 4000 ? (int32_t)(rng >> 12) - 524288 : 0;        /* a loud burst (within 2^19), then the tail */
        if (n % 5000 == 2500) {                                     /* new settings mid-way, as a knob turn would */
            fm1_reverb_set((int32_t)(rng >> 17) % 32769, (int32_t)(rng >> 3) % 32769,
                           (int32_t)(rng >> 9) % 32769 - 16384, (int32_t)(rng >> 5) % 32769);
        }
        if ((wp & 31u) == 0) lfo1 = (uint32_t)fm1_rv_lfo(phase[1]);
        q16 = fm1_rv_mod_offset(4680u, 100u, scale_q8, lfo1); whole = q16 >> 16;
        tail = s32(fm1_rv_interpolate((uint32_t)peek(wp, DEL2, whole), (uint32_t)peek(wp, DEL2, whole + 1u),
                                      q16 & 0xFFFFu));
        printf("%d %d %d %d %d %d %d %d %d %d %d %d %d ", send, k_input, k_diffusion, k_time, k_lowpass,
               lowpass_state[0], oldest(wp, AP1), oldest(wp, AP2), oldest(wp, AP3), oldest(wp, AP4), tail,
               oldest(wp, DAP1A), oldest(wp, DAP1B));
        {
            int32_t state1 = lowpass_state[1], tail2 = oldest(wp, DEL1), a2 = oldest(wp, DAP2A), b2 = oldest(wp, DAP2B);
            fm1_reverb_block(&send, &left, &right, 1);
            printf("%d %d %d %d %d %d\n", left, state1, tail2, a2, b2, right);
        }
    }
    return 0;
}
