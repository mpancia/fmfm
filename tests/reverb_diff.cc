// SPDX-License-Identifier: GPL-3.0-only
// The reverb ported to Lean against Clouds' original, on this computer: the same input and settings through both,
// then the error between the two outputs. tests/reference/clouds is Clouds unchanged (namespace renamed at compile
// time). Delay sizes are Clouds' own (scale 256) so the two are the same room.
//   Two checks, because the two are not the same signal after the first few thousand samples. Before the long delays
//   are first read the outputs agree closely (a click: under -30 dB error, 12-bit rounding plus the LFO's shape). After that the LFO
//   matters: the port's sine is a parabola, Clouds' a recurrence, and a delay time that differs by a tenth of a sample
//   decorrelates the wobbling tail from the original's. So the tail is compared by loudness: the level in 50 ms
//   windows must stay within 2 dB of the original's (down to -41 dBFS, below which the 12-bit steps dominate).
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include "clouds/dsp/frame.h"
#include "clouds/dsp/fx/reverb.h"
#include "reverb.h"

static uint16_t reference_memory[16384];

struct Case { const char *name; int time, bright; int input; };      // input: 0 click, 1 noise burst, 2 sine burst

static float input_at(int kind, int n, uint32_t *rng)
{
    *rng = *rng * 1664525u + 1013904223u;
    if (kind == 0) return n < 200 ? ((int16_t)(*rng >> 16)) / 32768.0f * 0.9f : 0.0f;       // a click
    if (kind == 1) return n < 8000 ? ((int16_t)(*rng >> 16)) / 32768.0f * 0.6f : 0.0f;
    return n < 16000 ? 0.7f * sinf(0.045f * (float)n) : 0.0f;
}

int main()
{
    const Case cases[] = {{"click, mid time", 50, 50, 0}, {"click, longest, bright", 100, 100, 0},
                          {"click, shortest, dark", 0, 0, 0}, {"noise burst, long", 90, 60, 1},
                          {"sine burst, mid", 40, 80, 2}};
    const int total = 32000 * 4, head = 4000, window = 1600;          // four seconds at Clouds' 32 kHz
    int failed = 0;
    for (const Case &c : cases) {
        clouds_ref::Reverb ref;
        static int32_t send[FM1_REVERB_BLOCK], left[FM1_REVERB_BLOCK], right[FM1_REVERB_BLOCK];
        const float time_gain = (11469 + 20644 * c.time / 100) / 32768.0f, lowpass = (19661 + 12124 * c.bright / 100) / 32768.0f;
        uint32_t rng = 7;
        double head_err2 = 0, head_sig2 = 0, win_ref = 0, win_got = 0, worst_db = 0, sum_db = 0;
        int windows = 0, counted = 0;
        memset(&ref, 0, sizeof ref);                                   // Clouds' processor is zeroed before Init
        ref.Init(reference_memory);
        ref.set_amount(1.0f); ref.set_input_gain(6554 / 32768.0f); ref.set_time(time_gain);
        ref.set_diffusion(22938 / 32768.0f); ref.set_lp(lowpass);
        fm1_reverb_init(256, 67109);                                   // a half hertz at 32 kHz
        fm1_reverb_set(11469 + 20644 * c.time / 100, 19661 + 12124 * c.bright / 100, 22938, 6554);
        for (int start = 0; start < total; start += FM1_REVERB_BLOCK) {
            int count = total - start < (int)FM1_REVERB_BLOCK ? total - start : (int)FM1_REVERB_BLOCK;
            static clouds_ref::FloatFrame frames[FM1_REVERB_BLOCK];
            for (int i = 0; i < count; i++) {
                send[i] = (int32_t)lrintf(input_at(c.input, start + i, &rng) * 32768.0f);
                frames[i].l = frames[i].r = (float)send[i] / 32768.0f / 2.0f;     // the reverb reads l + r
            }
            ref.Process(frames, count);
            fm1_reverb_block(send, left, right, count);
            for (int i = 0; i < count; i++) {
                double want[2] = {frames[i].l * 32768.0, frames[i].r * 32768.0}, got[2] = {(double)left[i], (double)right[i]};
                int n = start + i;
                for (int k = 0; k < 2; k++) {
                    if (n < head) { head_err2 += (got[k] - want[k]) * (got[k] - want[k]); head_sig2 += want[k] * want[k]; }
                    win_ref += want[k] * want[k]; win_got += got[k] * got[k];
                }
                if ((n + 1) % window == 0) {
                    double r = sqrt(win_ref / (2 * window)), g = sqrt(win_got / (2 * window));
                    windows++;
                    if (r > 300.0) {                                   // louder than -41 dBFS (below it 12-bit steps dominate)
                        double db = 20 * log10((g + 1e-9) / r);
                        counted++; sum_db += fabs(db);
                        if (fabs(db) > fabs(worst_db)) worst_db = db;
                    }
                    win_ref = win_got = 0;
                }
            }
        }
        double head_db = 10 * log10(head_err2 / (head_sig2 + 1e-9) + 1e-12);
        bool ok = head_db < (c.input == 0 ? -30 : -15) && fabs(worst_db) < 2.0 && counted > 0;   // bursts run the input diffuser's LFO longer
        printf("%s %-26s first %d samples: error %6.1f dB; loudness over %d windows: worst %+.2f dB, mean %.2f dB\n",
               ok ? "PASS" : "FAIL", c.name, head, head_db, counted, worst_db, counted ? sum_db / counted : 0.0);
        failed += !ok;
    }
    return failed ? 1 : 0;
}
