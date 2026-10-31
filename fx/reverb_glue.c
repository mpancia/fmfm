/* SPDX-License-Identifier: GPL-3.0-only */
/* The reverb send. The network follows `Reverb::Process` in Clouds (Emilie Gillet, MIT): the Griesinger topology
 * of Dattorro's paper, four allpass diffusers on the input and then two loops of two allpasses and a delay, with
 * LFO modulation on one diffuser and on the long delay of the first loop. This file owns the delay memory, the
 * write position and the filter states; the arithmetic of each step, included below as inline functions, is Lean
 * (Firmware/Reverb.lean). Each helper is one operation of Clouds' `FxEngine::Context`, on an accumulator. */
#include <lean/lean.h>
#include <stddef.h>
#include <stdint.h>

#include "reverb.h"

#undef LEAN_EXPORT
#define LEAN_EXPORT static inline
#include "ReverbApi.c"

#define RING 32768u
#ifdef FM1_CHIP
static uint16_t ring[RING] __attribute__((section(".pool")));
#else
static uint16_t ring[RING];
#endif

enum { AP1, AP2, AP3, AP4, DAP1A, DAP1B, DEL1, DAP2A, DAP2B, DEL2, LINES };

static uint32_t scale_q8, write_pos, start[LINES], length[LINES], phase[2], phase_step[2], lfo_now[2];
static int32_t lowpass_state[2];
static int32_t k_time = 16384, k_lowpass = 20000, k_diffusion = 22938, k_input = 6554;
static int32_t acc, previous;                  /* Clouds' accumulator and last read */

static int32_t s32(uint32_t v) { return (int32_t)v; }
static uint32_t scaled(uint32_t samples) { return (samples * scale_q8 + 128u) >> 8; }

static void load(int32_t v) { acc = v; }
static void read_value(int32_t v, int32_t gain) { acc += s32(fm1_rv_mul((uint32_t)v, (uint32_t)gain)); }
static int32_t fetch(uint32_t line, uint32_t offset)
{
    return s32(fm1_rv_decompress(ring[fm1_rv_pos(write_pos, start[line], offset)]));
}
static void read_line(uint32_t line, int32_t gain)       /* the oldest sample of the line ("TAIL") */
{
    previous = fetch(line, length[line] - 1u);
    acc += s32(fm1_rv_mul((uint32_t)previous, (uint32_t)gain));
}
static void write_line(uint32_t line, uint32_t offset, int32_t gain)
{
    ring[fm1_rv_pos(write_pos, start[line], offset)] = (uint16_t)fm1_rv_compress((uint32_t)acc);
    acc = s32(fm1_rv_mul((uint32_t)acc, (uint32_t)gain));
}
static void write_allpass(uint32_t line, int32_t gain)
{
    write_line(line, 0, gain);
    acc += previous;
}
static void read_modulated(uint32_t line, uint32_t base, uint32_t depth, uint32_t which, int32_t gain)
{
    uint32_t q16 = fm1_rv_mod_offset(base, depth, scale_q8, lfo_now[which]), whole = q16 >> 16;
    int32_t a = fetch(line, whole), b = fetch(line, whole + 1u);
    previous = s32(fm1_rv_interpolate((uint32_t)a, (uint32_t)b, q16 & 0xFFFFu));
    acc += s32(fm1_rv_mul((uint32_t)previous, (uint32_t)gain));
}
static void lowpass(uint32_t which, int32_t coefficient)
{
    lowpass_state[which] = s32(fm1_rv_lowpass((uint32_t)lowpass_state[which], (uint32_t)acc, (uint32_t)coefficient));
    acc = lowpass_state[which];
}

void fm1_reverb_clear(void)
{
    uint32_t i;
    for (i = 0; i < RING; i++) ring[i] = 0;
    lowpass_state[0] = lowpass_state[1] = 0;
}

void fm1_reverb_init(uint32_t scale, uint32_t lfo_phase_step)
{
    uint32_t i;
    scale_q8 = scale;
    for (i = 0; i < LINES; i++) { start[i] = fm1_rv_start(scale, i); length[i] = fm1_rv_length(scale, i); }
    fm1_reverb_clear();
    write_pos = 0; phase[0] = phase[1] = 0;
    phase_step[0] = lfo_phase_step;                       /* Clouds: 0.5 Hz and 0.3 Hz at 32 kHz */
    phase_step[1] = lfo_phase_step / 5u * 3u;
    lfo_now[0] = lfo_now[1] = fm1_rv_lfo(0);
}

void fm1_reverb_tune(uint32_t time, uint32_t bright)    /* settings of 0 to 100, as on the screen */
{
    k_time = s32(fm1_rv_time_gain(time));
    k_lowpass = s32(fm1_rv_bright_gain(bright));
}

void fm1_reverb_set(int32_t time_gain, int32_t lowpass_gain, int32_t diffusion, int32_t input_gain)
{
    k_time = time_gain; k_lowpass = lowpass_gain; k_diffusion = diffusion; k_input = input_gain;
}

void fm1_reverb_block(const int32_t *send, int32_t *wet_left, int32_t *wet_right, uint32_t count)
{
    const int32_t two = 65536;                 /* 2.0 */
    uint32_t n;
    for (n = 0; n < count; n++) {
        int32_t apout;
        write_pos = fm1_rv_next_write(write_pos);
        if ((write_pos & 31u) == 0) {          /* the LFOs step once in 32 samples */
            lfo_now[0] = fm1_rv_lfo(phase[0]); lfo_now[1] = fm1_rv_lfo(phase[1]);
            phase[0] += 32u * phase_step[0]; phase[1] += 32u * phase_step[1];
        }
        acc = 0; previous = 0;

        read_modulated(AP1, 10u, 60u, 0, 32768);               /* smear the first diffuser inside its loop */
        write_line(AP1, scaled(100u), 0);
        read_value(send[n], k_input);
        read_line(AP1, k_diffusion); write_allpass(AP1, -k_diffusion);
        read_line(AP2, k_diffusion); write_allpass(AP2, -k_diffusion);
        read_line(AP3, k_diffusion); write_allpass(AP3, -k_diffusion);
        read_line(AP4, k_diffusion); write_allpass(AP4, -k_diffusion);
        apout = acc;

        load(apout);                                           /* the first loop, which makes the left output */
        read_modulated(DEL2, 4680u, 100u, 1, k_time);
        lowpass(0, k_lowpass);
        read_line(DAP1A, -k_diffusion); write_allpass(DAP1A, k_diffusion);
        read_line(DAP1B, k_diffusion); write_allpass(DAP1B, -k_diffusion);
        write_line(DEL1, 0, two);
        wet_left[n] = acc;

        load(apout);                                           /* the second loop, which makes the right output */
        read_line(DEL1, k_time);
        lowpass(1, k_lowpass);
        read_line(DAP2A, k_diffusion); write_allpass(DAP2A, -k_diffusion);
        read_line(DAP2B, -k_diffusion); write_allpass(DAP2B, k_diffusion);
        write_line(DEL2, 0, two);
        wet_right[n] = acc;
    }
}
