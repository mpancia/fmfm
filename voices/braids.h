/* SPDX-License-Identifier: MIT */
/* Oscillator shapes ported from Braids, the macro oscillator of Mutable Instruments (Copyright 2012 Emilie
 * Gillet, MIT licence, see LICENSE-braids.txt): SAW and SQUARE (band-limited with a polynomial BLEP step,
 * analog_oscillator.cc), FM and FEEDBACK FM (digital_oscillator.cc). Whole-number maths only, as the chip has no
 * FPU. Changes from Braids: no oscillator sync, a sample rate of 44.1 kHz with our own pitch table (Braids' is
 * for 96 kHz), and a plain sine shape.
 *
 * A voice owns one braids_t. Pitches are in 1/128 semitone, MIDI note n is n * 128. */
#pragma once
#include <stdint.h>
#include "braids_sine.h"

enum { BRAIDS_SAW, BRAIDS_SQUARE, BRAIDS_FM, BRAIDS_FEEDBACK_FM, BRAIDS_SINE };

typedef struct {
    uint32_t phase, mod_phase;
    int32_t next;               /* the part of the last step edge that falls in the next sample */
    int16_t previous;           /* last output, for feedback FM */
    uint8_t high;               /* square: is the output in its high half */
} braids_t;

/* phase step per sample for MIDI notes 120..131 (C9..B9) at 44.1 kHz: f * 2^32 / 44100 */
static const uint32_t BRAIDS_INC_C9[12] = {
    815363807u, 863847862u, 915214929u, 969636441u, 1027294024u, 1088380105u,
    1153098554u, 1221665363u, 1294309365u, 1371273005u, 1452813141u, 1539201906u};

static uint32_t braids_note_inc(uint32_t note)
{
    return BRAIDS_INC_C9[note % 12u] >> (10u - note / 12u);       /* note 0..131 */
}

static uint32_t braids_pitch_inc(int32_t pitch)
{
    uint32_t note, a, b;
    if (pitch < 0) pitch = 0;
    if (pitch > 131 * 128 - 1) pitch = 131 * 128 - 1;
    note = (uint32_t)pitch >> 7;
    a = braids_note_inc(note);
    b = braids_note_inc(note + 1u);
    return a + (uint32_t)(((uint64_t)(b - a) * ((uint32_t)pitch & 127u)) >> 7);
}

/* the sine table at a 32-bit phase, interpolated */
static int32_t braids_sine(uint32_t phase)
{
    int32_t a = braids_wav_sine[phase >> 24], b = braids_wav_sine[(phase >> 24) + 1u];
    return a + (((b - a) * (int32_t)((phase >> 8) & 0xFFFFu)) >> 16);
}

static int32_t braids_blep_this(uint32_t t)
{
    if (t > 65535u) t = 65535u;
    return (int32_t)(t * t >> 18);
}
static int32_t braids_blep_next(uint32_t t)
{
    if (t > 65535u) t = 65535u;
    t = 65535u - t;
    return -(int32_t)(t * t >> 18);
}

static int32_t braids_saw(braids_t *o, uint32_t inc)
{
    int32_t out = o->next, next = 0;
    uint32_t den = inc >> 16;
    if (!den) den = 1;                      /* no division by zero */
    o->phase += inc;
    if (o->phase < inc) {                   /* the saw fell back to the start in this sample */
        uint32_t t = o->phase / den;
        out -= braids_blep_this(t);
        next -= braids_blep_next(t);
    }
    next += (int32_t)(o->phase >> 17);
    o->next = next;
    return (out - 16384) << 1;
}

/* `param` 0..32000: 0 is a square, more is a narrower pulse */
static int32_t braids_square(braids_t *o, uint32_t inc, int32_t param)
{
    int32_t out = o->next, next = 0;
    uint32_t den = inc >> 16, pw, self_reset;
    if (!den) den = 1;
    if (param < 0) param = 0;
    if (param > 32000) param = 32000;
    pw = (uint32_t)(32768 - param) << 16;
    o->phase += inc;
    self_reset = o->phase < inc;
    for (;;) {
        uint32_t t;
        if (!o->high) {
            if (o->phase < pw) break;
            t = (o->phase - pw) / den;
            out += braids_blep_this(t);
            next += braids_blep_next(t);
            o->high = 1;
        }
        if (!self_reset) break;
        self_reset = 0;
        t = o->phase / den;
        out -= braids_blep_this(t);
        next -= braids_blep_next(t);
        o->high = 0;
    }
    next += o->phase < pw ? 0 : 32767;
    o->next = next;
    return (out - 16384) << 1;
}

/* `index` 0..32767 is how strongly the modulator bends the carrier; `mod_inc` is the modulator's phase step */
static int32_t braids_fm(braids_t *o, uint32_t inc, uint32_t mod_inc, int32_t index)
{
    uint32_t pm;
    o->phase += inc;
    o->mod_phase += mod_inc;
    pm = (uint32_t)(braids_sine(o->mod_phase) * index) << 2;
    return braids_sine(o->phase + pm);
}

/* The carrier's last output feeds back into the modulator. `attenuation` 0..32767 lowers the index for high notes. */
static int32_t braids_feedback_fm(braids_t *o, uint32_t inc, uint32_t mod_inc, int32_t index, int32_t attenuation)
{
    int32_t p = index * attenuation >> 15;
    uint32_t pm = (uint32_t)o->previous << 14;
    o->phase += inc;
    o->mod_phase += mod_inc;
    pm = (uint32_t)(braids_sine(o->mod_phase + pm) * p) << 1;
    o->previous = (int16_t)braids_sine(o->phase + pm);
    return o->previous;
}
