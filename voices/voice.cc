// SPDX-License-Identifier: GPL-3.0-only
// The C interface to one Braids macro oscillator (voices/voice.h).
#include "voice.h"

#include <new>

#include "braids/macro_oscillator.h"

extern "C" {
// The narrowing of what the firmware sends is in voices/voice_setup_glue.c, the arithmetic in Firmware/VoiceSetup.lean.
uint32_t fm1_voice_shape(uint32_t shape);
int16_t fm1_voice_pitch(int32_t pitch);
int16_t fm1_voice_parameter(int32_t value);
}

namespace {

static_assert(sizeof(braids::MacroOscillator) <= BRAIDS_VOICE_BYTES, "raise BRAIDS_VOICE_BYTES in voice.h");

const char *const kShapeNames[BRAIDS_SHAPES] = {
    "CSAW", "MORPH", "SAW SQR", "SIN TRI", "BUZZ", "SQR SUB", "SAW SUB", "SQR SYNC", "SAW SYNC", "3 SAW",
    "3 SQR", "3 TRI", "3 SIN", "3 RING", "SWARM", "SAW COMB", "TOY", "FLT LP", "FLT PK", "FLT BP", "FLT HP",
    "VOSIM", "VOWEL", "VOWEL F", "HARMONIC", "FM", "FBK FM", "CHAOS FM", "PLUCK", "BOW", "BLOW", "FLUTE",
    "BELL", "DRUM", "KICK", "CYMBAL", "SNARE", "WAVETBL", "WAVE MAP", "WAVE LN", "WAVE PARA", "NOISE FLT",
    "TWIN PK", "CLK NOISE", "GRANULAR", "PARTICLE", "DIGI MOD", "?"};

const uint8_t kNoSync[BRAIDS_BLOCK] = {0};

braids::MacroOscillator *as_osc(void *voice) { return static_cast<braids::MacroOscillator *>(voice); }

}  // namespace

extern "C" {

void braids_voice_init(void *voice) {
  braids::MacroOscillator *osc = new (voice) braids::MacroOscillator;
  osc->Init();
}

void braids_voice_set(void *voice, uint32_t shape, int32_t pitch, int32_t timbre, int32_t color) {
  braids::MacroOscillator *osc = as_osc(voice);
  osc->set_shape(static_cast<braids::MacroOscillatorShape>(fm1_voice_shape(shape)));
  osc->set_pitch(fm1_voice_pitch(pitch));
  osc->set_parameters(fm1_voice_parameter(timbre), fm1_voice_parameter(color));
}

void braids_voice_strike(void *voice) { as_osc(voice)->Strike(); }

void braids_voice_render(void *voice, int16_t *out, uint32_t count) {
  as_osc(voice)->Render(kNoSync, out, count);
}

const char *braids_shape_name(uint32_t shape) { return shape < BRAIDS_SHAPES ? kShapeNames[shape] : "?"; }

}  // extern "C"
