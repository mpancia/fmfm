// SPDX-License-Identifier: GPL-3.0-only
// The C interface to one Braids macro oscillator (voices/voice.h).
#include "voice.h"

#include <new>

#include "braids/macro_oscillator.h"
#include "fm_glue.h"
#include "drum_glue.h"

extern "C" {
// The narrowing of what the firmware sends is in voices/voice_setup_glue.c, the arithmetic in Firmware/VoiceSetup.lean.
uint32_t fm1_voice_shape(uint32_t shape);
int16_t fm1_voice_pitch(int32_t pitch);
int16_t fm1_voice_parameter(int32_t value);
}

namespace {

constexpr uint32_t kFmOffset = BRAIDS_VOICE_BYTES - 256u;   // the FM voice's state sits after the Braids one, the drum's after that
constexpr uint32_t kDrumOffset = BRAIDS_VOICE_BYTES - 128u;
static_assert(sizeof(braids::MacroOscillator) <= kFmOffset, "raise BRAIDS_VOICE_BYTES in voice.h");
static_assert(sizeof(fm_voice_t) <= 128u, "the FM state outgrew its 128 bytes");
static_assert(sizeof(drum_voice_t) <= 128u, "the drum state outgrew its 128 bytes");

const char *const kShapeNames[BRAIDS_SHAPES] = {
    "CSAW", "MORPH", "SAW SQR", "SIN TRI", "BUZZ", "SQR SUB", "SAW SUB", "SQR SYNC", "SAW SYNC", "3 SAW",
    "3 SQR", "3 TRI", "3 SIN", "3 RING", "SWARM", "SAW COMB", "TOY", "FLT LP", "FLT PK", "FLT BP", "FLT HP",
    "VOSIM", "VOWEL", "VOWEL F", "HARMONIC", "FM", "FBK FM", "CHAOS FM", "PLUCK", "BOW", "BLOW", "FLUTE",
    "BELL", "DRUM", "KICK", "CYMBAL", "SNARE", "WAVETBL", "WAVE MAP", "WAVE LN", "WAVE PARA", "NOISE FLT",
    "TWIN PK", "CLK NOISE", "GRANULAR", "PARTICLE", "DIGI MOD", "?",
    "FM PIANO", "FM BELL", "FM BASS", "FM BRASS", "FM GLASS", "FM MALLET", "FM ORGAN", "FM CLANG",
    "808 BD", "808 SD", "808 CP", "808 CH", "808 OH", "808 LT", "808 MT", "808 HT", "808 CB", "808 CY"};

const uint8_t kNoSync[BRAIDS_BLOCK] = {0};

braids::MacroOscillator *as_osc(void *voice) { return static_cast<braids::MacroOscillator *>(voice); }
fm_voice_t *as_fm(void *voice) { return reinterpret_cast<fm_voice_t *>(static_cast<uint8_t *>(voice) + kFmOffset); }
drum_voice_t *as_drum(void *voice) { return reinterpret_cast<drum_voice_t *>(static_cast<uint8_t *>(voice) + kDrumOffset); }
// which engine the voice is on: Braids, the FM voice (shape 48 to 55) or the drums (56 on); the FM state's shape field holds it
bool is_fm(void *voice) { return as_fm(voice)->shape >= 48u && as_fm(voice)->shape < 56u; }
bool is_drum(void *voice) { return as_fm(voice)->shape >= 56u; }

}  // namespace

extern "C" {

void braids_voice_init(void *voice) {
  braids::MacroOscillator *osc = new (voice) braids::MacroOscillator;
  osc->Init();
  fm1_fm_init(as_fm(voice));
  fm1_drum_init(as_drum(voice));
}

void braids_voice_set(void *voice, uint32_t shape, int32_t pitch, int32_t timbre, int32_t color) {
  braids::MacroOscillator *osc = as_osc(voice);
  if (shape >= 56u) { as_fm(voice)->shape = shape; fm1_drum_set(as_drum(voice), shape - 56u, pitch, timbre, color); return; }
  if (shape >= 48u) { fm1_fm_set(as_fm(voice), shape, pitch, timbre, color); return; }
  as_fm(voice)->shape = 0;
  osc->set_shape(static_cast<braids::MacroOscillatorShape>(fm1_voice_shape(shape)));
  osc->set_pitch(fm1_voice_pitch(pitch));
  osc->set_parameters(fm1_voice_parameter(timbre), fm1_voice_parameter(color));
}

void braids_voice_strike(void *voice) {
  if (is_drum(voice)) fm1_drum_strike(as_drum(voice));
  else if (is_fm(voice)) fm1_fm_strike(as_fm(voice));
  else as_osc(voice)->Strike();
}

void braids_voice_render(void *voice, int16_t *out, uint32_t count) {
  if (is_drum(voice)) fm1_drum_render(as_drum(voice), out, count);
  else if (is_fm(voice)) fm1_fm_render(as_fm(voice), out, count);
  else as_osc(voice)->Render(kNoSync, out, count);
}

const char *braids_shape_name(uint32_t shape) { return shape < BRAIDS_SHAPES ? kShapeNames[shape] : "?"; }

}  // extern "C"
