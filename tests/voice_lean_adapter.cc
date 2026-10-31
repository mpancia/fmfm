// SPDX-License-Identifier: GPL-3.0-only
// A Braids macro oscillator as a C interface for tests/voice_diff.cc: the firmware's (voices/braids).
#include "braids/macro_oscillator.h"

static const uint8_t kNoSync[24] = {0};

extern "C" {
void *lean_voice_create() {
  braids::MacroOscillator *osc = new braids::MacroOscillator;
  osc->Init();
  return osc;
}
void lean_voice_set(void *voice, int shape, int pitch, int timbre, int color) {
  braids::MacroOscillator *osc = static_cast<braids::MacroOscillator *>(voice);
  osc->set_shape(static_cast<braids::MacroOscillatorShape>(shape));
  osc->set_pitch(static_cast<int16_t>(pitch));
  osc->set_parameters(static_cast<int16_t>(timbre), static_cast<int16_t>(color));
}
void lean_voice_strike(void *voice) { static_cast<braids::MacroOscillator *>(voice)->Strike(); }
void lean_voice_render(void *voice, int16_t *out, int count) {
  static_cast<braids::MacroOscillator *>(voice)->Render(kNoSync, out, count);
}
}
