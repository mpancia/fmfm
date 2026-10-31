// SPDX-License-Identifier: GPL-3.0-only
// A Braids macro oscillator as a C interface for tests/voice_diff.cc: the original (tests/reference).
#include "braids/macro_oscillator.h"

static const uint8_t kNoSync[24] = {0};

extern "C" {
void *ref_voice_create() {
  braids_ref::MacroOscillator *osc = new braids_ref::MacroOscillator;
  osc->Init();
  return osc;
}
void ref_voice_set(void *voice, int shape, int pitch, int timbre, int color) {
  braids_ref::MacroOscillator *osc = static_cast<braids_ref::MacroOscillator *>(voice);
  osc->set_shape(static_cast<braids_ref::MacroOscillatorShape>(shape));
  osc->set_pitch(static_cast<int16_t>(pitch));
  osc->set_parameters(static_cast<int16_t>(timbre), static_cast<int16_t>(color));
}
void ref_voice_strike(void *voice) { static_cast<braids_ref::MacroOscillator *>(voice)->Strike(); }
void ref_voice_render(void *voice, int16_t *out, int count) {
  static_cast<braids_ref::MacroOscillator *>(voice)->Render(kNoSync, out, count);
}
}
