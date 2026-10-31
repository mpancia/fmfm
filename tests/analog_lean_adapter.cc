// SPDX-License-Identifier: GPL-3.0-only
// The firmware's analog oscillator (voices/braids, with the Lean arithmetic), as a C interface for
// tests/analog_diff.cc.
#include "braids/analog_oscillator.h"

extern "C" {
void *lean_create() {
  braids::AnalogOscillator *osc = new braids::AnalogOscillator;
  osc->Init();
  return osc;
}
void lean_render(void *osc, int shape, int pitch, int parameter, const uint8_t *sync_in, int16_t *out,
                 uint8_t *sync_out, size_t size) {
  braids::AnalogOscillator *o = static_cast<braids::AnalogOscillator *>(osc);
  o->set_shape(static_cast<braids::AnalogOscillatorShape>(shape));
  o->set_pitch(static_cast<int16_t>(pitch));
  o->set_parameter(static_cast<int16_t>(parameter));
  o->Render(sync_in, out, sync_out, size);
}
}
