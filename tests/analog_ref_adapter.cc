// SPDX-License-Identifier: GPL-3.0-only
// Braids' original analog oscillator (tests/reference/braids), as a C interface for tests/analog_diff.cc.
#include "braids/analog_oscillator.h"

extern "C" {
void *ref_create() {
  braids_ref::AnalogOscillator *osc = new braids_ref::AnalogOscillator;
  osc->Init();
  return osc;
}
void ref_render(void *osc, int shape, int pitch, int parameter, const uint8_t *sync_in, int16_t *out, uint8_t *sync_out,
                size_t size) {
  braids_ref::AnalogOscillator *o = static_cast<braids_ref::AnalogOscillator *>(osc);
  o->set_shape(static_cast<braids_ref::AnalogOscillatorShape>(shape));
  o->set_pitch(static_cast<int16_t>(pitch));
  o->set_parameter(static_cast<int16_t>(parameter));
  o->Render(sync_in, out, sync_out, size);
}
}
