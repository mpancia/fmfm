// Copyright 2012 Emilie Gillet.
//
// Author: Emilie Gillet (emilie.o.gillet@gmail.com)
//
// Permission is hereby granted, free of charge, to any person obtaining a copy
// of this software and associated documentation files (the "Software"), to deal
// in the Software without restriction, including without limitation the rights
// to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
// copies of the Software, and to permit persons to whom the Software is
// furnished to do so, subject to the following conditions:
// 
// The above copyright notice and this permission notice shall be included in
// all copies or substantial portions of the Software.
// 
// THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
// IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
// FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
// AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
// LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
// OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN
// THE SOFTWARE.
// 
// See http://creativecommons.org/licenses/MIT/ for more information.
//
// -----------------------------------------------------------------------------
//
// Oscillator - analog style waveforms.

#include "braids/analog_oscillator.h"

#include "stmlib/utils/dsp.h"

#include "braids/resources.h"
#include "braids/parameter_interpolation.h"

extern "C" {
// The sample loops of these four oscillators are in voices/analog_glue.c, the arithmetic in Firmware/Analog.lean.
void fm1_analog_render_saw(uint32_t*, uint32_t*, uint32_t, int32_t*, const uint8_t*, int16_t*, uint8_t*, uint32_t);
void fm1_analog_render_square(uint32_t*, uint32_t*, uint32_t, int32_t*, uint8_t*, uint32_t, const uint8_t*, int16_t*,
                              uint8_t*, uint32_t);
void fm1_analog_render_triangle(uint32_t*, uint32_t*, uint32_t, const uint8_t*, int16_t*, uint32_t);
void fm1_analog_render_sine(uint32_t*, uint32_t*, uint32_t, const uint8_t*, int16_t*, uint32_t);
void fm1_analog_render_variable_saw(uint32_t*, uint32_t*, uint32_t, int32_t*, uint8_t*, uint32_t, const uint8_t*,
                                    int16_t*, uint8_t*, uint32_t);
void fm1_analog_render_csaw(uint32_t*, uint32_t*, uint32_t, int32_t*, uint8_t*, int32_t*, uint32_t, int32_t,
                            const uint8_t*, int16_t*, uint8_t*, uint32_t);
void fm1_analog_render_triangle_fold(uint32_t*, uint32_t*, uint32_t, int32_t*, int32_t, const uint8_t*, int16_t*,
                                     uint32_t);
void fm1_analog_render_sine_fold(uint32_t*, uint32_t*, uint32_t, int32_t*, int32_t, const uint8_t*, int16_t*, uint32_t);
void fm1_analog_render_buzz(uint32_t*, uint32_t, uint32_t, uint32_t, uint32_t, const uint8_t*, int16_t*, uint32_t);
// The pitch to phase step is in voices/pitch_glue.c, the arithmetic in Firmware/Pitch.lean.
uint32_t fm1_pitch_increment_of(int16_t pitch);
// The per-block setup is in voices/analog_setup_glue.c, the arithmetic in Firmware/AnalogSetup.lean.
int16_t fm1_analog_clamped_pitch(int16_t pitch);
uint32_t fm1_analog_square_pulse_width(int16_t parameter);
uint32_t fm1_analog_variable_saw_pulse_width(int16_t parameter);
uint32_t fm1_analog_buzz_zone(int16_t pitch, int16_t parameter);
uint32_t fm1_analog_buzz_zone2(int16_t pitch, int16_t parameter);
uint32_t fm1_analog_buzz_crossfade(int16_t pitch, int16_t parameter);
}

namespace braids {

using namespace stmlib;

uint32_t AnalogOscillator::ComputePhaseIncrement(int16_t midi_pitch) {
  return fm1_pitch_increment_of(midi_pitch);
}

void AnalogOscillator::Render(
    const uint8_t* sync_in,
    int16_t* buffer,
    uint8_t* sync_out,
    size_t size) {
  RenderFn fn = fn_table_[shape_];
  
  if (shape_ != previous_shape_) {
    Init();
    previous_shape_ = shape_;
  }
  
  phase_increment_ = ComputePhaseIncrement(pitch_);
  pitch_ = fm1_analog_clamped_pitch(pitch_);
  
  (this->*fn)(sync_in, buffer, sync_out, size);
}

void AnalogOscillator::RenderCSaw(
    const uint8_t* sync_in,
    int16_t* buffer,
    uint8_t* sync_out,
    size_t size) {
  uint8_t high = high_;
  int32_t depth = discontinuity_depth_;
  fm1_analog_render_csaw(&phase_, &previous_phase_increment_, phase_increment_, &next_sample_, &high, &depth,
                         static_cast<uint32_t>(parameter_), aux_parameter_, sync_in, buffer, sync_out, size);
  high_ = high;
  discontinuity_depth_ = static_cast<int16_t>(depth);
}

void AnalogOscillator::RenderSquare(
    const uint8_t* sync_in,
    int16_t* buffer,
    uint8_t* sync_out,
    size_t size) {
  uint8_t high = high_;
  fm1_analog_render_square(&phase_, &previous_phase_increment_, phase_increment_, &next_sample_, &high,
                           fm1_analog_square_pulse_width(parameter_), sync_in, buffer, sync_out, size);
  high_ = high;
}

void AnalogOscillator::RenderSaw(
    const uint8_t* sync_in,
    int16_t* buffer,
    uint8_t* sync_out,
    size_t size) {
  fm1_analog_render_saw(&phase_, &previous_phase_increment_, phase_increment_, &next_sample_, sync_in, buffer,
                        sync_out, size);
}

void AnalogOscillator::RenderVariableSaw(
    const uint8_t* sync_in,
    int16_t* buffer,
    uint8_t* sync_out,
    size_t size) {
  uint8_t high = high_;
  fm1_analog_render_variable_saw(&phase_, &previous_phase_increment_, phase_increment_, &next_sample_, &high,
                                 fm1_analog_variable_saw_pulse_width(parameter_), sync_in, buffer, sync_out, size);
  high_ = high;
}

void AnalogOscillator::RenderTriangle(
    const uint8_t* sync_in,
    int16_t* buffer,
    uint8_t* sync_out,
    size_t size) {
  fm1_analog_render_triangle(&phase_, &previous_phase_increment_, phase_increment_, sync_in, buffer, size);
}

void AnalogOscillator::RenderSine(
    const uint8_t* sync_in,
    int16_t* buffer,
    uint8_t* sync_out,
    size_t size) {
  fm1_analog_render_sine(&phase_, &previous_phase_increment_, phase_increment_, sync_in, buffer, size);
}

void AnalogOscillator::RenderTriangleFold(
    const uint8_t* sync_in,
    int16_t* buffer,
    uint8_t* sync_out,
    size_t size) {
  int32_t previous_parameter = previous_parameter_;
  fm1_analog_render_triangle_fold(&phase_, &previous_phase_increment_, phase_increment_, &previous_parameter,
                                  parameter_, sync_in, buffer, size);
  previous_parameter_ = parameter_;
}

void AnalogOscillator::RenderSineFold(
    const uint8_t* sync_in,
    int16_t* buffer,
    uint8_t* sync_out,
    size_t size) {
  int32_t previous_parameter = previous_parameter_;
  fm1_analog_render_sine_fold(&phase_, &previous_phase_increment_, phase_increment_, &previous_parameter,
                              parameter_, sync_in, buffer, size);
  previous_parameter_ = parameter_;
}

void AnalogOscillator::RenderBuzz(
    const uint8_t* sync_in,
    int16_t* buffer,
    uint8_t* sync_out,
    size_t size) {
  fm1_analog_render_buzz(&phase_, phase_increment_, fm1_analog_buzz_zone(pitch_, parameter_),
                         fm1_analog_buzz_zone2(pitch_, parameter_), fm1_analog_buzz_crossfade(pitch_, parameter_),
                         sync_in, buffer, size);
}

/* static */
AnalogOscillator::RenderFn AnalogOscillator::fn_table_[] = {
  &AnalogOscillator::RenderSaw,
  &AnalogOscillator::RenderVariableSaw,
  &AnalogOscillator::RenderCSaw,
  &AnalogOscillator::RenderSquare,
  &AnalogOscillator::RenderTriangle,
  &AnalogOscillator::RenderSine,
  &AnalogOscillator::RenderTriangleFold,
  &AnalogOscillator::RenderSineFold,
  &AnalogOscillator::RenderBuzz,
};

}  // namespace braids

// One entry of the sine table, for the Lean code (Firmware/Analog.lean, `Analog.sineTable`).
extern "C" uint16_t fm1_braids_wav_sine(uint32_t index) {
  return static_cast<uint16_t>(braids::wav_sine[index]);
}

// Entries of Braids' wave-shaper and comb tables, for the Lean code (Firmware/Analog.lean).
extern "C" uint16_t fm1_braids_ws_sine_fold(uint32_t index) {
  return static_cast<uint16_t>(braids::ws_sine_fold[index]);
}
extern "C" uint16_t fm1_braids_ws_tri_fold(uint32_t index) {
  return static_cast<uint16_t>(braids::ws_tri_fold[index]);
}
extern "C" uint16_t fm1_braids_comb(uint32_t zone, uint32_t index) {
  return static_cast<uint16_t>(braids::waveform_table[WAV_BANDLIMITED_COMB_0 + zone][index]);
}

// The top octave of phase steps (97 entries), for the Lean code (Firmware/Pitch.lean, `Pitch.incrementTable`).
extern "C" uint32_t fm1_braids_oscillator_increment(uint32_t index) {
  return braids::lut_oscillator_increments[index];
}
