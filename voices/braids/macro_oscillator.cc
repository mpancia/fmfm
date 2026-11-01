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
// Macro-oscillator.

#include "braids/macro_oscillator.h"
#include "macro_glue.h"

#include <algorithm>

extern "C" {
// The per-block setup is in voices/macro_setup_glue.c, the arithmetic in Firmware/MacroSetup.lean.
int32_t fm1_macro_csaw_shift(int16_t parameter1);
uint32_t fm1_macro_morph_zone(int16_t parameter0);
uint32_t fm1_macro_morph_balance(int16_t parameter0);
int32_t fm1_macro_morph_parameter(int16_t parameter0);
int32_t fm1_macro_morph_cutoff(int16_t pitch, int16_t parameter1);
int32_t fm1_macro_morph_fuzz(int16_t pitch, int16_t parameter1);
int16_t fm1_macro_triple_pitch(int16_t pitch, int16_t parameter);
int16_t fm1_macro_sub_pitch(int16_t pitch, int16_t parameter1);
int16_t fm1_macro_dual_sync_pitch(int16_t pitch, int16_t parameter0);
int32_t fm1_macro_sine_parameter(int16_t pitch, int16_t parameter0);
int32_t fm1_macro_tri_parameter(int16_t pitch, int16_t parameter0);
int16_t fm1_macro_buzz_pitch(int16_t pitch, int16_t parameter1);
}

namespace braids {
  
using namespace stmlib;

void MacroOscillator::Render(
    const uint8_t* sync,
    int16_t* buffer,
    size_t size) {
  RenderFn fn = fn_table_[shape_];
  (this->*fn)(sync, buffer, size);
}

void MacroOscillator::RenderCSaw(
    const uint8_t* sync,
    int16_t* buffer,
    size_t size) {
  analog_oscillator_[0].set_pitch(pitch_);
  analog_oscillator_[0].set_shape(OSC_SHAPE_CSAW);
  analog_oscillator_[0].set_parameter(parameter_[0]);
  analog_oscillator_[0].set_aux_parameter(parameter_[1]);
  analog_oscillator_[0].Render(sync, buffer, NULL, size);
  fm1_macro_render_csaw(buffer, fm1_macro_csaw_shift(parameter_[1]), size);
}

void MacroOscillator::RenderMorph(
    const uint8_t* sync,
    int16_t* buffer,
    size_t size) {
  analog_oscillator_[0].set_pitch(pitch_);
  analog_oscillator_[1].set_pitch(pitch_);
  
  uint32_t zone = fm1_macro_morph_zone(parameter_[0]);
  analog_oscillator_[0].set_parameter(fm1_macro_morph_parameter(parameter_[0]));
  analog_oscillator_[1].set_parameter(0);
  analog_oscillator_[0].set_shape(zone == 0 ? OSC_SHAPE_TRIANGLE : OSC_SHAPE_SQUARE);
  analog_oscillator_[1].set_shape(zone == 2 ? OSC_SHAPE_SINE : OSC_SHAPE_SAW);
  
  int16_t* shape_1 = buffer;
  int16_t* shape_2 = temp_buffer_;
  analog_oscillator_[0].Render(sync, shape_1, NULL, size);
  analog_oscillator_[1].Render(sync, shape_2, NULL, size);
  
  fm1_macro_render_morph(buffer, shape_2, fm1_macro_morph_balance(parameter_[0]), &lp_state_,
                         fm1_macro_morph_cutoff(pitch_, parameter_[1]), fm1_macro_morph_fuzz(pitch_, parameter_[1]),
                         size);
}

void MacroOscillator::RenderSawSquare(
    const uint8_t* sync,
    int16_t* buffer,
    size_t size) {
  analog_oscillator_[0].set_parameter(parameter_[0]);
  analog_oscillator_[1].set_parameter(parameter_[0]);
  analog_oscillator_[0].set_pitch(pitch_);
  analog_oscillator_[1].set_pitch(pitch_);

  analog_oscillator_[0].set_shape(OSC_SHAPE_VARIABLE_SAW);
  analog_oscillator_[1].set_shape(OSC_SHAPE_SQUARE);
  
  int16_t* saw_buffer = buffer;
  int16_t* square_buffer = temp_buffer_;
  
  analog_oscillator_[0].Render(sync, saw_buffer, NULL, size);
  analog_oscillator_[1].Render(sync, square_buffer, NULL, size);
  
  fm1_macro_render_saw_square(saw_buffer, square_buffer, previous_parameter_[1], parameter_[1], size);
  previous_parameter_[1] = parameter_[1];
}

#define SEMI * 128

const int16_t intervals[65] = {
  -24 SEMI, -24 SEMI, -24 SEMI + 4,
  -23 SEMI, -22 SEMI, -21 SEMI, -20 SEMI, -19 SEMI, -18 SEMI,
  -17 SEMI - 4, -17 SEMI,
  -16 SEMI, -15 SEMI, -14 SEMI, -13 SEMI,
  -12 SEMI - 4, -12 SEMI,
  -11 SEMI, -10 SEMI, -9 SEMI, -8 SEMI,
  -7 SEMI - 4, -7 SEMI,
  -6 SEMI, -5 SEMI, -4 SEMI, -3 SEMI, -2 SEMI, -1 SEMI,
  -24, -8, -4, 0, 4, 8, 24,
  1 SEMI, 2 SEMI, 3 SEMI, 4 SEMI, 5 SEMI, 6 SEMI,
  7 SEMI, 7 SEMI + 4,
  8 SEMI, 9 SEMI, 10 SEMI, 11 SEMI,
  12 SEMI, 12 SEMI + 4,
  13 SEMI, 14 SEMI, 15 SEMI, 16 SEMI,
  17 SEMI, 17 SEMI + 4,
  18 SEMI, 19 SEMI, 20 SEMI, 21 SEMI, 22 SEMI, 23 SEMI,
  24 SEMI - 4, 24 SEMI, 24 SEMI
};

extern "C" int16_t fm1_braids_macro_interval(uint32_t index) {
  return intervals[index];
}

void MacroOscillator::RenderTriple(
    const uint8_t* sync,
    int16_t* buffer,
    size_t size) {
  AnalogOscillatorShape base_shape;
  switch (shape_) {
    case MACRO_OSC_SHAPE_TRIPLE_SAW:
      base_shape = OSC_SHAPE_SAW;
      break;
    case MACRO_OSC_SHAPE_TRIPLE_TRIANGLE:
      base_shape = OSC_SHAPE_TRIANGLE;
      break;
    case MACRO_OSC_SHAPE_TRIPLE_SQUARE:
      base_shape = OSC_SHAPE_SQUARE;
      break;
    default:
      base_shape = OSC_SHAPE_SINE;
      break;
  }
  
  analog_oscillator_[0].set_parameter(0);
  analog_oscillator_[1].set_parameter(0);
  analog_oscillator_[2].set_parameter(0);

  analog_oscillator_[0].set_pitch(pitch_);
  for (size_t i = 0; i < 2; ++i) {
    analog_oscillator_[i + 1].set_pitch(fm1_macro_triple_pitch(pitch_, parameter_[i]));
  }

  analog_oscillator_[0].set_shape(base_shape);
  analog_oscillator_[1].set_shape(base_shape);
  analog_oscillator_[2].set_shape(base_shape);

  std::fill(&buffer[0], &buffer[size], 0);
  for (size_t i = 0; i < 3; ++i) {
    analog_oscillator_[i].Render(sync, temp_buffer_, NULL, size);
    fm1_macro_render_triple_add(buffer, temp_buffer_, size);
  }
}

void MacroOscillator::RenderSub(
    const uint8_t* sync,
    int16_t* buffer,
    size_t size) {
  AnalogOscillatorShape base_shape = shape_ == MACRO_OSC_SHAPE_SQUARE_SUB ?
      OSC_SHAPE_SQUARE : OSC_SHAPE_VARIABLE_SAW;
  analog_oscillator_[0].set_parameter(parameter_[0]);
  analog_oscillator_[0].set_shape(base_shape);
  analog_oscillator_[0].set_pitch(pitch_);

  analog_oscillator_[1].set_parameter(0);
  analog_oscillator_[1].set_shape(OSC_SHAPE_SQUARE);
  analog_oscillator_[1].set_pitch(fm1_macro_sub_pitch(pitch_, parameter_[1]));

  analog_oscillator_[0].Render(sync, buffer, NULL, size);
  analog_oscillator_[1].Render(sync, temp_buffer_, NULL, size);
  
  fm1_macro_render_sub(buffer, temp_buffer_, previous_parameter_[1], parameter_[1], size);
  previous_parameter_[1] = parameter_[1];
}

void MacroOscillator::RenderDualSync(
    const uint8_t* sync,
    int16_t* buffer,
    size_t size) {
  AnalogOscillatorShape base_shape = shape_ == MACRO_OSC_SHAPE_SQUARE_SYNC ?
      OSC_SHAPE_SQUARE : OSC_SHAPE_SAW;
  analog_oscillator_[0].set_parameter(0);
  analog_oscillator_[0].set_shape(base_shape);
  analog_oscillator_[0].set_pitch(pitch_);

  analog_oscillator_[1].set_parameter(0);
  analog_oscillator_[1].set_shape(base_shape);
  analog_oscillator_[1].set_pitch(fm1_macro_dual_sync_pitch(pitch_, parameter_[0]));

  analog_oscillator_[0].Render(sync, buffer, sync_buffer_, size);
  analog_oscillator_[1].Render(sync_buffer_, temp_buffer_, NULL, size);
  
  fm1_macro_render_dual_sync(buffer, temp_buffer_, previous_parameter_[1], parameter_[1], size);
  previous_parameter_[1] = parameter_[1];
}

void MacroOscillator::RenderSineTriangle(
    const uint8_t* sync,
    int16_t* buffer,
    size_t size) {
  analog_oscillator_[0].set_parameter(fm1_macro_sine_parameter(pitch_, parameter_[0]));
  analog_oscillator_[1].set_parameter(fm1_macro_tri_parameter(pitch_, parameter_[0]));
  analog_oscillator_[0].set_pitch(pitch_);
  analog_oscillator_[1].set_pitch(pitch_);
  
  analog_oscillator_[0].set_shape(OSC_SHAPE_SINE_FOLD);
  analog_oscillator_[1].set_shape(OSC_SHAPE_TRIANGLE_FOLD);

  analog_oscillator_[0].Render(sync, buffer, NULL, size);
  analog_oscillator_[1].Render(sync, temp_buffer_, NULL, size);

  fm1_macro_render_sine_triangle(buffer, temp_buffer_, previous_parameter_[1], parameter_[1], size);
  previous_parameter_[1] = parameter_[1];
}

void MacroOscillator::RenderBuzz(
    const uint8_t* sync,
    int16_t* buffer,
    size_t size) {
  analog_oscillator_[0].set_parameter(parameter_[0]);
  analog_oscillator_[0].set_shape(OSC_SHAPE_BUZZ);
  analog_oscillator_[0].set_pitch(pitch_);

  analog_oscillator_[1].set_parameter(parameter_[0]);
  analog_oscillator_[1].set_shape(OSC_SHAPE_BUZZ);
  analog_oscillator_[1].set_pitch(fm1_macro_buzz_pitch(pitch_, parameter_[1]));

  analog_oscillator_[0].Render(sync, buffer, NULL, size);
  analog_oscillator_[1].Render(sync, temp_buffer_, NULL, size);
  fm1_macro_render_buzz(buffer, temp_buffer_, size);
}

void MacroOscillator::RenderDigital(
    const uint8_t* sync,
    int16_t* buffer,
    size_t size) {
  digital_oscillator_.set_parameters(parameter_[0], parameter_[1]);
  digital_oscillator_.set_pitch(pitch_);
  digital_oscillator_.set_shape(static_cast<DigitalOscillatorShape>(
      shape_ - MACRO_OSC_SHAPE_TRIPLE_RING_MOD));
  digital_oscillator_.Render(sync, buffer, size);
}

void MacroOscillator::RenderSawComb(
  const uint8_t* sync,
  int16_t* buffer,
  size_t size) {
  analog_oscillator_[0].set_parameter(0);
  analog_oscillator_[0].set_pitch(pitch_);
  analog_oscillator_[0].set_shape(OSC_SHAPE_SAW);
  analog_oscillator_[0].Render(sync, buffer, NULL, size);
  
  digital_oscillator_.set_parameters(parameter_[0], parameter_[1]);
  digital_oscillator_.set_pitch(pitch_);
  digital_oscillator_.set_shape(OSC_SHAPE_COMB_FILTER);
  digital_oscillator_.Render(sync, buffer, size);
}

/* static */
MacroOscillator::RenderFn MacroOscillator::fn_table_[] = {
  &MacroOscillator::RenderCSaw,
  &MacroOscillator::RenderMorph,
  &MacroOscillator::RenderSawSquare,
  &MacroOscillator::RenderSineTriangle,
  &MacroOscillator::RenderBuzz,
  &MacroOscillator::RenderSub,
  &MacroOscillator::RenderSub,
  &MacroOscillator::RenderDualSync,
  &MacroOscillator::RenderDualSync,
  &MacroOscillator::RenderTriple,
  &MacroOscillator::RenderTriple,
  &MacroOscillator::RenderTriple,
  &MacroOscillator::RenderTriple,
  &MacroOscillator::RenderDigital,
  &MacroOscillator::RenderDigital,
  &MacroOscillator::RenderSawComb,
  &MacroOscillator::RenderDigital,
  &MacroOscillator::RenderDigital,
  &MacroOscillator::RenderDigital,
  &MacroOscillator::RenderDigital,
  &MacroOscillator::RenderDigital,
  &MacroOscillator::RenderDigital,
  &MacroOscillator::RenderDigital,
  &MacroOscillator::RenderDigital,
  &MacroOscillator::RenderDigital,
  &MacroOscillator::RenderDigital,
  &MacroOscillator::RenderDigital,
  &MacroOscillator::RenderDigital,
  &MacroOscillator::RenderDigital,
  &MacroOscillator::RenderDigital,
  &MacroOscillator::RenderDigital,
  &MacroOscillator::RenderDigital,
  &MacroOscillator::RenderDigital,
  &MacroOscillator::RenderDigital,
  &MacroOscillator::RenderDigital,
  &MacroOscillator::RenderDigital,
  &MacroOscillator::RenderDigital,
  &MacroOscillator::RenderDigital,
  &MacroOscillator::RenderDigital,
  &MacroOscillator::RenderDigital,
  &MacroOscillator::RenderDigital,
  &MacroOscillator::RenderDigital,
  &MacroOscillator::RenderDigital,
  &MacroOscillator::RenderDigital,
  &MacroOscillator::RenderDigital,
  &MacroOscillator::RenderDigital,
  &MacroOscillator::RenderDigital,
  &MacroOscillator::RenderDigital,
  // &MacroOscillator::RenderDigital
};

}  // namespace braids
