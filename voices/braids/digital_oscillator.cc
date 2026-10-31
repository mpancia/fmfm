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
// Oscillator - digital style waveforms.

#include "braids/digital_oscillator.h"
#include "filters_glue.h"
#include "vowels_glue.h"
#include "wavetables_glue.h"
#include "noise_glue.h"
#include "percussion_glue.h"
#include "physical_glue.h"

extern "C" {
void fm1_digital_render_fm(uint32_t*, uint32_t*, uint32_t, uint32_t, int32_t, int32_t, const uint8_t*, int16_t*,
                           uint32_t);
void fm1_digital_render_feedback_fm(uint32_t*, uint32_t*, int16_t*, uint32_t, uint32_t, int32_t, int32_t, int32_t,
                                    const uint8_t*, int16_t*, uint32_t);
void fm1_digital_render_chaotic_fm(uint32_t*, uint32_t*, int16_t*, uint32_t, uint32_t, int32_t, int32_t,
                                   const uint8_t*, int16_t*, uint32_t);
void fm1_digital_render_ring_mod(uint32_t*, uint32_t*, uint32_t*, uint32_t, uint32_t, uint32_t, const uint8_t*,
                                 int16_t*, uint32_t);
void fm1_digital_render_toy(uint32_t*, uint8_t*, uint16_t*, uint32_t, uint16_t, uint8_t, const uint8_t*, int16_t*,
                            uint32_t);
void fm1_digital_render_modulation(uint32_t*, uint32_t*, uint16_t*, int32_t*, uint8_t*, uint32_t, uint32_t, int32_t,
                                   int16_t*, uint32_t);
}

#include <algorithm>
#include <cstdio>

#include "stmlib/utils/dsp.h"
#include "stmlib/utils/random.h"

#include "braids/parameter_interpolation.h"
#include "braids/resources.h"

namespace braids {
  
using namespace stmlib;

static const uint16_t kHighestNote = 140 * 128;
static const uint16_t kPitchTableStart = 128 * 128;
static const uint16_t kOctave = 12 * 128;


uint32_t DigitalOscillator::ComputePhaseIncrement(int16_t midi_pitch) {
  if (midi_pitch >= kPitchTableStart) {
    midi_pitch = kPitchTableStart - 1;
  }
  
  int32_t ref_pitch = midi_pitch;
  ref_pitch -= kPitchTableStart;
  
  size_t num_shifts = 0;
  while (ref_pitch < 0) {
    ref_pitch += kOctave;
    ++num_shifts;
  }
  
  uint32_t a = lut_oscillator_increments[ref_pitch >> 4];
  uint32_t b = lut_oscillator_increments[(ref_pitch >> 4) + 1];
  uint32_t phase_increment = a + \
      (static_cast<int32_t>(b - a) * (ref_pitch & 0xf) >> 4);
  phase_increment >>= num_shifts;
  return phase_increment;
}

uint32_t DigitalOscillator::ComputeDelay(int16_t midi_pitch) {
  if (midi_pitch >= kHighestNote - kOctave) {
    midi_pitch = kHighestNote - kOctave;
  }
  
  int32_t ref_pitch = midi_pitch;
  ref_pitch -= kPitchTableStart;
  
  size_t num_shifts = 0;
  while (ref_pitch < 0) {
    ref_pitch += kOctave;
    ++num_shifts;
  }
  
  uint32_t a = lut_oscillator_delays[ref_pitch >> 4];
  uint32_t b = lut_oscillator_delays[(ref_pitch >> 4) + 1];
  uint32_t delay = a + (static_cast<int32_t>(b - a) * (ref_pitch & 0xf) >> 4);  
  delay >>= 12 - num_shifts;
  return delay;
}

void DigitalOscillator::Render(
    const uint8_t* sync,
    int16_t* buffer,
    size_t size) {

  // Quantize parameter for FM.
  if (shape_ >= OSC_SHAPE_FM &&
      shape_ <= OSC_SHAPE_CHAOTIC_FEEDBACK_FM) {
    uint16_t integral = parameter_[1] >> 8;
    uint16_t fractional = parameter_[1] & 255;
    int16_t a = lut_fm_frequency_quantizer[integral];
    int16_t b = lut_fm_frequency_quantizer[integral + 1];
    parameter_[1] = a + ((b - a) * fractional >> 8);
  }    
  
  RenderFn fn = fn_table_[shape_];
  
  if (shape_ != previous_shape_) {
    Init();
    previous_shape_ = shape_;
    init_ = true;
  }
  
  phase_increment_ = ComputePhaseIncrement(pitch_);
  delay_ = ComputeDelay(pitch_);
  
  if (pitch_ > kHighestNote) {
    pitch_ = kHighestNote;
  } else if (pitch_ < 0) {
    pitch_ = 0;
  }

  (this->*fn)(sync, buffer, size);
}

void DigitalOscillator::RenderTripleRingMod(
    const uint8_t* sync,
    int16_t* buffer,
    size_t size) {
  uint32_t increment_1 = ComputePhaseIncrement(pitch_ + ((parameter_[0] - 16384) >> 2));
  uint32_t increment_2 = ComputePhaseIncrement(pitch_ + ((parameter_[1] - 16384) >> 2));
  fm1_digital_render_ring_mod(&phase_, &state_.vow.formant_phase[0], &state_.vow.formant_phase[1], phase_increment_,
                              increment_1, increment_2, sync, buffer, size);
}

void DigitalOscillator::RenderSawSwarm(
    const uint8_t* sync,
    int16_t* buffer,
    size_t size) {
  int32_t detune = parameter_[0] + 1024;
  detune = (detune * detune) >> 9;
  uint32_t increments[7];
  for (int16_t i = 0; i < 7; ++i) {
    int32_t saw_detune = detune * (i - 3);
    int32_t detune_integral = saw_detune >> 16;
    int32_t detune_fractional = saw_detune & 0xffff;
    int32_t increment_a = ComputePhaseIncrement(pitch_ + detune_integral);
    int32_t increment_b = ComputePhaseIncrement(pitch_ + detune_integral + 1);
    increments[i] = increment_a + \
        (((increment_b - increment_a) * detune_fractional) >> 16);
  }
  if (strike_) {
    for (size_t i = 0; i < 6; ++i) {
      state_.saw.phase[i] = Random::GetWord();
    }
    strike_ = false;
  }
  int32_t hp_cutoff = pitch_;
  if (parameter_[1] < 10922) {
    hp_cutoff += ((parameter_[1] - 10922) * 24) >> 5;
  } else {
    hp_cutoff += ((parameter_[1] - 10922) * 12) >> 5;
  }
  if (hp_cutoff < 0) {
    hp_cutoff = 0;
  } else if (hp_cutoff > 32767) {
    hp_cutoff = 32767;
  }
  
  int32_t f = Interpolate824(lut_svf_cutoff, hp_cutoff << 17);
  int32_t damp = lut_svf_damp[0];
  fm1_filters_render_swarm(&phase_, state_.saw.phase, increments, f, damp, &state_.saw.bp, &state_.saw.lp,
                           sync, buffer, size);
}

void DigitalOscillator::RenderComb(
    const uint8_t* sync,
     int16_t* buffer,
     size_t size) {
  // Filter the delay time to avoid clicks/glitches.
  int32_t pitch = pitch_ + ((parameter_[0] - 16384) >> 1);
  int32_t filtered_pitch = state_.ffm.previous_sample;
  filtered_pitch = (15 * filtered_pitch + pitch) >> 4;
  state_.ffm.previous_sample = filtered_pitch;
  
  int16_t* dl = delay_lines_.comb;
  uint32_t delay = ComputeDelay(filtered_pitch);
  if (delay > (kCombDelayLength << 16)) {
    delay = kCombDelayLength << 16;
  }
  uint32_t delay_integral = delay >> 16;
  int32_t delay_fractional = delay & 0xffff;

  // Warp the resonance curve to have a more precise adjustment in the extrema.
  int32_t resonance = fm1_physical_comb_resonance(parameter_[1]);
  uint32_t delay_ptr = phase_ % kCombDelayLength;
  fm1_physical_render_comb(dl, &delay_ptr, delay_integral, delay_fractional, resonance, buffer, size);
  phase_ = delay_ptr;
}

void DigitalOscillator::RenderToy(
    const uint8_t* sync,
    int16_t* buffer,
    size_t size) {
  // 4 times oversampling.
  phase_increment_ >>= 2;
  fm1_digital_render_toy(&phase_, &state_.toy.held_sample, &state_.toy.decimation_counter, phase_increment_,
                         512 - (parameter_[0] >> 6), parameter_[1] >> 8, sync, buffer, size);
}
 
const uint32_t kPhaseReset[] = {
  0,
  0x80000000,
  0x40000000,
  0x80000000
};

void DigitalOscillator::RenderDigitalFilter(
    const uint8_t* sync,
    int16_t* buffer,
    size_t size) {
  int16_t shifted_pitch = pitch_ + ((parameter_[0] - 2048) >> 1);
  if (shifted_pitch > 16383) {
    shifted_pitch = 16383;
  }
  uint8_t filter_type = shape_ - OSC_SHAPE_DIGITAL_FILTER_LP;
  uint32_t modulator_phase_increment = state_.res.modulator_phase_increment;
  uint32_t target_increment = ComputePhaseIncrement(shifted_pitch);
  uint32_t modulator_phase_increment_increment =
    modulator_phase_increment < target_increment
    ? (target_increment - modulator_phase_increment) / size
    : ~((modulator_phase_increment - target_increment) / size);
  uint8_t polarity = state_.res.polarity;
  fm1_filters_render_digital_filter(&phase_, phase_increment_, &state_.res.modulator_phase,
                                    &state_.res.modulator_phase_increment, modulator_phase_increment_increment,
                                    &state_.res.square_modulator_phase, &state_.res.integrator, &polarity,
                                    filter_type, parameter_[1], sync, buffer, size);
  state_.res.polarity = polarity;
}

void DigitalOscillator::RenderVosim(
    const uint8_t* sync,
    int16_t* buffer,
    size_t size) {
  for (size_t i = 0; i < 2; ++i) {
    state_.vow.formant_increment[i] = ComputePhaseIncrement(parameter_[i] >> 1);
  }
  fm1_filters_render_vosim(&phase_, phase_increment_, state_.vow.formant_phase, state_.vow.formant_increment,
                           sync, buffer, size);
}

struct PhonemeDefinition {
  uint8_t formant_frequency[3];
  uint8_t formant_amplitude[3];
};

static const PhonemeDefinition vowels_data[9] = {
    { { 27,  40,  89 }, { 15,  13,  1 } },
    { { 18,  51,  62 }, { 13,  12,  6 } },
    { { 15,  69,  93 }, { 14,  12,  7 } },
    { { 10,  84, 110 }, { 13,  10,  8 } },
    { { 23,  44,  87 }, { 15,  12,  1 } },
    { { 13,  29,  80 }, { 13,   8,  0 } },
    { {  6,  46,  81 }, { 12,   3,  0 } },
    { {  9,  51,  95 }, { 15,   3,  0 } },
    { {  6,  73,  99 }, {  7,   3,  14 } }
};

static const PhonemeDefinition consonant_data[8] = {
    { { 6, 54, 121 }, { 9,  9,  0 } },
    { { 18, 50, 51 }, { 12,  10,  5 } },
    { { 11, 24, 70 }, { 13,  8,  0 } },
    { { 15, 69, 74 }, { 14,  12,  7 } },
    { { 16, 37, 111 }, { 14,  8,  1 } },
    { { 18, 51, 62 }, { 14,  12,  6 } },
    { { 6, 26, 81 }, { 5,  5,  5 } },
    { { 6, 73, 99 }, { 7,  10,  14 } },
};


void DigitalOscillator::RenderVowel(
    const uint8_t* sync,
    int16_t* buffer,
    size_t size) {
  size_t vowel_index = parameter_[0] >> 12;
  uint16_t balance = parameter_[0] & 0x0fff;
  uint16_t formant_shift = (200 + (parameter_[1] >> 6));
  if (strike_) {
    strike_ = false;
    state_.vow.consonant_frames = 160;
    uint16_t index = (Random::GetSample() + 1) & 7;
    for (size_t i = 0; i < 3; ++i) {
      state_.vow.formant_increment[i] = \
          static_cast<uint32_t>(consonant_data[index].formant_frequency[i]) * \
          0x1000 * formant_shift;
      state_.vow.formant_amplitude[i] = consonant_data[index].formant_amplitude[i];
    }
    state_.vow.noise = index >= 6 ? 4095 : 0;
  }
  
  if (state_.vow.consonant_frames) {
    --state_.vow.consonant_frames;
  } else {
    for (size_t i = 0; i < 3; ++i) {
      state_.vow.formant_increment[i] = 
          (vowels_data[vowel_index].formant_frequency[i] * (0x1000 - balance) + \
           vowels_data[vowel_index + 1].formant_frequency[i] * balance) * \
           formant_shift;
      state_.vow.formant_amplitude[i] =
          (vowels_data[vowel_index].formant_amplitude[i] * (0x1000 - balance) + \
           vowels_data[vowel_index + 1].formant_amplitude[i] * balance) >> 12;
    }
    state_.vow.noise = 0;
  }
  fm1_vowels_render_vowel(&phase_, phase_increment_, state_.vow.formant_phase, state_.vow.formant_increment,
                          state_.vow.formant_amplitude, state_.vow.noise, buffer, size);
}

static const int16_t formant_f_data[kNumFormants][kNumFormants][kNumFormants] = {
  // bass
  {
    { 9519, 10738, 12448, 12636, 12892 }, // a
    { 8620, 11720, 12591, 12932, 13158 }, // e
    { 7579, 11891, 12768, 13122, 13323 }, // i
    { 8620, 10013, 12591, 12768, 13010 }, // o
    { 8324, 9519, 12591, 12831, 13048 } // u
  },
  // tenor
  {
    { 9696, 10821, 12810, 13010, 13263 }, // a
    { 8620, 11827, 12768, 13228, 13477 }, // e
    { 7908, 12038, 12932, 13263, 13452 }, // i
    { 8620, 10156, 12768, 12932, 13085 }, // o
    { 8324, 9519, 12852, 13010, 13296 } // u
  },
  // countertenor
  {
    { 9730, 10902, 12892, 13085, 13330 }, // a
    { 8832, 11953, 12852, 13085, 13296 }, // e
    { 7749, 12014, 13010, 13330, 13483 }, // i
    { 8781, 10211, 12852, 13085, 13296 }, // o
    { 8448, 9627, 12892, 13085, 13363 } // u
  },
  // alto
  {
    { 10156, 10960, 12932, 13427, 14195 }, // a
    { 8620, 11692, 12852, 13296, 14195 }, // e
    { 8324, 11827, 12852, 13550, 14195 }, // i
    { 8881, 10156, 12956, 13427, 14195 }, // o
    { 8160, 9860, 12708, 13427, 14195 } // u
  },
  // soprano
  {
    { 10156, 10960, 13010, 13667, 14195 }, // a
    { 8324, 12187, 12932, 13489, 14195 }, // e
    { 7749, 12337, 13048, 13667, 14195 }, // i
    { 8881, 10156, 12956, 13609, 14195 }, // o
    { 8160, 9860, 12852, 13609, 14195 } // u
  }
};

static const int16_t formant_a_data[kNumFormants][kNumFormants][kNumFormants] = {
  // bass
  {
    { 16384, 7318, 5813, 5813, 1638 }, // a
    { 16384, 4115, 5813, 4115, 2062 }, // e
    { 16384, 518, 2596, 1301, 652 }, // i
    { 16384, 4617, 1460, 1638, 163 }, // o
    { 16384, 1638, 411, 652, 259 } // u
  },
  // tenor
  {
    { 16384, 8211, 7318, 6522, 1301 }, // a
    { 16384, 3269, 4115, 3269, 1638 }, // e
    { 16384, 2913, 2062, 1638, 518 }, // i
    { 16384, 5181, 4115, 4115, 821 }, // o
    { 16384, 1638, 2314, 3269, 821 } // u
  },
  // countertenor
  {
    { 16384, 8211, 1159, 1033, 206 }, // a
    { 16384, 3269, 2062, 1638, 1638 }, // e
    { 16384, 1033, 1033, 259, 259 }, // i
    { 16384, 5181, 821, 1301, 326 }, // o
    { 16384, 1638, 1159, 518, 326 } // u
  },
  // alto
  {
    { 16384, 10337, 1638, 259, 16 }, // a
    { 16384, 1033, 518, 291, 16 }, // e
    { 16384, 1638, 518, 259, 16 }, // i
    { 16384, 5813, 2596, 652, 29 }, // o
    { 16384, 4115, 518, 163, 10 } // u
  },
  // soprano
  {
    { 16384, 8211, 411, 1638, 51 }, // a
    { 16384, 1638, 2913, 163, 25 }, // e
    { 16384, 4115, 821, 821, 103 }, // i
    { 16384, 4617, 1301, 1301, 51 }, // o
    { 16384, 2596, 291, 163, 16 } // u
  }
};

int16_t DigitalOscillator::InterpolateFormantParameter(
    const int16_t table[][kNumFormants][kNumFormants],
    int16_t x,
    int16_t y,
    uint8_t formant) {
  uint16_t x_index = x >> 13;
  uint16_t x_mix = x << 3;
  uint16_t y_index = y >> 13;
  uint16_t y_mix = y << 3;
  int16_t a = table[x_index][y_index][formant];
  int16_t b = table[x_index + 1][y_index][formant];
  int16_t c = table[x_index][y_index + 1][formant];
  int16_t d = table[x_index + 1][y_index + 1][formant];
  a = a + ((b - a) * x_mix >> 16);
  c = c + ((d - c) * x_mix >> 16);
  return a + ((c - a) * y_mix >> 16);
}

void DigitalOscillator::RenderVowelFof(
  const uint8_t* sync,
  int16_t* buffer,
  size_t size) {

  // The original implementation used FOF but we live in the future and it's
  // less computationally expensive to render a proper bank of 5 SVF.

  int16_t amplitudes[kNumFormants];
  int32_t svf_lp[kNumFormants];
  int32_t svf_bp[kNumFormants];
  int16_t svf_f[kNumFormants];
  
  for (size_t i = 0; i < kNumFormants; ++i) {
    int32_t frequency = InterpolateFormantParameter(
        formant_f_data,
        parameter_[1],
        parameter_[0],
        i) + (12 << 7);
    svf_f[i] = Interpolate824(lut_svf_cutoff, frequency << 17);
    amplitudes[i] = InterpolateFormantParameter(
        formant_a_data,
        parameter_[1],
        parameter_[0],
        i);
    if (init_) {
      svf_lp[i] = 0;
      svf_bp[i] = 0;
    } else {
      svf_lp[i] = state_.fof.svf_lp[i];
      svf_bp[i] = state_.fof.svf_bp[i];
    }
  }
  
  if (init_) {
    init_ = false;
  }
  int32_t svf_f32[kNumFormants];
  for (size_t i = 0; i < kNumFormants; ++i) {
    svf_f32[i] = svf_f[i];
  }
  fm1_vowels_render_fof(&phase_, &state_.fof.previous_sample, &state_.fof.next_saw_sample, phase_increment_ << 1,
                        svf_lp, svf_bp, svf_f32, amplitudes[0], buffer, size);
  for (size_t i = 0; i < kNumFormants; ++i) {
    state_.fof.svf_lp[i] = svf_lp[i];
    state_.fof.svf_bp[i] = svf_bp[i];
  }
}

void DigitalOscillator::RenderFm(
    const uint8_t* sync,
    int16_t* buffer,
    size_t size) {
  uint32_t modulator_phase_increment = ComputePhaseIncrement(
      (12 << 7) + pitch_ + ((parameter_[1] - 16384) >> 1)) >> 1;
  fm1_digital_render_fm(&phase_, &state_.modulator_phase, phase_increment_, modulator_phase_increment,
                        previous_parameter_[0], parameter_[0], sync, buffer, size);
  previous_parameter_[0] = parameter_[0];
}

void DigitalOscillator::RenderFeedbackFm(
    const uint8_t* sync,
    int16_t* buffer,
    size_t size) {
  int32_t attenuation = pitch_ - (72 << 7) + ((parameter_[1] - 16384) >> 1);
  attenuation = 32767 - attenuation * 4;
  if (attenuation < 0) attenuation = 0;
  if (attenuation > 32767) attenuation = 32767;
  uint32_t modulator_phase_increment = ComputePhaseIncrement(
      (12 << 7) + pitch_ + ((parameter_[1] - 16384) >> 1)) >> 1;
  fm1_digital_render_feedback_fm(&phase_, &state_.ffm.modulator_phase, &state_.ffm.previous_sample, phase_increment_,
                                 modulator_phase_increment, attenuation, previous_parameter_[0], parameter_[0],
                                 sync, buffer, size);
  previous_parameter_[0] = parameter_[0];
}

void DigitalOscillator::RenderChaoticFeedbackFm(
    const uint8_t* sync,
    int16_t* buffer,
    size_t size) {
  uint32_t modulator_phase_increment = ComputePhaseIncrement(
      (12 << 7) + pitch_ + ((parameter_[1] - 16384) >> 1)) >> 1;
  fm1_digital_render_chaotic_fm(&phase_, &state_.ffm.modulator_phase, &state_.ffm.previous_sample, phase_increment_,
                                modulator_phase_increment, previous_parameter_[0], parameter_[0], sync, buffer, size);
  previous_parameter_[0] = parameter_[0];
}


static const int16_t kBellPartials[] = {
  -1284, -1283, -184, -183, 385, 1175, 1536, 2233, 2434, 2934, 3110
};

static const int16_t kBellPartialAmplitudes[] = {
  8192, 5488, 8192, 14745, 21872, 13680, 11960, 10895, 10895, 6144, 10895
};

static const uint16_t kBellPartialDecayLong[] = {
  65533, 65533, 65533, 65532, 65531, 65531, 65530, 65529, 65527, 65523, 65519
};

static const uint16_t kBellPartialDecayShort[] = {
  65308, 65283, 65186, 65123, 64839, 64889, 64632, 64409, 64038, 63302, 62575
};

static const int16_t kDrumPartials[] = {
  0, 0, 1041, 1747, 1846, 3072
};

static const int16_t kDrumPartialAmplitude[] = {
  16986, 2654, 3981, 5308, 3981, 2985
};

static const uint16_t kDrumPartialDecayLong[] = {
  65533, 65531, 65531, 65531, 65531, 65516
};

static const uint16_t kDrumPartialDecayShort[] = {
  65083, 64715, 64715, 64715, 64715, 62312
};

void DigitalOscillator::RenderStruckBell(
    const uint8_t* sync,
    int16_t* buffer,
    size_t size) {
  
  // To save some CPU cycles, do not refresh the frequency of all partials at
  // the same time. This create a kind of "arpeggiation" with high frequency
  // CV though...
  size_t first_partial = state_.add.current_partial;
  size_t last_partial = std::min(
      state_.add.current_partial + 3,
      kNumBellPartials);
  state_.add.current_partial = (first_partial + 3) % kNumBellPartials;
  
  if (strike_) {
    for (size_t i = 0; i < kNumBellPartials; ++i) {
      state_.add.partial_amplitude[i] = kBellPartialAmplitudes[i];
      state_.add.partial_phase[i] = (1L << 30);
    }
    strike_ = false;
    first_partial = 0;
    last_partial = kNumBellPartials;
  }
  
  for (size_t i = first_partial; i < last_partial; ++i) {
    int16_t partial_pitch = pitch_ + kBellPartials[i];
    if (i & 1) {
      partial_pitch += parameter_[1] >> 7;
    } else {
      partial_pitch -= parameter_[1] >> 7;
    }
    state_.add.partial_phase_increment[i] = \
        ComputePhaseIncrement(partial_pitch) << 1;
  }
  
  // Allow a "droning" bell with no energy loss when the parameter is set to
  // its maximum value
  if (parameter_[0] < 32000) {
    for (size_t i = 0; i < kNumBellPartials; ++i) {
      state_.add.partial_amplitude[i] = fm1_percussion_decay(
          state_.add.partial_amplitude[i], kBellPartialDecayLong[i], kBellPartialDecayShort[i], parameter_[0]);
    }
  }
  fm1_percussion_render_bell(state_.add.partial_phase, state_.add.partial_phase_increment,
                             state_.add.partial_amplitude, &state_.add.previous_sample, buffer, size);
}

void DigitalOscillator::RenderHarmonics(
    const uint8_t* sync,
    int16_t* buffer,
    size_t size) {
  uint32_t phase_increment = phase_increment_ << 1;
  int32_t target_amplitude[kNumAdditiveHarmonics];
  
  int32_t peak = (kNumAdditiveHarmonics * parameter_[0]) >> 7;
  int32_t second_peak = (peak >> 1) + kNumAdditiveHarmonics * 128;
  int32_t second_peak_amount = parameter_[1] * parameter_[1] >> 15;

  int32_t sqrtsqrt_width = parameter_[1] < 16384
      ? parameter_[1] >> 6 : 511 - (parameter_[1] >> 6);
  int32_t sqrt_width = sqrtsqrt_width * sqrtsqrt_width >> 10;
  int32_t width = sqrt_width * sqrt_width + 4;
  int32_t total = 0;
  for (size_t i = 0; i < kNumAdditiveHarmonics; ++i) {
    int32_t x = i << 8;
    int32_t d, g;

    d = (x - peak);
    g = 32768 * 128 / (128 + d * d / width);
    
    d = (x - second_peak);
    g += second_peak_amount * 128 / (128 + d * d / width);
    total += g;
    target_amplitude[i] = g;
  }
  
  int32_t attenuation = 2147483647 / total;
  for (size_t i = 0; i < kNumAdditiveHarmonics; ++i) {
    if ((phase_increment >> 16) * (i + 1) > 0x4000) {
      target_amplitude[i] = 0;
    } else {
      target_amplitude[i] = target_amplitude[i] * attenuation >> 16;
    }
  }
  fm1_filters_render_harmonics(&phase_, &state_.add.previous_sample, phase_increment, state_.hrm.amplitude,
                               target_amplitude, sync, buffer, size);
}

void DigitalOscillator::RenderStruckDrum(
    const uint8_t* sync,
    int16_t* buffer,
    size_t size) {
  
  if (strike_) {
    bool reset_phase = state_.add.partial_amplitude[0] < 1024;
    for (size_t i = 0; i < kNumDrumPartials; ++i) {
      state_.add.target_partial_amplitude[i] = kDrumPartialAmplitude[i];
      if (reset_phase) {
        state_.add.partial_phase[i] = (1L << 30);
      }
    }
    strike_ = false;
  } else {
    if (parameter_[0] < 32000) {
      for (size_t i = 0; i < kNumDrumPartials; ++i) {
        state_.add.target_partial_amplitude[i] = fm1_percussion_decay(
            state_.add.partial_amplitude[i], kDrumPartialDecayLong[i], kDrumPartialDecayShort[i], parameter_[0]);
      }
    }
  }
  
  for (size_t i = 0; i < kNumDrumPartials; ++i) {
    int16_t partial_pitch = pitch_ + kDrumPartials[i];
    state_.add.partial_phase_increment[i] = ComputePhaseIncrement(partial_pitch) << 1;
  }
  
  int32_t cutoff = (pitch_ - 12 * 128) + (parameter_[1] >> 2);
  if (cutoff < 0) {
    cutoff = 0;
  } else if (cutoff > 32767) {
    cutoff = 32767;
  }
  int32_t f = Interpolate824(lut_svf_cutoff, cutoff << 16);
  int32_t harmonics_gain = parameter_[1] < 12888 ? (parameter_[1] + 4096) : 16384;
  int32_t noise_mode_gain = parameter_[1] < 16384 ? 0 : parameter_[1] - 16384;
  noise_mode_gain = noise_mode_gain * 12888 >> 14;
  fm1_percussion_render_drum(state_.add.partial_phase, state_.add.partial_phase_increment,
                             state_.add.partial_amplitude, state_.add.target_partial_amplitude, state_.add.lp_noise,
                             f, noise_mode_gain, harmonics_gain, &state_.add.previous_sample, buffer, size);
  for (size_t i = 0; i < kNumBellPartials; ++i) {
    AdditiveState* a = &state_.add;
    a->partial_amplitude[i] = a->target_partial_amplitude[i];
  }
}

void DigitalOscillator::RenderPlucked(
    const uint8_t* sync,
    int16_t* buffer,
    size_t size) {
  phase_increment_ <<= 1;
  if (strike_) {
    ++active_voice_;
    if (active_voice_ >= kNumPluckVoices) {
      active_voice_ = 0;
    }
    // Find the optimal oversampling rate.
    PluckState* p = &state_.plk[active_voice_];
    int32_t increment = phase_increment_;
    p->shift = 0;
    while (increment > (2 << 22)) {
      increment >>= 1;
      ++p->shift;
    }
    p->size = 1024 >> p->shift;
    p->mask = p->size - 1;
    p->write_ptr = 0;
    p->max_phase_increment = phase_increment_ << 1;
    p->phase_increment = phase_increment_;
    int32_t width = parameter_[1];
    width = (3 * width) >> 1;
    p->initialization_ptr = p->size * (8192 + width) >> 16;
    strike_ = false;
  }
  
  PluckState* current_string = &state_.plk[active_voice_];
  
  // Update the phase increment of the latest note, but do not transpose too
  // high above the original pitch.
  current_string->phase_increment = std::min(
      phase_increment_,
      current_string->max_phase_increment);
  
  // Compute loss and stretching factors.
  uint32_t update_probability = parameter_[0] < 16384
      ? 65535
      : 131072 - (parameter_[0] >> 3) * 31;
  int16_t loss = 4096 - (phase_increment_ >> 14);
  if (loss < 256) {
    loss = 256;
  }
  if (parameter_[0] < 16384) {
    loss = loss * (16384 - parameter_[0]) >> 14;
  } else {
    loss = 0;
  }
  
  fm1_pluck_voice voices[kNumPluckVoices];
  for (size_t i = 0; i < kNumPluckVoices; ++i) {
    PluckState* p = &state_.plk[i];
    voices[i].dl = delay_lines_.ks + i * 1025;
    voices[i].phase = p->phase;
    voices[i].phase_increment = p->phase_increment;
    voices[i].shift = p->shift;
    voices[i].mask = p->mask;
    voices[i].size = p->size;
    voices[i].write_ptr = p->write_ptr;
    voices[i].initialization_ptr = p->initialization_ptr;
  }
  fm1_physical_render_plucked(voices, kNumPluckVoices, update_probability, loss, &state_.plk[0].previous_sample,
                              buffer, size);
  for (size_t i = 0; i < kNumPluckVoices; ++i) {
    PluckState* p = &state_.plk[i];
    p->phase = voices[i].phase;
    p->write_ptr = voices[i].write_ptr;
    p->initialization_ptr = voices[i].initialization_ptr;
  }
}

void DigitalOscillator::RenderBowed(
    const uint8_t* sync,
    int16_t* buffer,
    size_t size) {
  int8_t* dl_b = delay_lines_.bowed.bridge;
  int8_t* dl_n = delay_lines_.bowed.neck;
  
  if (strike_) {
    memset(dl_b, 0, sizeof(delay_lines_.bowed.bridge));
    memset(dl_n, 0, sizeof(delay_lines_.bowed.neck));
    memset(&state_, 0, sizeof(state_));
    strike_ = false;
  }
  int16_t parameter_0 = 172 - (parameter_[0]  >> 8);
  int16_t parameter_1 = 6 + (parameter_[1]  >> 9);

  // Setup delay times and interpolation coefficients.
  uint32_t delay = (delay_ >> 1) - (2 << 16);  // Compensation for 1-pole delay
  uint32_t bridge_delay = (delay >> 8) * parameter_1;
  // Transpose one octave up when the note is too low to fit in the delays.
  while ((delay - bridge_delay) > ((kWGNeckLength - 1) << 16)
         || bridge_delay > ((kWGBridgeLength - 1) << 16)) {
    delay >>= 1;
    bridge_delay >>= 1;
  }
  fm1_pipe_state state;
  state.delay_ptr = state_.phy.delay_ptr;
  state.excitation_ptr = state_.phy.excitation_ptr;
  state.lp = state_.phy.lp_state;
  state.filter0 = state_.phy.filter_state[0];
  state.filter1 = state_.phy.filter_state[1];
  state.previous = state_.phy.previous_sample;
  phase_ += phase_increment_ * (size >> 1);
  fm1_physical_render_bowed(dl_b, dl_n, &state, bridge_delay, delay - bridge_delay, parameter_0, buffer, size);
  uint16_t excitation_ptr = state.excitation_ptr;
  if ((excitation_ptr >> 1) >= LUT_BOWING_ENVELOPE_SIZE - 32) {
    excitation_ptr = (LUT_BOWING_ENVELOPE_SIZE - 32) << 1;
  }
  state_.phy.delay_ptr = state.delay_ptr % kWGNeckLength;
  state_.phy.excitation_ptr = excitation_ptr;
  state_.phy.lp_state = state.lp;
  state_.phy.filter_state[0] = state.filter0;
  state_.phy.filter_state[1] = state.filter1;
  state_.phy.previous_sample = state.previous;
}

void DigitalOscillator::RenderBlown(
    const uint8_t* sync,
    int16_t* buffer,
    size_t size) {
  int16_t* dl = delay_lines_.bore;
  if (strike_) {
    memset(dl, 0, sizeof(delay_lines_.bore));
    strike_ = false;
  }

  uint32_t delay = (delay_ >> 1) - (1 << 16);
  while (delay > ((kWGBoreLength - 1) << 16)) {
    delay >>= 1;
  }
  uint16_t parameter = 28000 - (parameter_[0] >> 1);
  int16_t normalized_pitch = (pitch_ - 8192 + (parameter_[1] >> 1)) >> 7;
  if (normalized_pitch < 0) {
    normalized_pitch = 0;
  } else if (normalized_pitch > 127) {
    normalized_pitch = 127;
  }
  uint16_t filter_coefficient = lut_flute_body_filter[normalized_pitch];
  fm1_pipe_state state;
  state.delay_ptr = state_.phy.delay_ptr;
  state.excitation_ptr = 0;
  state.lp = state_.phy.lp_state;
  state.filter0 = state_.phy.filter_state[0];
  state.filter1 = 0;
  state.previous = 0;
  phase_ += phase_increment_ * size;
  fm1_physical_render_blown(dl, &state, delay, parameter, filter_coefficient, buffer, size);
  state_.phy.filter_state[0] = state.filter0;
  state_.phy.delay_ptr = state.delay_ptr % kWGBoreLength;
  state_.phy.lp_state = state.lp;
}

void DigitalOscillator::RenderFluted(
    const uint8_t* sync,
    int16_t* buffer,
    size_t size) {
  int8_t* dl_b = delay_lines_.fluted.bore;
  int8_t* dl_j = delay_lines_.fluted.jet;
  
  if (strike_) {
    state_.phy.excitation_ptr = 0;
    memset(dl_b, 0, sizeof(delay_lines_.fluted.bore));
    memset(dl_j, 0, sizeof(delay_lines_.fluted.jet));
    state_.phy.lp_state = 0;
    strike_ = false;
  }

  // Setup delay times and interpolation coefficients.
  uint32_t bore_delay = (delay_ << 1) - (2 << 16);
  uint32_t jet_delay = (bore_delay >> 8) * (48 + (parameter_[1]  >> 10));
  bore_delay -= jet_delay;
  while (bore_delay > ((kWGFBoreLength - 1) << 16)
         || jet_delay > ((kWGJetLength - 1) << 16)) {
    bore_delay >>= 1;
    jet_delay >>= 1;
  }
  uint16_t breath_intensity = 2100 - (parameter_[0] >> 4);
  uint16_t filter_coefficient = lut_flute_body_filter[pitch_ >> 7];
  fm1_pipe_state state;
  state.delay_ptr = state_.phy.delay_ptr;
  state.excitation_ptr = state_.phy.excitation_ptr;
  state.lp = state_.phy.lp_state;
  state.filter0 = state_.phy.filter_state[0];
  state.filter1 = state_.phy.filter_state[1];
  state.previous = 0;
  phase_ += phase_increment_ * size;
  fm1_physical_render_fluted(dl_b, dl_j, &state, bore_delay, jet_delay, breath_intensity, filter_coefficient,
                             buffer, size);
  uint16_t excitation_ptr = state.excitation_ptr;
  if (excitation_ptr >= LUT_BLOWING_ENVELOPE_SIZE - 32) {
    excitation_ptr = LUT_BLOWING_ENVELOPE_SIZE - 32;
  }
  state_.phy.delay_ptr = state.delay_ptr;
  state_.phy.excitation_ptr = excitation_ptr;
  state_.phy.lp_state = state.lp;
  state_.phy.filter_state[0] = state.filter0;
  state_.phy.filter_state[1] = state.filter1;
}

struct WavetableDefinition {
  uint8_t num_steps;
  uint8_t wave_index[17];
};

static const WavetableDefinition wavetable_definitions[] = {
// 01 male
{ 16 , { 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 15 } },
// 02 female
{ 16 , { 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 31 } },
// 03 choir
{ 16 , { 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 47 } },
// 04 space_voice
{ 16 , { 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 63 } },
// 05 tampura
{ 16 , { 64, 65, 66, 67, 68, 68, 69, 70, 71, 72, 73, 73, 74, 75, 75, 76, 76 } },
// 06 shamus
{ 16 , { 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 92 } },
// 07 swept_string
{ 16 , { 93, 94, 95, 96, 97, 98, 99, 100, 101,
         102, 103, 104, 105, 106, 107, 108, 108 } },
// 08 bowed
{ 16 , { 109, 110, 111, 112, 113, 114, 115, 116,
         117, 118, 119, 120, 121, 122, 123, 124, 124 } },
// 09 cello
{ 16 , { 125, 126, 127, 128, 129, 130, 131, 132,
         132, 132, 132, 132, 132, 132, 132, 132, 132 } },
// 10 vibes
{ 16 , { 133, 134, 135, 136, 137, 138, 139, 140,
         141, 142, 143, 144, 144, 144, 145, 145, 145 } },
// 11 slap
{ 16 , { 146, 147, 148, 149, 150, 151, 151, 151,
         152, 152, 152, 152, 153, 153, 153, 153, 153 } },
// 12 piano
{ 8 , { 154, 154, 154, 154, 154, 154, 155, 156, 156 } },
// 13 organ!
{ 16 , { 176, 157, 158, 159, 160, 161, 162, 163,
         164, 165, 166, 167, 168, 169, 170, 171, 171 } },
// 14 waves!
{ 16 , { 172, 173, 174, 175, 176, 177, 178, 179,
         180, 181, 182, 183, 184, 185, 186, 187, 187 } },
// 15 digital
{ 16 , { 176, 188, 189, 190, 191, 192, 193, 194,
         195, 196, 197, 198, 199, 200, 201, 202, 202 } },
// 16 drone 1
{ 16 , { 203, 205, 204, 205, 212, 206, 207, 208,
         208, 209, 210, 210, 211, 211, 212, 212, 212 } },
// 17 drone 2
{ 8 , { 213, 213, 213, 214, 215, 216, 217, 218, 219 } },
// 18 metallic
{ 16 , { 220, 221, 222, 223, 224, 225, 226, 227,
         228, 229, 230, 231, 232, 233, 234, 235, 235 } },
// 19 fantasy
{ 16 , { 236, 237, 238, 239, 240, 241, 242, 243,
         244, 245, 246, 247, 248, 249, 250, 251, 251 } },
// 20 bell
{ 4 , { 252, 253, 254, 255, 254 } },
};

void DigitalOscillator::RenderWavetables(
    const uint8_t* sync,
    int16_t* buffer,
    size_t size) {
  // Add some hysteresis to the second parameter to prevent a single DAC bit
  // error to cause a sharp and glitchy wavetable transition.
  if ((parameter_[1] > previous_parameter_[1] + 64) ||
      (parameter_[1] < previous_parameter_[1] - 64)) {
    previous_parameter_[1] = parameter_[1];
  }
      
  uint32_t wavetable_index = static_cast<uint32_t>(previous_parameter_[1]) * 20;
  wavetable_index >>= 15;
  
  const WavetableDefinition& wt = wavetable_definitions[wavetable_index];
  uint32_t wave_pointer = (parameter_[0] << 1) * wt.num_steps;
  uint32_t wave_a = wt.wave_index[(wave_pointer >> 16)];
  uint32_t wave_b = wt.wave_index[(wave_pointer >> 16) + 1];
  fm1_wavetables_render_table(&phase_, phase_increment_ >> 1, wave_a, wave_b, wave_pointer & 0xffff, sync, buffer,
                              size);
}

void DigitalOscillator::RenderWaveMap(
    const uint8_t* sync,
    int16_t* buffer,
    size_t size) {
  // The grid is 16x16; so there are 15 interpolation squares.
  uint16_t p[2];
  uint16_t wave_xfade[2];
  uint16_t wave_coordinate[2];

  p[0] = parameter_[0] * 15 >> 4;
  p[1] = parameter_[1] * 15 >> 4;
  wave_xfade[0] = p[0] << 5;
  wave_xfade[1] = p[1] << 5;
  wave_coordinate[0] = p[0] >> 11;
  wave_coordinate[1] = p[1] >> 11;

  uint32_t waves[4];
  for (size_t i = 0; i < 2; ++i) {
    for (size_t j = 0; j < 2; ++j) {
      uint16_t wave_index = \
          (wave_coordinate[0] + i) * 16 + (wave_coordinate[1] + j);
      waves[i * 2 + j] = wt_map[wave_index];
    }
  }
  fm1_wavetables_render_map(&phase_, phase_increment_ >> 1, waves, wave_xfade[0], wave_xfade[1], sync, buffer, size);
}

static const uint8_t wave_line[] = {
  187, 179, 154, 155, 135, 134, 137, 19, 24, 3, 8, 66, 79, 25, 180, 174, 64,
  127, 198, 15, 10, 7, 11, 0, 191, 192, 115, 238, 237, 236, 241, 47, 70, 76,
  235, 26, 133, 208, 34, 175, 183, 146, 147, 148, 150, 151, 152, 153, 117,
  138, 32, 33, 35, 125, 199, 201, 30, 31, 193, 27, 29, 21, 18, 182
};


static const uint8_t mini_wave_line[] = {
  157, 161, 171, 188, 189, 191, 192, 193, 196, 198, 201, 234, 232,
  229, 226, 224, 1, 2, 3, 4, 5, 8, 12, 32, 36, 42, 47, 252, 254, 141, 139,
  135, 174
};

void DigitalOscillator::RenderWaveLine(
    const uint8_t* sync,
    int16_t* buffer,
    size_t size) {
  smoothed_parameter_ = (3 * smoothed_parameter_ + (parameter_[0] << 1)) >> 2;

  uint16_t scan = smoothed_parameter_;
  uint32_t wave_0 = wave_line[previous_parameter_[0] >> 9];
  uint32_t wave_1 = wave_line[scan >> 10];
  uint32_t wave_2 = wave_line[(scan >> 10) + 1];

  uint16_t smooth_xfade = scan << 6;
  uint16_t rough_xfade_increment = 32768 / size;
  uint32_t balance = parameter_[1] << 3;
  uint32_t mode = parameter_[1] < 8192 ? 0 : parameter_[1] < 16384 ? 1 : parameter_[1] < 24576 ? 2 : 3;
  fm1_wavetables_render_line(&phase_, phase_increment_ >> 1, wave_0, wave_1, wave_2, smooth_xfade,
                             rough_xfade_increment, balance, mode, sync, buffer, size);
  previous_parameter_[0] = smoothed_parameter_ >> 1;
}

#define SEMI * 128

static const uint16_t chords[17][3] = {
  { 2, 4, 6 },
  { 16, 32, 48 },
  { 2 SEMI, 7 SEMI, 12 SEMI },
  { 3 SEMI, 7 SEMI, 10 SEMI },
  { 3 SEMI, 7 SEMI, 12 SEMI },
  { 3 SEMI, 7 SEMI, 14 SEMI },
  { 3 SEMI, 7 SEMI, 17 SEMI },
  { 7 SEMI, 12 SEMI, 19 SEMI },
  { 7 SEMI, 3 + 12 SEMI, 5 + 19 SEMI },
  { 4 SEMI, 7 SEMI, 17 SEMI },
  { 4 SEMI, 7 SEMI, 14 SEMI },
  { 4 SEMI, 7 SEMI, 12 SEMI },
  { 4 SEMI, 7 SEMI, 11 SEMI },
  { 5 SEMI, 7 SEMI, 12 SEMI },
  { 4, 7 SEMI, 12 SEMI },
  { 4, 4 + 12 SEMI, 12 SEMI },
  { 4, 4 + 12 SEMI, 12 SEMI },
};

void DigitalOscillator::RenderWaveParaphonic(
    const uint8_t* sync,
    int16_t* buffer,
    size_t size) {
  if (strike_) {
    for (size_t i = 0; i < 4; ++i) {
      state_.saw.phase[i] = Random::GetWord();
    }
    strike_ = false;
  }
  
  uint32_t phase_increment[4];
  phase_increment[0] = phase_increment_;
  
  uint16_t chord_integral = parameter_[1] >> 11;
  uint16_t chord_fractional = parameter_[1] << 5;
  if (chord_fractional < 30720) {
    chord_fractional = 0;
  } else if (chord_fractional >= 34816) {
    chord_fractional = 65535;
  } else {
    chord_fractional = (chord_fractional - 30720) * 16;
  }
  
  for (size_t i = 0; i < 3; ++i) {
    uint16_t detune_1 = chords[chord_integral][i];
    uint16_t detune_2 = chords[chord_integral + 1][i];
    uint16_t detune = detune_1 + ((detune_2 - detune_1) * chord_fractional >> 16);
    phase_increment[i + 1] = ComputePhaseIncrement(pitch_ + detune);
  }

  uint32_t wave_1 = mini_wave_line[parameter_[0] >> 10];
  uint32_t wave_2 = mini_wave_line[(parameter_[0] >> 10) + 1];
  uint16_t wave_xfade = parameter_[0] << 6;
  fm1_wavetables_render_paraphonic(state_.saw.phase, phase_increment, wave_1, wave_2, wave_xfade, buffer, size);
}

void DigitalOscillator::RenderFilteredNoise(
    const uint8_t* sync,
    int16_t* buffer,
    size_t size) {
  int32_t f = Interpolate824(lut_svf_cutoff, pitch_ << 17);
  int32_t damp = Interpolate824(lut_svf_damp, parameter_[0] << 17);
  int32_t scale = Interpolate824(lut_svf_scale, parameter_[0] << 17);
  int32_t bp_gain, lp_gain, hp_gain;
  
  // Morph between LP, BP, HP.
  if (parameter_[1] < 16384) {
    bp_gain = parameter_[1];
    lp_gain = 16384 - bp_gain;
    hp_gain = 0;
  } else {
    bp_gain = 32767 - parameter_[1];
    hp_gain = parameter_[1] - 16384;
    lp_gain = 0;
  }
  
  int32_t gain_correction = f > scale ? scale * 32767 / f : 32767;
  fm1_noise_render_filtered(&state_.svf.lp, &state_.svf.bp, f, damp, lp_gain, bp_gain, hp_gain, gain_correction,
                            buffer, size);
}

void DigitalOscillator::RenderTwinPeaksNoise(
    const uint8_t* sync,
    int16_t* buffer,
    size_t size) {
  uint32_t q = 65240 + (parameter_[0] >> 7);
  int32_t q_squared = q * q >> 17;
  int16_t p1 = pitch_;

  CONSTRAIN(p1, 0, 16383)
  int32_t c1 = Interpolate824(lut_resonator_coefficient, p1 << 17);
  int32_t s1 = Interpolate824(lut_resonator_scale, p1 << 17);
  
  int16_t p2 = pitch_ + ((parameter_[1] - 16384) >> 1);
  CONSTRAIN(p2, 0, 16383)
  int32_t c2 = Interpolate824(lut_resonator_coefficient, p2 << 17);
  int32_t s2 = Interpolate824(lut_resonator_scale, p2 << 17);

  c1 = c1 * q >> 16;
  c2 = c2 * q >> 16;

  int32_t makeup_gain = 8191 - (parameter_[0] >> 2);
  fm1_noise_render_twin_peaks(&state_.pno.filter_state[0][0], s1, c1, s2, c2, q_squared, makeup_gain, buffer, size);
}

void DigitalOscillator::RenderClockedNoise(
    const uint8_t* sync,
    int16_t* buffer,
    size_t size) {
  ClockedNoiseState* state = &state_.clk;
  
  if ((parameter_[1] > previous_parameter_[1] + 64) ||
      (parameter_[1] < previous_parameter_[1] - 64)) {
    previous_parameter_[1] = parameter_[1];
  }
  if ((parameter_[0] > previous_parameter_[0] + 16) ||
      (parameter_[0] < previous_parameter_[0] - 16)) {
    previous_parameter_[0] = parameter_[0];
  }
  
  
  if (strike_) {
    state->seed = Random::GetWord();
    strike_ = false;
  }
  
  // Shift the range of the Coarse knob to reach higher clock rates, close
  // to the sample rate.
  uint32_t phase = phase_;
  uint32_t phase_increment = phase_increment_;
  for (size_t i = 0; i < 3; ++i) {
    if (phase_increment < (1UL << 31)) {
      phase_increment <<= 1;
    }
  }
  
  // Compute the period of the random generator.
  state->cycle_phase_increment = ComputePhaseIncrement(
      previous_parameter_[0] - 16384) << 1;
  
  // Compute the number of quantization steps
  uint32_t num_steps = 1 + (previous_parameter_[1] >> 10);
  if (num_steps == 1) {
    num_steps = 2;
  }
  uint32_t quantizer_divider = 65536 / num_steps;
  fm1_noise_render_clocked(&phase, phase_increment, &state->rng_state, &state->cycle_phase,
                           state->cycle_phase_increment, state->seed, &state->sample, quantizer_divider, sync, buffer,
                           size);
  phase_ = phase;
}

void DigitalOscillator::RenderGranularCloud(
    const uint8_t* sync,
    int16_t* buffer,
    size_t size) {
  
  for (size_t i = 0; i < 4; ++i) {
    Grain* g = &state_.grain[i];
    // If a grain has reached the end of its envelope, reset it.
    if (g->envelope_phase > (1 << 24) ||
        g->envelope_phase_increment == 0) {
      g->envelope_phase_increment = 0;
      if ((Random::GetWord() & 0xffff) < 0x4000) {
        g->envelope_phase_increment = \
            lut_granular_envelope_rate[parameter_[0] >> 7] << 3;
        g->envelope_phase = 0;
        g->phase_increment = phase_increment_;
        int32_t pitch_mod = Random::GetSample() * parameter_[1] >> 16;
        int32_t phi = phase_increment_ >> 8;
        if (pitch_mod < 0) {
          g->phase_increment += phi * (pitch_mod >> 8);
        } else {
          g->phase_increment += phi * (pitch_mod >> 7);
        }
      }
    }
  }
  
  fm1_noise_render_cloud(&state_.grain[0].phase, buffer, size);
}

void DigitalOscillator::RenderParticleNoise(
    const uint8_t* sync,
    int16_t* buffer,
    size_t size) {
  uint32_t density = 1024 + parameter_[0];
  fm1_noise_render_particle(&state_.pno.amplitude, &state_.pno.filter_state[0][0], state_.pno.filter_scale,
                            state_.pno.filter_coefficient, density, pitch_, parameter_[1], buffer, size);
}


void DigitalOscillator::RenderDigitalModulation(
    const uint8_t* sync,
    int16_t* buffer,
    size_t size) {
  uint32_t symbol_stream_phase_increment = ComputePhaseIncrement(
      pitch_ - 1536 + ((parameter_[0] - 32767) >> 3));
  if (strike_) {
    state_.dmd.symbol_count = 0;
    strike_ = false;
  }
  fm1_digital_render_modulation(&phase_, &state_.dmd.symbol_phase, &state_.dmd.symbol_count,
                                &state_.dmd.filter_state, &state_.dmd.data_byte, phase_increment_,
                                symbol_stream_phase_increment, parameter_[1], buffer, size);
}

void DigitalOscillator::RenderQuestionMark(
    const uint8_t* sync,
    int16_t* buffer,
    size_t size) {
  ClockedNoiseState* state = &state_.clk;
  
  if (strike_) {
    state->rng_state = 0;
    state->cycle_phase = 0;
    state->sample = 10;
    state->cycle_phase_increment = -1;
    state->seed = 32767;
    strike_ = false;
  }
  
  uint32_t dit_duration = 3600 + ((32767 - parameter_[0]) >> 2);
  int32_t noise_threshold = 1024 + (parameter_[1] >> 3);
  int16_t length = state->sample;
  fm1_vowels_render_question(&phase_, phase_increment_, &state->cycle_phase, &state->cycle_phase_increment,
                             &state->rng_state, &state->seed, &length, dit_duration, noise_threshold, parameter_[1],
                             buffer, size);
  state->sample = length;
}

void DigitalOscillator::RenderKick(
    const uint8_t* sync,
    int16_t* buffer,
    size_t size) {
  if (init_) {
    pulse_[0].Init();
    pulse_[0].set_delay(0);
    pulse_[0].set_decay(3340);

    pulse_[1].Init();
    pulse_[1].set_delay(1.0e-3 * 48000);
    pulse_[1].set_decay(3072);

    pulse_[2].Init();
    pulse_[2].set_delay(4.0e-3 * 48000);
    pulse_[2].set_decay(4093);

    svf_[0].Init();
    svf_[0].set_punch(32768);
    svf_[0].set_mode(SVF_MODE_BP);
    init_ = false;
  }
  
  if (strike_) {
    strike_ = false;
    pulse_[0].Trigger(12 * 32768 * 0.7);
    pulse_[1].Trigger(-19662 * 0.7);
    pulse_[2].Trigger(18000);
    svf_[0].set_punch(24000);
  }
  
  uint32_t decay = parameter_[0];
  uint32_t scaled = 65535 - (decay << 1);
  uint32_t squared = scaled * scaled >> 16;
  scaled = squared * scaled >> 18;
  svf_[0].set_resonance(32768 - 128 - scaled);
  
  uint32_t coefficient = parameter_[1];
  coefficient = coefficient * coefficient >> 15;
  coefficient = coefficient * coefficient >> 15;
  int32_t lp_coefficient = 128 + (coefficient >> 1) * 3;
  fm1_excite_regs pulse[3];
  fm1_svf_regs svf;
  for (size_t i = 0; i < 3; ++i) {
    pulse_[i].Export(&pulse[i]);
  }
  svf_[0].Export(&svf);
  fm1_percussion_render_kick(pulse, &svf, &state_.svf.lp, pitch_, lp_coefficient, buffer, size);
  for (size_t i = 0; i < 3; ++i) {
    pulse_[i].Import(pulse[i]);
  }
  svf_[0].Import(svf);
}

void DigitalOscillator::RenderSnare(
    const uint8_t* sync,
    int16_t* buffer,
    size_t size) {
  if (init_) {
    pulse_[0].Init();
    pulse_[0].set_delay(0);
    pulse_[0].set_decay(1536);

    pulse_[1].Init();
    pulse_[1].set_delay(1e-3 * 48000);
    pulse_[1].set_decay(3072);

    pulse_[2].Init();
    pulse_[2].set_delay(1e-3 * 48000);
    pulse_[2].set_decay(1200);
  
    pulse_[3].Init();
    pulse_[3].set_delay(0);
  
    svf_[0].Init();

    svf_[1].Init();

    svf_[2].Init();
    svf_[2].set_resonance(2000);
    svf_[2].set_mode(SVF_MODE_BP);

    init_ = false;
  }
  
  if (strike_) {
    int32_t decay = 49152 - pitch_;
    decay += parameter_[1] < 16384 ? 0 : parameter_[1] - 16384;
    if (decay > 65535) {
      decay = 65535;
    }
    svf_[0].set_resonance(29000 + (decay >> 5));
    svf_[1].set_resonance(26500 + (decay >> 5));
    pulse_[3].set_decay(4092 + (decay >> 14));
    
    pulse_[0].Trigger(15 * 32768);
    pulse_[1].Trigger(-1 * 32768);
    pulse_[2].Trigger(13107);
    int32_t snappy = parameter_[1];
    if (snappy >= 14336) {
      snappy = 14336;
    }
    pulse_[3].Trigger(512 + (snappy << 1));
    strike_ = false;
  }
  
  svf_[0].set_frequency(pitch_ + (12 << 7));
  svf_[1].set_frequency(pitch_ + (24 << 7));
  svf_[2].set_frequency(pitch_ + (60 << 7));
  
  int32_t g_1 = 22000 - (parameter_[0] >> 1);
  int32_t g_2 = 22000 + (parameter_[0] >> 1);
  fm1_excite_regs pulse[4];
  fm1_svf_regs svf[3];
  for (size_t i = 0; i < 4; ++i) {
    pulse_[i].Export(&pulse[i]);
  }
  for (size_t i = 0; i < 3; ++i) {
    svf_[i].Export(&svf[i]);
  }
  fm1_percussion_render_snare(pulse, svf, g_1, g_2, buffer, size);
  for (size_t i = 0; i < 4; ++i) {
    pulse_[i].Import(pulse[i]);
  }
  for (size_t i = 0; i < 3; ++i) {
    svf_[i].Import(svf[i]);
  }
}

void DigitalOscillator::RenderCymbal(
    const uint8_t* sync,
    int16_t* buffer,
    size_t size) {
  if (init_) {
    svf_[0].Init();
    svf_[0].set_mode(SVF_MODE_BP);
    svf_[0].set_resonance(12000);
    svf_[1].Init();
    svf_[1].set_mode(SVF_MODE_HP);
    svf_[1].set_resonance(2000);
    init_ = false;
  }
  
  HatState* hat = &state_.hat;

  uint32_t increments[7];
  int32_t note = (40 << 7) + (pitch_ >> 1);
  increments[0] = ComputePhaseIncrement(note);
  
  uint32_t root = increments[0] >> 10;
  increments[1] = root * 24273 >> 4;
  increments[2] = root * 12561 >> 4;
  increments[3] = root * 18417 >> 4;
  increments[4] = root * 22452 >> 4;
  increments[5] = root * 31858 >> 4;
  increments[6] = increments[0] * 24;

  int32_t xfade = parameter_[1];
  svf_[0].set_frequency(parameter_[0] >> 1);
  svf_[1].set_frequency(parameter_[0] >> 1);
  fm1_svf_regs svf[2];
  svf_[0].Export(&svf[0]);
  svf_[1].Export(&svf[1]);
  fm1_percussion_render_cymbal(&phase_, hat->phase, &hat->rng_state, increments, svf, xfade, buffer, size);
  svf_[0].Import(svf[0]);
  svf_[1].Import(svf[1]);
}

/*
void DigitalOscillator::RenderYourAlgo(
    const uint8_t* sync,
    int16_t* buffer,
    size_t size) {
  while (size--) {
    *buffer++ = 0;
  }
}
*/

/* static */
DigitalOscillator::RenderFn DigitalOscillator::fn_table_[] = {
  &DigitalOscillator::RenderTripleRingMod,
  &DigitalOscillator::RenderSawSwarm,
  &DigitalOscillator::RenderComb,
  &DigitalOscillator::RenderToy,
  &DigitalOscillator::RenderDigitalFilter,
  &DigitalOscillator::RenderDigitalFilter,
  &DigitalOscillator::RenderDigitalFilter,
  &DigitalOscillator::RenderDigitalFilter,
  &DigitalOscillator::RenderVosim,
  &DigitalOscillator::RenderVowel,
  &DigitalOscillator::RenderVowelFof,
  &DigitalOscillator::RenderHarmonics,
  &DigitalOscillator::RenderFm,
  &DigitalOscillator::RenderFeedbackFm,
  &DigitalOscillator::RenderChaoticFeedbackFm,
  &DigitalOscillator::RenderPlucked,
  &DigitalOscillator::RenderBowed,
  &DigitalOscillator::RenderBlown,
  &DigitalOscillator::RenderFluted,
  &DigitalOscillator::RenderStruckBell,
  &DigitalOscillator::RenderStruckDrum,
  &DigitalOscillator::RenderKick,
  &DigitalOscillator::RenderCymbal,
  &DigitalOscillator::RenderSnare,
  &DigitalOscillator::RenderWavetables,
  &DigitalOscillator::RenderWaveMap,
  &DigitalOscillator::RenderWaveLine,
  &DigitalOscillator::RenderWaveParaphonic,
  &DigitalOscillator::RenderFilteredNoise,
  &DigitalOscillator::RenderTwinPeaksNoise,
  &DigitalOscillator::RenderClockedNoise,
  &DigitalOscillator::RenderGranularCloud,
  &DigitalOscillator::RenderParticleNoise,
  &DigitalOscillator::RenderDigitalModulation,
  // &DigitalOscillator::RenderYourAlgo,

  &DigitalOscillator::RenderQuestionMark
};

}  // namespace braids

extern "C" uint16_t fm1_braids_ws_moderate_overdrive(uint32_t index) {
  return static_cast<uint16_t>(braids::ws_moderate_overdrive[index]);
}
