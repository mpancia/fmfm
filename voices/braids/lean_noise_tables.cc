// SPDX-License-Identifier: GPL-3.0-only
// Entries of Braids' tables for the Lean code in Firmware/Noise.lean.
#include "braids/resources.h"

extern "C" uint16_t fm1_braids_lut_resonator_coefficient(uint32_t index) {
  return braids::lut_resonator_coefficient[index];
}

extern "C" uint16_t fm1_braids_lut_resonator_scale(uint32_t index) {
  return braids::lut_resonator_scale[index];
}

extern "C" uint16_t fm1_braids_lut_granular_envelope(uint32_t index) {
  return braids::lut_granular_envelope[index];
}

extern "C" uint16_t fm1_braids_lut_svf_scale(uint32_t index) {
  return braids::lut_svf_scale[index];
}

extern "C" uint16_t fm1_braids_lut_granular_envelope_rate(uint32_t index) {
  return braids::lut_granular_envelope_rate[index];
}
