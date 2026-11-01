// SPDX-License-Identifier: GPL-3.0-only
// Entries of Braids' tables for the Lean code in Firmware/Physical.lean.
#include "braids/resources.h"

extern "C" uint16_t fm1_braids_lut_bowing_envelope(uint32_t index) {
  return braids::lut_bowing_envelope[index];
}

extern "C" uint16_t fm1_braids_lut_bowing_friction(uint32_t index) {
  return braids::lut_bowing_friction[index];
}

extern "C" uint16_t fm1_braids_lut_blowing_envelope(uint32_t index) {
  return braids::lut_blowing_envelope[index];
}

extern "C" uint16_t fm1_braids_lut_blowing_jet(uint32_t index) {
  return static_cast<uint16_t>(braids::lut_blowing_jet[index]);
}

extern "C" uint16_t fm1_braids_lut_flute_body_filter(uint32_t index) {
  return braids::lut_flute_body_filter[index];
}
