// SPDX-License-Identifier: GPL-3.0-only
// Entries of Braids' tables for the Lean code in Firmware/Vowels.lean.
#include "braids/resources.h"

extern "C" uint16_t fm1_braids_formant_sine(uint32_t index) {
  return static_cast<uint16_t>(braids::wav_formant_sine[index]);
}

extern "C" uint16_t fm1_braids_formant_square(uint32_t index) {
  return static_cast<uint16_t>(braids::wav_formant_square[index]);
}

extern "C" uint8_t fm1_braids_vowels_wt_code(uint32_t index) {
  return braids::wt_code[index];
}
