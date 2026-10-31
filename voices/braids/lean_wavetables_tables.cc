// SPDX-License-Identifier: GPL-3.0-only
// Entries of Braids' tables for the Lean code in Firmware/Wavetables.lean.
#include "braids/resources.h"

extern "C" uint8_t fm1_braids_wt_wave(uint32_t wave, uint32_t index) {
  return braids::wt_waves[wave * 129 + index];
}
