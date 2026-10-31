// SPDX-License-Identifier: GPL-3.0-only
// Entries of Braids' tables for the Lean code in Firmware/Percussion.lean.
#include "braids/resources.h"

extern "C" uint16_t fm1_braids_lut_svf_cutoff(uint32_t index) {
  return braids::lut_svf_cutoff[index];
}

extern "C" uint16_t fm1_braids_lut_svf_damp(uint32_t index) {
  return braids::lut_svf_damp[index];
}
