// SPDX-License-Identifier: GPL-3.0-only
// Entries of Braids' tables for the Lean code in Firmware/Filters.lean.
#include "braids/resources.h"

extern "C" uint16_t fm1_braids_lut_bell(uint32_t index) {
  return braids::lut_bell[index];
}
