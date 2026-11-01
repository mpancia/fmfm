// SPDX-License-Identifier: GPL-3.0-only
// Entries of Braids' tables for the Lean code in Firmware/DigitalSetup.lean.
#include "braids/resources.h"

extern "C" uint16_t fm1_braids_lut_fm_frequency_quantizer(uint32_t index) {
  return braids::lut_fm_frequency_quantizer[index];
}

extern "C" uint32_t fm1_braids_lut_oscillator_delays(uint32_t index) {
  return braids::lut_oscillator_delays[index];
}
