// SPDX-License-Identifier: GPL-3.0-only
// Entries of Braids' tables for the Lean code in Firmware/Macro.lean.
#include "braids/resources.h"

extern "C" uint16_t fm1_braids_ws_violent_overdrive(uint32_t index) {
  return static_cast<uint16_t>(braids::ws_violent_overdrive[index]);
}
