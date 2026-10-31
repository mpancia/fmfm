// SPDX-License-Identifier: GPL-3.0-only
// Braids' random number generator for the C loops in voices/*_glue.c, which pass the numbers to the Lean code.
#include "stmlib/utils/random.h"

extern "C" int16_t fm1_braids_random_sample(void) {
  return stmlib::Random::GetSample();
}

extern "C" uint32_t fm1_braids_random_word(void) {
  return stmlib::Random::GetWord();
}
