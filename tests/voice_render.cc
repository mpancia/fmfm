// SPDX-License-Identifier: GPL-3.0-only
// Render one Braids voice to raw 16-bit mono at 44.1 kHz on this computer (used by tools/audit_voices.py).
//   voice_render SHAPE TIMBRE COLOR NOTE SECONDS > out.raw
// Prints nothing but the samples, then the render time per sample on stderr.
#include <stdio.h>
#include <stdlib.h>
#include <time.h>

#include "voice.h"

int main(int argc, char **argv) {
  if (argc != 6) return 2;
  static uint8_t mem[BRAIDS_VOICE_BYTES] __attribute__((aligned(8)));
  const uint32_t shape = static_cast<uint32_t>(atoi(argv[1]));
  const int32_t timbre = atoi(argv[2]), color = atoi(argv[3]), note = atoi(argv[4]);
  const uint32_t total = static_cast<uint32_t>(atof(argv[5]) * 44100);
  static int16_t buffer[44100 * 8];
  if (total > sizeof buffer / sizeof buffer[0]) return 2;
  braids_voice_init(mem);
  braids_voice_set(mem, shape, note << 7, timbre, color);
  braids_voice_strike(mem);
  timespec start, end;
  clock_gettime(CLOCK_MONOTONIC, &start);
  for (uint32_t i = 0; i < total; i += BRAIDS_BLOCK) {
    const uint32_t count = i + BRAIDS_BLOCK <= total ? BRAIDS_BLOCK : total - i;
    braids_voice_render(mem, buffer + i, count);
  }
  clock_gettime(CLOCK_MONOTONIC, &end);
  fwrite(buffer, 2, total, stdout);
  fprintf(stderr, "%.1f\n", ((end.tv_sec - start.tv_sec) * 1e9 + (end.tv_nsec - start.tv_nsec)) / total);
  return 0;
}
