// SPDX-License-Identifier: GPL-3.0-only
// Differential test of the Lean analog oscillators against Braids' own C++ (tests/reference/, unchanged).
// Both render the same shape with the same pitch, parameter and sync input, block after block, and every
// output sample and sync pulse must be identical. Run by `make test-analog`.
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

extern "C" {
void *ref_create(void);
void ref_render(void *osc, int shape, int pitch, int parameter, const uint8_t *sync_in, int16_t *out, uint8_t *sync_out,
                size_t size);
void *lean_create(void);
void lean_render(void *osc, int shape, int pitch, int parameter, const uint8_t *sync_in, int16_t *out,
                 uint8_t *sync_out, size_t size);
}

static double now() { timespec t; clock_gettime(CLOCK_MONOTONIC, &t); return t.tv_sec + t.tv_nsec * 1e-9; }
static uint32_t rng = 12345;
static uint32_t rnd() { return rng = rng * 1664525u + 1013904223u; }

int main() {
  const char *names[] = {"SAW", "VARIABLE_SAW", "CSAW", "SQUARE", "TRIANGLE", "SINE", "TRIANGLE_FOLD", "SINE_FOLD", "BUZZ"};
  const int shapes[] = {0, 1, 2, 3, 4, 5, 6, 7, 8};         // every analog shape
  long samples = 0, mismatches = 0, sync_mismatches = 0;
  double ref_time = 0, lean_time = 0;
  for (int shape : shapes) {
    void *ref = ref_create(), *lean = lean_create();
    long bad = 0;
    for (int block = 0; block < 6000; block++) {
      const size_t size = (rnd() & 1) ? 24 : 16;
      const int pitch = static_cast<int>(rnd() % (127 * 128));     // any note the engine can be given
      const int parameter = static_cast<int>(rnd() % 32768);
      uint8_t sync[24], sync_ref[24], sync_lean[24];
      const bool with_sync = (block % 3) != 0;
      for (size_t i = 0; i < size; i++) sync[i] = (with_sync && rnd() % 6 == 0) ? 1 + rnd() % 255 : 0;
      int16_t a[24], b[24];
      memset(sync_ref, 0, sizeof sync_ref); memset(sync_lean, 0, sizeof sync_lean);
      const bool want_sync_out = (block % 2) == 0;
      const double t0 = now();
      ref_render(ref, shape, pitch, parameter, sync, a, want_sync_out ? sync_ref : nullptr, size);
      const double t1 = now();
      lean_render(lean, shape, pitch, parameter, sync, b, want_sync_out ? sync_lean : nullptr, size);
      ref_time += t1 - t0; lean_time += now() - t1;
      for (size_t i = 0; i < size; i++) {
        samples++;
        if (a[i] != b[i]) { if (bad++ < 3) printf("%s block %d sample %zu: reference %d lean %d\n", names[shape], block, i, a[i], b[i]); mismatches++; }
        if (want_sync_out && sync_ref[i] != sync_lean[i]) { sync_mismatches++; if (sync_mismatches < 3) printf("%s sync pulse differs\n", names[shape]); }
      }
    }
    printf("%-9s %s\n", names[shape], bad ? "DIFFERS" : "identical");
  }
  printf("%ld samples, %ld sample mismatches, %ld sync mismatches\n", samples, mismatches, sync_mismatches);
  printf("render time: original %.1f ns/sample, Lean %.1f ns/sample\n", ref_time / samples * 1e9, lean_time / samples * 1e9);
  return mismatches || sync_mismatches ? 1 : 0;
}
