// SPDX-License-Identifier: GPL-3.0-only
// Differential test of the whole Braids voice: the firmware's (voices/braids, parts of it in Lean) against Braids'
// own C++ (tests/reference/, unchanged), all 48 shapes, random pitch and timbre with note strikes, then a long run at a steady pitch. Every output
// sample must be identical. This is the guard for every engine ported to Lean. Run by `make test-lean`.
#include <stdint.h>
#include <stdio.h>
#include <string.h>

extern "C" {
void *ref_voice_create(void);
void ref_voice_set(void *voice, int shape, int pitch, int timbre, int color);
void ref_voice_strike(void *voice);
void ref_voice_render(void *voice, int16_t *out, int count);
void *lean_voice_create(void);
void lean_voice_set(void *voice, int shape, int pitch, int timbre, int color);
void lean_voice_strike(void *voice);
void lean_voice_render(void *voice, int16_t *out, int count);
}

static uint32_t rng = 777;
static uint32_t rnd() { return rng = rng * 1664525u + 1013904223u; }

int main() {
  long samples = 0, mismatches = 0;
  int shapes_differing = 0;
  for (int shape = 0; shape < 48; shape++) {
    void *ref = ref_voice_create(), *lean = lean_voice_create();
    long bad = 0;
    for (int block = 0; block < 1500; block++) {
      if (block % 100 == 0) { ref_voice_strike(ref); lean_voice_strike(lean); }
      const int pitch = 24 * 128 + static_cast<int>(rnd() % (80 * 128));
      const int timbre = static_cast<int>(rnd() % 32768), color = static_cast<int>(rnd() % 32768);
      int16_t a[16], b[16];
      ref_voice_set(ref, shape, pitch, timbre, color);
      lean_voice_set(lean, shape, pitch, timbre, color);
      ref_voice_render(ref, a, 16);
      lean_voice_render(lean, b, 16);
      for (int i = 0; i < 16; i++) {
        samples++;
        if (a[i] != b[i]) { if (bad++ == 0) printf("shape %d first difference at block %d sample %d: %d vs %d\n", shape, block, i, a[i], b[i]); mismatches++; }
      }
    }
    // Then a long run at a steady high pitch, so the slow engines (the digital modulation's symbol stream) get
    // through whole cycles.
    for (int block = 0; block < 30000; block++) {
      if (block % 10000 == 0) { ref_voice_strike(ref); lean_voice_strike(lean); }
      static int timbre = 1000, color = 20000;
      if (block % 200 == 0) { timbre = static_cast<int>(rnd() % 32768); color = static_cast<int>(rnd() % 32768); }
      int16_t a[16], b[16];
      ref_voice_set(ref, shape, 84 * 128, timbre, color);
      lean_voice_set(lean, shape, 84 * 128, timbre, color);
      ref_voice_render(ref, a, 16);
      lean_voice_render(lean, b, 16);
      for (int i = 0; i < 16; i++) {
        samples++;
        if (a[i] != b[i]) { if (bad++ == 0) printf("shape %d first difference at block %d sample %d: %d vs %d\n", shape, block, i, a[i], b[i]); mismatches++; }
      }
    }
    // The question mark plays a long message of short and long beeps: run it past the end of the message (8240 dits of 3600 samples).
    if (shape == 47) {
      for (int block = 0; block < 2100000; block++) {
        int16_t a[16], b[16];
        ref_voice_set(ref, shape, 60 * 128, 32767, 3000);
        lean_voice_set(lean, shape, 60 * 128, 32767, 3000);
        ref_voice_render(ref, a, 16);
        lean_voice_render(lean, b, 16);
        for (int i = 0; i < 16; i++) {
          samples++;
          if (a[i] != b[i]) { if (bad++ == 0) printf("shape %d first difference at block %d sample %d: %d vs %d\n", shape, block, i, a[i], b[i]); mismatches++; }
        }
      }
    }
    if (bad) shapes_differing++;
  }
  printf("%ld samples over 48 shapes: %ld differ (%d shapes)\n", samples, mismatches, shapes_differing);
  return mismatches ? 1 : 0;
}
