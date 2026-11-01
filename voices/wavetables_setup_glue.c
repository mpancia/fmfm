/* SPDX-License-Identifier: GPL-3.0-only */
/* The per-block setup of the Braids wavetable engines, with the arithmetic in Lean
 * (Firmware/WavetablesSetup.lean), included below as inline functions. voices/braids/digital_oscillator.cc calls
 * these once per block. */
#include <lean/lean.h>
#include <stdint.h>

#undef LEAN_EXPORT
#define LEAN_EXPORT static inline
#include "WavetablesSetupApi.c"

void fm1_wavetables_setup_table(int16_t param0, int16_t prev1, uint32_t *wave_a, uint32_t *wave_b,
                                uint32_t *balance)
{
    *wave_a = fm1_wavetables_setup_table_wave((uint16_t)param0, (uint16_t)prev1, 0);
    *wave_b = fm1_wavetables_setup_table_wave((uint16_t)param0, (uint16_t)prev1, 1);
    *balance = fm1_wavetables_setup_table_balance((uint16_t)param0, (uint16_t)prev1);
}

/* `waves` receives the square's four corners, row-major. */
void fm1_wavetables_setup_map(int16_t param0, int16_t param1, uint32_t *waves, uint32_t *xfade_x, uint32_t *xfade_y)
{
    uint32_t i, j;
    for (i = 0; i < 2; ++i)
        for (j = 0; j < 2; ++j)
            waves[i * 2 + j] = fm1_wavetables_setup_map_wave((uint16_t)param0, (uint16_t)param1, i, j);
    *xfade_x = fm1_wavetables_setup_map_xfade((uint16_t)param0);
    *xfade_y = fm1_wavetables_setup_map_xfade((uint16_t)param1);
}

/* `smoothed` is the smoothed parameter before the block and receives the value after it; `held` receives the
 * held parameter for the next block. */
void fm1_wavetables_setup_line(int32_t *smoothed, int16_t prev0, int16_t param0, int16_t param1, uint32_t size,
                               uint32_t *wave_0, uint32_t *wave_1, uint32_t *wave_2, uint32_t *smooth_xfade,
                               uint32_t *rough_step, uint32_t *balance, uint32_t *mode, int16_t *held)
{
    int32_t previous = *smoothed;
    *smoothed = fm1_wavetables_setup_line_smoothed(previous, (uint16_t)param0);
    *wave_0 = fm1_wavetables_setup_line_wave0((uint16_t)prev0);
    *wave_1 = fm1_wavetables_setup_line_wave(previous, (uint16_t)param0, 0);
    *wave_2 = fm1_wavetables_setup_line_wave(previous, (uint16_t)param0, 1);
    *smooth_xfade = fm1_wavetables_setup_line_smooth_xfade(previous, (uint16_t)param0);
    *rough_step = fm1_wavetables_setup_line_rough_step(size);
    *balance = fm1_wavetables_setup_line_balance((uint16_t)param1);
    *mode = fm1_wavetables_setup_line_mode((uint16_t)param1);
    *held = fm1_wavetables_setup_line_held(previous, (uint16_t)param0);
}

/* `inc` receives the four voices' phase steps: the oscillator's, then the three detuned ones. */
void fm1_wavetables_setup_paraphonic(int16_t pitch, uint32_t inc0, int16_t param0, int16_t param1, uint32_t *inc,
                                     uint32_t *wave_a, uint32_t *wave_b, uint32_t *xfade)
{
    uint32_t voice;
    inc[0] = inc0;
    for (voice = 0; voice < 3; ++voice)
        inc[voice + 1] = fm1_wavetables_setup_voice_increment((uint16_t)pitch, (uint16_t)param1, voice);
    *wave_a = fm1_wavetables_setup_mini_line_wave((uint16_t)param0, 0);
    *wave_b = fm1_wavetables_setup_mini_line_wave((uint16_t)param0, 1);
    *xfade = fm1_wavetables_setup_mini_line_xfade((uint16_t)param0);
}
