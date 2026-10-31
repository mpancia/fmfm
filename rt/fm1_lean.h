/* SPDX-License-Identifier: GPL-3.0-only */
/* C view of the Lean code in the Firmware library: the functions marked @[export]. Lean passes every
 * argument of an exported function as OWNED: the call consumes the reference you give it. So:
 *     t = fm1_tracker_press(t, n);        // old t is consumed, new t returned: fine
 *     fm1_tracker_last(t)                 // would consume t: use the _of wrappers below to keep it
 * Keep this file in step with the @[export] names; the linker fails if one is missing. */
#pragma once
#include <lean/lean.h>

lean_object *fm1_tracker_new(lean_object *unit);                  /* pass lean_box(0) */
lean_object *fm1_tracker_press(lean_object *t, uint8_t note);
lean_object *fm1_tracker_release(lean_object *t, uint8_t note);
uint8_t fm1_tracker_last(lean_object *t);                         /* consumes t */
uint32_t fm1_tracker_count(lean_object *t);                       /* consumes t */
uint32_t fm1_phase_step(uint32_t phase, uint32_t step);

/* the same, keeping t */
static inline uint8_t fm1_tracker_last_of(lean_object *t) { lean_inc(t); return fm1_tracker_last(t); }
static inline uint32_t fm1_tracker_count_of(lean_object *t) { lean_inc(t); return fm1_tracker_count(t); }
