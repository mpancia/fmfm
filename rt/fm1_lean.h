/* SPDX-License-Identifier: GPL-3.0-only */
/* C view of the Lean code in the Firmware library: the functions marked @[export] in Firmware/LaneApi.lean.
 * Lean passes every argument of an exported function as OWNED: the call consumes the reference you give it.
 *     lane = fm1_lane_tick(lane);         old lane consumed, new one returned: right
 *     fm1_lane_step(lane)                 would consume the lane: use the _of wrappers below to keep it
 * Keep this file in step with the @[export] names; the linker fails if one is missing. */
#pragma once
#include <lean/lean.h>

lean_object *fm1_lane_make(uint32_t hits, uint32_t steps, uint32_t div, uint32_t mask, uint32_t low, uint32_t span,
                           uint32_t seed);
lean_object *fm1_lane_tick(lean_object *lane);
lean_object *fm1_lane_reconfigure(lean_object *lane, uint32_t hits, uint32_t steps, uint32_t div, uint32_t mask);
lean_object *fm1_lane_set_notes(lean_object *lane, uint32_t algo, uint32_t prob, uint32_t amount, uint32_t mutate);
lean_object *fm1_lane_silence(lean_object *lane);

/* Firmware/Harmony.lean: the scale a lane plays in (scale index, key, chord root, follow 0/1/2); never empty */
uint32_t fm1_harmony_mask(uint32_t scale, uint32_t key, uint32_t chord_root, uint32_t follow);

/* Firmware/Lfo.lean: scalar, safe in any context */
uint32_t fm1_lfo_advance(uint32_t phase, uint32_t step);
uint32_t fm1_lfo_modulate(uint32_t base, uint32_t depth, uint32_t phase);   /* base and depth in percent; the result too */

/* each consumes the lane */
uint32_t fm1_lane_on(lean_object *lane);            /* note the last tick started, 255 for none */
uint32_t fm1_lane_off(lean_object *lane);           /* note the last tick stopped, 255 for none */
uint32_t fm1_lane_step(lean_object *lane);
uint32_t fm1_lane_hit_at(lean_object *lane, uint32_t index);

/* the same, keeping the lane */
static inline uint32_t fm1_lane_on_of(lean_object *l) { lean_inc(l); return fm1_lane_on(l); }
static inline uint32_t fm1_lane_off_of(lean_object *l) { lean_inc(l); return fm1_lane_off(l); }
static inline uint32_t fm1_lane_step_of(lean_object *l) { lean_inc(l); return fm1_lane_step(l); }
static inline uint32_t fm1_lane_hit_at_of(lean_object *l, uint32_t i) { lean_inc(l); return fm1_lane_hit_at(l, i); }
