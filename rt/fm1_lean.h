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
lean_object *fm1_lane_set_rhythm(lean_object *lane, uint32_t kind, uint32_t rotate, uint32_t accents, uint32_t rule,
                                 uint32_t ratchet, uint32_t subhits, uint32_t reseed);
lean_object *fm1_lane_learn(lean_object *lane, uint32_t note);   /* a key the player pressed: STEP writes it, MARKOV counts it */
lean_object *fm1_lane_silence(lean_object *lane);

/* Firmware/Harmony.lean: the scale a lane plays in (scale index, key, chord root, follow 0/1/2); never empty */
uint32_t fm1_harmony_mask(uint32_t scale, uint32_t key, uint32_t chord_root, uint32_t follow);

/* Firmware/Lfo.lean: scalar, safe in any context */
uint32_t fm1_lfo_advance(uint32_t phase, uint32_t step);
uint32_t fm1_lfo_modulate(uint32_t base, uint32_t depth, uint32_t phase);   /* base and depth in percent; the result too */

/* Firmware/Mix.lean: scalar, used in the audio interrupt; Lean's Int32 and Int16 are uint32_t and uint16_t here,
 * cast at the call */
uint32_t fm1_mix_envelope_step(uint32_t amp, uint32_t gate, uint32_t up, uint32_t down);
uint32_t fm1_mix_voice_sample(uint16_t sample, uint16_t gain, uint32_t amp);   /* gain 256 = 1, amp 130048 = full */
uint32_t fm1_mix_send_sample(uint32_t s, uint16_t send);                      /* send 256 = all of it */
uint32_t fm1_mix_wet_sample(uint32_t wet, uint32_t gain);                     /* gain is Q15 */
uint32_t fm1_mix_limit(uint32_t mix);                                        /* within 524287: the master gain cannot wrap it */

/* each consumes the lane */
uint32_t fm1_lane_on(lean_object *lane);            /* note the last tick started, 255 for none */
uint32_t fm1_lane_off(lean_object *lane);           /* note the last tick stopped, 255 for none */
uint32_t fm1_lane_step(lean_object *lane);
uint32_t fm1_lane_hit_at(lean_object *lane, uint32_t index);
uint32_t fm1_lane_accent_at(lean_object *lane, uint32_t index);
uint32_t fm1_lane_loud(lean_object *lane);         /* 1 if the note the last tick started is accented */

/* the same, keeping the lane */
static inline uint32_t fm1_lane_on_of(lean_object *l) { lean_inc(l); return fm1_lane_on(l); }
static inline uint32_t fm1_lane_off_of(lean_object *l) { lean_inc(l); return fm1_lane_off(l); }
static inline uint32_t fm1_lane_step_of(lean_object *l) { lean_inc(l); return fm1_lane_step(l); }
static inline uint32_t fm1_lane_hit_at_of(lean_object *l, uint32_t i) { lean_inc(l); return fm1_lane_hit_at(l, i); }
static inline uint32_t fm1_lane_accent_at_of(lean_object *l, uint32_t i) { lean_inc(l); return fm1_lane_accent_at(l, i); }
static inline uint32_t fm1_lane_loud_of(lean_object *l) { lean_inc(l); return fm1_lane_loud(l); }

/* Firmware/PatchApi.lean: a user patch as 102 bytes for a flash slot (Proofs/Patch.lean: a patch the knobs can
 * produce loads back unchanged; anything else decodes to none). Every call consumes its object arguments. */
#define FM1_PATCH_BYTES 102u
lean_object *fm1_patch_lane_make(uint32_t hits, uint32_t steps, uint32_t speed, uint32_t scale, uint32_t sound,
                                 uint32_t low, uint32_t span, uint32_t algo, uint32_t chance, uint32_t amount,
                                 uint32_t mutate, uint32_t chord, uint32_t level, uint32_t send, uint32_t seed,
                                 uint32_t feel, uint32_t rotate, uint32_t accents, uint32_t rule, uint32_t ratchet,
                                 uint32_t subhits);
lean_object *fm1_patch_make(uint32_t bpm, uint32_t key, uint32_t progression, uint32_t rate, uint32_t scale_lock,
                            uint32_t reverb_time, uint32_t reverb_bright, uint32_t reverb_amount,
                            uint32_t delay_time, uint32_t delay_feedback, uint32_t delay_tone, uint32_t delay_amount,
                            lean_object *lane0, lean_object *lane1, lean_object *lane2, lean_object *lane3);
lean_object *fm1_patch_encode(lean_object *patch);             /* a ByteArray: lean_sarray_cptr, lean_sarray_size */
lean_object *fm1_patch_decode(lean_object *bytes);             /* Option: lean_is_scalar for none, else field 0 */
uint32_t fm1_patch_field(lean_object *patch, uint32_t index);  /* bpm, key, progression, rate, scale lock, reverb x3, delay x4 */
lean_object *fm1_patch_lane(lean_object *patch, uint32_t index);
uint32_t fm1_patch_lane_field(lean_object *lane, uint32_t index);   /* the patch_lane_t fields in order, seed, then the FEEL six */

/* the same, keeping the patch or lane */
static inline uint32_t fm1_patch_field_of(lean_object *p, uint32_t i) { lean_inc(p); return fm1_patch_field(p, i); }
static inline lean_object *fm1_patch_lane_of(lean_object *p, uint32_t i) { lean_inc(p); return fm1_patch_lane(p, i); }
static inline uint32_t fm1_patch_lane_field_of(lean_object *l, uint32_t i) { lean_inc(l); return fm1_patch_lane_field(l, i); }
