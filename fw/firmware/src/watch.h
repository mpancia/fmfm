/* The proofs, watched. The theorems in Proofs/ are about the Lean; the C that calls it (this file's voices,
 * clock and glue) and the compiler are trusted. In the simulator and host builds, the statements of a dozen of
 * those theorems are also checked on the running machine, at the point the C consumes the Lean's answer: every
 * note a lane starts is in its scale, note-ons and note-offs balance, the mix never leaves the proved bound, a
 * swung quarter note is exactly 24 straight ticks, a plain lane plays exactly its hits a bar, a saved patch
 * decodes to the same bytes. A violation here could only come from the trusted parts (the C handed the Lean
 * something the theorem's hypotheses exclude, or the compiled code is not the definition), which is exactly
 * what the proofs cannot see. The simulator page shows the counters; tools/smoke_web.mjs fails on any
 * violation. On the chip none of this is compiled. */
#if defined(DINGHY_WEB) || defined(DINGHY_HOST)
#define WATCHED 1
enum {
    W_NOTE_IN_SCALE, W_NOTE_ON_OFF, W_NOTE_ON_HIT, W_BAR_HITS, W_MIX_BOUNDED, W_PAN_NO_GAIN, W_SWING_TICK,
    W_SWING_QUARTER, W_CHORD_ROOT, W_MASK_NONEMPTY, W_FOLLOW_IN_KEY, W_PATCH_ROUND_TRIP, W_COUNT
};
static struct { const char *theorem; uint32_t checks, fails; } watch[W_COUNT] = {
    {"lane_note_in_scale", 0, 0},            {"run_every_note_on_has_a_note_off", 0, 0},
    {"lane_note_only_on_hit", 0, 0},         {"run_bar_plays_every_hit", 0, 0},
    {"mix_machine_sample_bounded", 0, 0},    {"mix_pan_never_amplifies", 0, 0},
    {"swing_tick_in_range", 0, 0},           {"swing_quarter_note_exact", 0, 0},
    {"harmony_chord_root_in_key", 0, 0},     {"harmony_mask_never_empty", 0, 0},
    {"harmony_follow_in_key", 0, 0},         {"patch_decode_encode_round_trip", 0, 0},
};
#define WATCH(w, cond) do { watch[w].checks++; if (!(cond)) watch[w].fails++; } while (0)
/* what the C last gave each lane, so the checks can state the theorems' hypotheses */
static struct {
    uint32_t mask, hits, steps, feel, chance;
    uint32_t ons, offs;                     /* over the whole run */
    uint32_t bar_ons, bar_ok;               /* note-ons since the last bar end; a whole bar has run unchanged */
} wlane[4];
static void watch_lane_set(uint32_t i, uint32_t mask, uint32_t hits, uint32_t steps, uint32_t feel, uint32_t chance)
{
    wlane[i].mask = mask; wlane[i].hits = hits < steps ? hits : steps; wlane[i].steps = steps;
    wlane[i].feel = feel; wlane[i].chance = chance; wlane[i].bar_ok = 0; wlane[i].bar_ons = 0;
}
#define WATCH_LANE_SET(i, mask, hits, steps, feel, chance) watch_lane_set(i, mask, hits, steps, feel, chance)
#define WATCH_LANE_RESET(i) (wlane[i].bar_ok = 0)
static uint32_t watch_quarter;              /* the tick lengths of the quarter note so far */
#else
#define WATCH(w, cond) ((void)0)
#define WATCH_LANE_SET(i, mask, hits, steps, feel, chance) ((void)0)
#define WATCH_LANE_RESET(i) ((void)0)
#endif
