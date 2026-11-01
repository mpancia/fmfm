/* SPDX-License-Identifier: GPL-3.0-only */
/* FORMALFRED: a generative music box for the FM-1 (Alfred the butler is its mascot): four lanes, each a clock divider driving a Euclidean rhythm; a note
 * algorithm picks the pitches inside a range, a scale (or a chord) adjusts them, and Braids voices (voices/,
 * Mutable Instruments, MIT) play them. The lane logic is Lean (Firmware/Lane.lean, proved in Proofs/); this file
 * holds the sound, the controls and the screen. Derived from Dinghy (see UPSTREAM.md).
 *
 * Menu: the buttons HOME, SEQ, EDIT, GLO pick a group of pages; pressing the same one again moves to its next
 * page. Four knobs set the four values on screen. SELECT picks the lane, SEL mutes it, ALGORITHM sets the tempo.
 * PRESETS opens the browser: sounds in EDIT, patches elsewhere (SELECT then picks the family).
 * PLAY starts and stops, SAVE keeps the patch in a slot, REC rolls a new variation of the lane.
 *
 * Rules of the chip (no FPU, no 64-bit division): docs/RULES.md. Platform calls: docs/API.md. */
static void app_idle(void);
#define APP_NAME "FORMALFRED"              /* the rescue and the crash screen say this */
#define STORE_MAGIC 0x44524C41u                /* "ALRD": our settings never read as another firmware's */
#define LCD_IDLE app_idle
#include "platform.c"
#include "fm1_lean.h"
#include "voice.h"
#include "presets.h"
#include "theme.h"
#include "reverb.h"
#include "delay.h"
#include "alfred.h"
#ifndef ALFRED_LOOK
#define ALFRED_LOOK 5                           /* the look a fresh unit starts with (index into THEMES) */
#endif

/* ---- the sound (audio ISR: keep it short, no flash, no screen) */
#define NV 6u                                   /* voices */
static uint8_t vmem[NV][BRAIDS_VOICE_BYTES] __attribute__((aligned(8), section(".pool")));
static struct {
    volatile int32_t gate;                      /* target level: 0 = released */
    volatile int32_t pitch, timbre, color;      /* the voice's pitch (1/128 semitone) and its two timbre values */
    volatile uint16_t gain;                     /* levels the shapes out, 256 = 1 */
    volatile uint16_t send;                     /* how much goes to the reverb, 256 = all */
    volatile uint8_t shape, attack, release, env, strike;
    int32_t amp;                                /* the level now: glides to gate, no clicks */
    uint32_t age;
    uint8_t note;
} voice[NV];

static const int32_t ATTACK[4] = {1024, 256, 64, 12};              /* level steps a sample: 2 ms to 190 ms */
static const int32_t RELEASE[7] = {250, 80, 25, 10, 4, 2, 1};      /* 10 ms to 2.3 s */

static void render_voice(uint32_t v, int32_t *out, int32_t *bus, uint32_t n)
{
    int16_t block[BRAIDS_BLOCK];
    int32_t amp = voice[v].amp, g = voice[v].gate;
    const int32_t up = ATTACK[voice[v].attack & 3u], down = RELEASE[voice[v].release % 7u];
    uint32_t i, j;
    if (voice[v].strike) { voice[v].strike = 0; braids_voice_strike(vmem[v]); }
    for (i = 0; i < n; i += BRAIDS_BLOCK) {
        int32_t timbre = voice[v].timbre + ((amp * (int32_t)voice[v].env) >> 6);   /* brighter while loud */
        braids_voice_set(vmem[v], voice[v].shape, voice[v].pitch, timbre > 32767 ? 32767 : timbre, voice[v].color);
        braids_voice_render(vmem[v], block, BRAIDS_BLOCK);
        for (j = 0; j < BRAIDS_BLOCK; j++) {
            int32_t s;                                                    /* the arithmetic is Lean: Firmware/Mix.lean */
            amp = (int32_t)fm1_mix_envelope_step((uint32_t)amp, (uint32_t)g, (uint32_t)up, (uint32_t)down);
            s = (int32_t)fm1_mix_voice_sample((uint16_t)block[j], voice[v].gain, (uint32_t)amp);
            out[2u * (i + j)] += s;
            out[2u * (i + j) + 1u] += s;
            bus[i + j] += (int32_t)fm1_mix_send_sample((uint32_t)s, voice[v].send);   /* the send bus is left plus right */
        }
    }
    voice[v].amp = amp;
}

static int32_t send_bus[FM1_REVERB_BLOCK], wet_left[FM1_REVERB_BLOCK], wet_right[FM1_REVERB_BLOCK]
    __attribute__((section(".pool")));
static volatile uint32_t reverb_ready;          /* the reverb memory is cleared and the network may run */
static volatile int32_t reverb_return = 32768;  /* Q15 gain of the wet signal into the mix */
static volatile int32_t delay_return;           /* the same for the delay; the delay is off while it is 0 */

static void app_audio(int32_t *out, uint32_t n)
{
    uint32_t v, i;
    if (n > FM1_REVERB_BLOCK) n = FM1_REVERB_BLOCK;
    for (i = 0; i < n; i++) send_bus[i] = 0;
    for (v = 0; v < NV; v++)
        if (voice[v].amp || voice[v].gate)
            render_voice(v, out, send_bus, n);
    if (!reverb_ready) return;
    if (delay_return) {                         /* the echo, the same to both sides, before the reverb */
        const uint32_t gain = (uint32_t)delay_return;
        fm1_delay_block(send_bus, wet_left, n);
        for (i = 0; i < n; i++) {
            int32_t *l = &out[2u * i], *r = l + 1, w = (int32_t)fm1_mix_wet_sample((uint32_t)wet_left[i], gain);
            *l = (int32_t)fm1_mix_limit((uint32_t)(*l + w));
            *r = (int32_t)fm1_mix_limit((uint32_t)(*r + w));
        }
    }
    if (!reverb_return) return;
    fm1_reverb_block(send_bus, wet_left, wet_right, n);
    for (i = 0; i < n; i++) {
        const uint32_t gain = (uint32_t)reverb_return;
        int32_t *l = &out[2u * i], *r = l + 1;
        *l = (int32_t)fm1_mix_limit((uint32_t)(*l + (int32_t)fm1_mix_wet_sample((uint32_t)wet_left[i], gain)));
        *r = (int32_t)fm1_mix_limit((uint32_t)(*r + (int32_t)fm1_mix_wet_sample((uint32_t)wet_right[i], gain)));
    }
}

/* ---- notes (main loop) */
static uint32_t ages;

static void play(uint32_t note, uint32_t vel, const sound_t *sound, uint32_t send)
{
    uint32_t v, pick = 0, best = 0xFFFFFFFFu;
    if (note > 127u || !vel) return;
    for (v = 0; v < NV; v++) {                  /* the same note, else a free voice, else the oldest */
        uint32_t score = voice[v].note == note && voice[v].gate ? 0u
                       : voice[v].gate ? 0x80000000u + voice[v].age : (uint32_t)voice[v].amp + 1u;
        if (score < best) { best = score; pick = v; }
    }
    voice[pick].note = (uint8_t)note;
    voice[pick].age = ++ages;
    voice[pick].pitch = (int32_t)note << 7;
    voice[pick].timbre = sound->timbre;
    voice[pick].color = sound->color;
    voice[pick].gain = sound->gain;
    voice[pick].shape = sound->shape;
    voice[pick].attack = sound->attack;
    voice[pick].release = sound->release;
    voice[pick].env = sound->env;
    voice[pick].send = (uint16_t)(send * 256u / 100u);
    voice[pick].strike = 1;
    voice[pick].gate = (int32_t)(vel * 64u * 16u);   /* 127 at the top: six voices stay under full scale */
}
static void stop(uint32_t note)
{
    uint32_t v;
    for (v = 0; v < NV; v++)
        if (voice[v].note == note)
            voice[v].gate = 0;
}
static int quiet(void)                          /* nothing sounds, not even a release */
{
    uint32_t v;
    for (v = 0; v < NV; v++)
        if (voice[v].gate || voice[v].amp) return 0;
    return 1;
}

/* ---- the lanes and the patch */
#define NL 4u
static const char *const SCALE_NAME[] = {"MAJOR", "MINOR", "PENT+", "PENT-", "DORIAN", "H.MIN", "WHOLE", "CHROM",
                                         "PHRYG", "LYDIAN", "BLUES", "UKR.D", "DBL.H", "H.MAJ"};
#define NSCALE (sizeof SCALE_NAME / sizeof SCALE_NAME[0])
static const uint8_t SPEED[] = {2, 3, 4, 6, 8, 12, 16, 24};   /* clock ticks per step: 6 = sixteenth notes */
static const char *const SPEED_NAME[] = {"1/48", "1/32", "1/24", "1/16", "1/12", "1/8", "1/6", "1/4"};
#define NSPEED (sizeof SPEED / sizeof SPEED[0])
static const char *const ALGO_NAME[] = {"RANDOM", "WALK", "UP", "DOWN", "BOUNCE", "LOOP", "TURING", "STEP", "MARKOV", "GRAMMAR", "CHORD"};
/* what the NOTES page's second and third knobs mean for each algorithm ("" hides the knob) */
static const char *const ALGO_LABEL[][2] = {{"", ""}, {"STEP", ""}, {"", ""}, {"", ""}, {"", ""}, {"LENGTH", "MUTATE"},
                                            {"LENGTH", "FLIP"}, {"LENGTH", "MUTATE"}, {"STYLE", "JUMP"}, {"GRAMMAR", "DEPTH"},
                                            {"TONES", "OCTAVE"}};
static const char *const STYLE_NAME[] = {"STEPS", "LEAPS", "REPEATS", "ARCS"};
static const char *const GRAMMAR_NAME[] = {"FIBO", "CANTOR", "THUE", "ROUND"};
/* the rhythm sources (the FEEL page) and what its three other knobs mean for each */
static const char *const FEEL_NAME[] = {"EUCLID", "ROTATE", "AUTOMAT", "RATCHET"};
#define NFEEL (sizeof FEEL_NAME / sizeof FEEL_NAME[0])
static const char *const FEEL_LABEL[NFEEL][3] = {{"", "", ""}, {"ROTATE", "ACCENTS", ""}, {"RULE", "", ""}, {"RATCHET", "SUBHITS", ""}};
#define NALGO (sizeof ALGO_NAME / sizeof ALGO_NAME[0])
static const char *const CHORD_NAME[] = {"OFF", "SCALE", "TRIAD"};
static const char *const KEY_NAME[12] = {"C", "C#", "D", "D#", "E", "F", "F#", "G", "G#", "A", "A#", "B"};
/* chord progressions: semitones above the key, one chord a step; index 0 is no progression */
static const uint8_t PROGRESSION[][4] = {{0, 0, 0, 0}, {0, 5, 7, 0}, {0, 7, 9, 5}, {9, 5, 0, 7}, {2, 7, 0, 0},
                                         {0, 8, 3, 10}, {0, 4, 5, 7}, {0, 5, 7, 0}};
static const char *const PROGRESSION_NAME[] = {"OFF", "1-4-5-1", "1-5-6-4", "6-4-1-5", "2-5-1-1", "1-6-3-7", "1-3-4-5",
                                               "1-4-5 m"};   /* scale degrees of the chord roots; m: the minor set */
#define NPROGRESSION (sizeof PROGRESSION_NAME / sizeof PROGRESSION_NAME[0])
static const uint8_t RATE_BARS[] = {1, 2, 4};
static const uint16_t ATTACK_MS[4] = {2, 6, 25, 190};
static const uint16_t RELEASE_MS[7] = {10, 30, 90, 230, 580, 1200, 2300};
static const char *const FAMILY_NAME[] = {"ALL", "ANALOG", "FILTER", "VOICE", "FM", "PHYSICAL", "PERCUSSION", "WAVETABLE", "NOISE"};
static const uint8_t FAMILY_FIRST[] = {0, 0, 17, 21, 25, 28, 32, 37, 41}, FAMILY_LAST[] = {47, 16, 20, 24, 27, 31, 36, 40, 47};
#define NFAMILY (sizeof FAMILY_NAME / sizeof FAMILY_NAME[0])
static const char *const TYPE_NAME[] = {"ALL", "TONE", "PLUCK", "PAD", "DRUM"};     /* sound_t.type + 1 */
#define NTYPE (sizeof TYPE_NAME / sizeof TYPE_NAME[0])

static lean_object *lane[NL];
static struct {
    uint8_t hits, steps, speed, scale, low, span, preset, muted, algo, chance, amount, mutate, chord, level, send;
    uint8_t feel, rotate, accents, rule, ratchet, subhits;   /* the rhythm source: not in patches yet */
    uint16_t seed;
    sound_t sound;                              /* the lane's sound: a preset, then whatever the knobs changed */
} cfg[NL];
/* one slow modulator a lane (the LFO page): a triangle over RATE bars moves TARGET by up to DEPTH percent either way.
 * The modulated value lives in `live`; cfg keeps what the knobs set. Firmware/Lfo.lean does the arithmetic. */
static const char *const LFO_TARGET[] = {"OFF", "CHANCE", "LEVEL", "TIMBRE", "COLOUR"};
#define NLFO_TARGET (sizeof LFO_TARGET / sizeof LFO_TARGET[0])
static const uint8_t LFO_BARS[] = {1, 2, 4, 8, 16};
static struct {
    uint8_t target, rate, depth;                /* the knobs */
    uint32_t phase;
    uint8_t chance, level;                      /* live values the lane plays with */
    sound_t sound;
} lfo[NL];
static uint32_t reverb_time = 50, reverb_bright = 60, reverb_amount = 70;   /* the send reverb: decay, brightness, return */
static uint32_t delay_time = 6, delay_feedback = 40, delay_tone = 60, delay_amount;   /* the send delay: note value, feedback, tone, return */
static uint32_t delay_bpm;                      /* the tempo the delay line is tuned to */
static const char *const DELAY_TIME_NAME[FM1_DELAY_TIMES] = {"1/32", "1/16", "1/8T", "1/16.", "1/8", "1/4T", "1/8.", "1/4"};
static uint32_t bpm = 100, key, progression, rate_bars = 1, scale_lock, running = 1, tick_acc, tick_ms, tick_count, chord_index;
static uint32_t selected, patch_index, save_slot, midi_out_base;
static char patch_name[20] = "INIT";

#define NUSER 8u
#define NBROWSE (NPATCHES + NUSER)

static uint32_t chord_root(void) { return progression ? PROGRESSION[progression][chord_index & 3u] : 0u; }

static uint32_t lane_mask(uint32_t i)           /* the scale, turned to the key and the current chord: Firmware/Harmony.lean */
{
    uint32_t scale = scale_lock ? scale_lock - 1u : cfg[i].scale;
    uint32_t follow = progression ? cfg[i].chord : 0u;
    return fm1_harmony_mask(scale, key, chord_root(), follow);
}

static void lane_apply(uint32_t i)
{
    lane[i] = fm1_lane_reconfigure(lane[i], cfg[i].hits, cfg[i].steps, SPEED[cfg[i].speed], lane_mask(i));
    lane[i] = fm1_lane_set_notes(lane[i], cfg[i].algo, lfo[i].target ? lfo[i].chance : cfg[i].chance, cfg[i].amount, cfg[i].mutate);
    lane[i] = fm1_lane_set_rhythm(lane[i], cfg[i].feel, cfg[i].rotate, cfg[i].accents, cfg[i].rule, cfg[i].ratchet, cfg[i].subhits, 0);
}

static void lane_report(uint32_t i)             /* play what the lane just started, stop what it stopped */
{
    uint32_t off = fm1_lane_off_of(lane[i]), on = fm1_lane_on_of(lane[i]);
    if (off < 128u) { stop(off); midi_send(0x80u | (midi_out_base + i), off, 0); }
    if (on < 128u && !cfg[i].muted && lfo[i].level) {
        uint32_t vel = lfo[i].level;
        if (cfg[i].feel == 1u && cfg[i].accents) vel = fm1_lane_loud_of(lane[i]) ? vel : vel * 5u / 8u;   /* accents stand out */
        play(on, vel ? vel : 1u, &lfo[i].sound, cfg[i].send);
        midi_send(0x90u | (midi_out_base + i), on, vel ? vel : 1u);
    }
}

static void set_sound(uint32_t i, uint32_t index)
{
    cfg[i].preset = (uint8_t)index;
    cfg[i].sound = SOUNDS[index];
}

static void silence_lanes(void)
{
    uint32_t i;
    for (i = 0; i < NL; i++) {
        lane[i] = fm1_lane_silence(lane[i]);
        lane_report(i);
    }
}

static void lane_remake(uint32_t i)             /* a new lane from the settings: stops its note first */
{
    lane[i] = fm1_lane_silence(lane[i]);
    lane_report(i);
    lean_dec(lane[i]);
    lane[i] = fm1_lane_make(cfg[i].hits, cfg[i].steps, SPEED[cfg[i].speed], lane_mask(i), cfg[i].low, cfg[i].span,
                            0x9E3779B9u * (cfg[i].seed + 1u));
    lane[i] = fm1_lane_set_notes(lane[i], cfg[i].algo, cfg[i].chance, cfg[i].amount, cfg[i].mutate);
    lane[i] = fm1_lane_set_rhythm(lane[i], cfg[i].feel, cfg[i].rotate, cfg[i].accents, cfg[i].rule, cfg[i].ratchet, cfg[i].subhits, 1);
}

static void lanes_remask(void)                  /* the key, scale lock or chord changed */
{
    uint32_t i;
    for (i = 0; i < NL; i++) lane_apply(i);
}

static void reverb_apply(void)
{
    int32_t gain = (int32_t)(reverb_amount * 328u);         /* 100 is a gain of 1.0 */
    fm1_reverb_tune(reverb_time, reverb_bright);
    if (!reverb_return && gain) {               /* while the return was off the reverb did not run: drop the stale tail */
        reverb_ready = 0;
        fm1_reverb_clear();
        reverb_ready = 1;
    }
    reverb_return = gain;
}

static void delay_apply(void)
{
    int32_t gain = (int32_t)(delay_amount * 328u);          /* 100 is a gain of 1.0 */
    delay_bpm = bpm;
    fm1_delay_tune(delay_time, bpm, FS, delay_feedback, delay_tone);
    if (!delay_return && gain) {                /* while the return was off the line did not run: drop stale echoes */
        reverb_ready = 0;
        fm1_delay_clear();
        reverb_ready = 1;
    }
    delay_return = gain;
}

static void patch_set(const char *name, uint32_t new_bpm, uint32_t new_key, uint32_t prog, uint32_t rate, uint32_t lock,
                      const uint8_t *reverb, const uint8_t *delay, const patch_lane_t *src)
{
    uint32_t i;
    silence_lanes();
    for (i = 0; i < sizeof patch_name - 1u && name[i]; i++) patch_name[i] = name[i];
    patch_name[i] = 0;
    bpm = new_bpm; key = new_key % 12u; progression = prog < NPROGRESSION ? prog : 0u; rate_bars = rate; scale_lock = lock;
    chord_index = 0; tick_count = 0;
    reverb_time = reverb[0]; reverb_bright = reverb[1]; reverb_amount = reverb[2];
    reverb_apply();
    delay_time = delay[0] % FM1_DELAY_TIMES; delay_feedback = delay[1]; delay_tone = delay[2]; delay_amount = delay[3];
    delay_apply();
    for (i = 0; i < NL; i++) {
        cfg[i].hits = src[i].hits; cfg[i].steps = src[i].steps; cfg[i].speed = src[i].speed; cfg[i].scale = src[i].scale;
        cfg[i].low = src[i].low; cfg[i].span = src[i].span; cfg[i].seed = src[i].seed; cfg[i].algo = src[i].algo;
        cfg[i].chance = src[i].chance; cfg[i].amount = src[i].amount; cfg[i].mutate = src[i].mutate;
        cfg[i].chord = src[i].chord; cfg[i].level = src[i].level; cfg[i].send = src[i].send; cfg[i].muted = 0;
        cfg[i].feel = src[i].feel; cfg[i].rotate = src[i].rotate; cfg[i].accents = src[i].accents; cfg[i].rule = src[i].rule;
        cfg[i].ratchet = src[i].ratchet; cfg[i].subhits = src[i].subhits;
        set_sound(i, src[i].sound);
        lean_dec(lane[i]);
        lane[i] = fm1_lane_make(cfg[i].hits, cfg[i].steps, SPEED[cfg[i].speed], lane_mask(i), cfg[i].low, cfg[i].span,
                                0x9E3779B9u * (cfg[i].seed + 1u));
        lane[i] = fm1_lane_set_notes(lane[i], cfg[i].algo, cfg[i].chance, cfg[i].amount, cfg[i].mutate);
    }
}

static void user_name(char *name, uint32_t slot)    /* "USER 1" to "USER 8" */
{
    static const char prefix[] = "USER ";
    uint32_t i;
    for (i = 0; prefix[i]; i++) name[i] = prefix[i];
    name[i++] = (char)('1' + slot);
    name[i] = 0;
}

static lean_object *patch_from_slot(uint32_t slot)  /* the patch in a user slot, or 0; Firmware/Patch.lean checks the bytes */
{
    lean_object *bytes = lean_alloc_sarray(1, FM1_PATCH_BYTES, FM1_PATCH_BYTES), *decoded, *patch;
    if (slot_load(slot, lean_sarray_cptr(bytes), FM1_PATCH_BYTES)) { lean_dec(bytes); return 0; }
    decoded = fm1_patch_decode(bytes);
    if (lean_is_scalar(decoded)) return 0;
    patch = lean_ctor_get(decoded, 0);
    lean_inc(patch);
    lean_dec(decoded);
    return patch;
}

static void patch_load(uint32_t index)
{
    lean_object *user;
    patch_index = index;
    if (index < NPATCHES) {
        const patch_t *p = &PATCHES[index];
        patch_set(p->name, p->bpm, p->key, p->progression, p->rate, p->scale_lock, p->reverb, p->delay, p->lane);
    } else if ((user = patch_from_slot(index - NPATCHES)) != 0) {
        patch_lane_t lanes[NL];
        uint8_t reverb[3], delay[4];
        char name[7];
        uint32_t i;
        for (i = 0; i < NL; i++) {
            lean_object *l = fm1_patch_lane_of(user, i);
            patch_lane_t *d = &lanes[i];
            d->hits = (uint8_t)fm1_patch_lane_field_of(l, 0); d->steps = (uint8_t)fm1_patch_lane_field_of(l, 1);
            d->speed = (uint8_t)fm1_patch_lane_field_of(l, 2); d->scale = (uint8_t)fm1_patch_lane_field_of(l, 3);
            d->sound = (uint8_t)fm1_patch_lane_field_of(l, 4); d->low = (uint8_t)fm1_patch_lane_field_of(l, 5);
            d->span = (uint8_t)fm1_patch_lane_field_of(l, 6); d->algo = (uint8_t)fm1_patch_lane_field_of(l, 7);
            d->chance = (uint8_t)fm1_patch_lane_field_of(l, 8); d->amount = (uint8_t)fm1_patch_lane_field_of(l, 9);
            d->mutate = (uint8_t)fm1_patch_lane_field_of(l, 10); d->chord = (uint8_t)fm1_patch_lane_field_of(l, 11);
            d->level = (uint8_t)fm1_patch_lane_field_of(l, 12); d->send = (uint8_t)fm1_patch_lane_field_of(l, 13);
            d->seed = (uint16_t)fm1_patch_lane_field_of(l, 14);
            d->feel = (uint8_t)fm1_patch_lane_field_of(l, 15); d->rotate = (uint8_t)fm1_patch_lane_field_of(l, 16);
            d->accents = (uint8_t)fm1_patch_lane_field_of(l, 17); d->rule = (uint8_t)fm1_patch_lane_field_of(l, 18);
            d->ratchet = (uint8_t)fm1_patch_lane_field_of(l, 19); d->subhits = (uint8_t)fm1_patch_lane_field_of(l, 20);
            lean_dec(l);
        }
        for (i = 0; i < 3u; i++) reverb[i] = (uint8_t)fm1_patch_field_of(user, 5u + i);
        for (i = 0; i < 4u; i++) delay[i] = (uint8_t)fm1_patch_field_of(user, 8u + i);
        user_name(name, index - NPATCHES);
        patch_set(name, fm1_patch_field_of(user, 0), fm1_patch_field_of(user, 1), fm1_patch_field_of(user, 2),
                  fm1_patch_field_of(user, 3), fm1_patch_field_of(user, 4), reverb, delay, lanes);
        lean_dec(user);
    } else {
        const patch_t *p = &PATCHES[0];
        patch_set("EMPTY", p->bpm, 0, 0, 1, 0, p->reverb, p->delay, p->lane);
    }
}

static void patch_save(uint32_t slot)
{
    lean_object *lanes[NL], *patch, *bytes;
    uint32_t i;
    for (i = 0; i < NL; i++)
        lanes[i] = fm1_patch_lane_make(cfg[i].hits, cfg[i].steps, cfg[i].speed, cfg[i].scale, cfg[i].preset, cfg[i].low,
                                       cfg[i].span, cfg[i].algo, cfg[i].chance, cfg[i].amount, cfg[i].mutate, cfg[i].chord,
                                       cfg[i].level, cfg[i].send, cfg[i].seed, cfg[i].feel, cfg[i].rotate, cfg[i].accents,
                                       cfg[i].rule, cfg[i].ratchet, cfg[i].subhits);
    patch = fm1_patch_make(bpm, key, progression, rate_bars, scale_lock, reverb_time, reverb_bright, reverb_amount,
                           delay_time, delay_feedback, delay_tone, delay_amount, lanes[0], lanes[1], lanes[2], lanes[3]);
    bytes = fm1_patch_encode(patch);
    silence_lanes();                            /* a flash write stalls the sound */
    slot_save(slot, lean_sarray_cptr(bytes), (uint32_t)lean_sarray_size(bytes));
    lean_dec(bytes);
    patch_index = NPATCHES + slot;
    user_name(patch_name, slot);
}

static void lfo_tick(uint32_t dt_ms)            /* move every modulator on and refresh what it drives */
{
    uint32_t i;
    for (i = 0; i < NL; i++) {
        uint32_t period = LFO_BARS[lfo[i].rate % 5u] * 240000u / bpm, was = lfo[i].chance | lfo[i].level << 8;   /* ms a cycle: bars * 4 beats */
        uint32_t tri = 0;
        lfo[i].sound = cfg[i].sound;
        lfo[i].chance = cfg[i].chance;
        lfo[i].level = cfg[i].level;
        if (lfo[i].target && running) {
            lfo[i].phase = fm1_lfo_advance(lfo[i].phase, 0xFFFFFFFFu / period * dt_ms);
            tri = lfo[i].phase;
        }
        switch (lfo[i].target) {
        case 1: lfo[i].chance = (uint8_t)fm1_lfo_modulate(cfg[i].chance, lfo[i].depth, tri); break;
        case 2: lfo[i].level = (uint8_t)fm1_lfo_modulate(cfg[i].level, lfo[i].depth, tri); break;
        case 3: lfo[i].sound.timbre = (uint16_t)(fm1_lfo_modulate(cfg[i].sound.timbre * 100u / 32767u, lfo[i].depth, tri) * 327u); break;
        case 4: lfo[i].sound.color = (uint16_t)(fm1_lfo_modulate(cfg[i].sound.color * 100u / 32767u, lfo[i].depth, tri) * 327u); break;
        default: break;
        }
        if (lfo[i].target == 1u && (lfo[i].chance | lfo[i].level << 8) != was) lane_apply(i);   /* the lane keeps its own copy */
    }
}

static void clock_poll(void)                    /* 24 ticks a quarter note: bpm * 4 hundred-thousandths of a tick a ms */
{
    uint32_t dt = fm1_ms - tick_ms, i;
    tick_ms = fm1_ms;
    if (!running) return;
    tick_acc += dt * bpm * 4u;
    while (tick_acc >= 10000u) {
        tick_acc -= 10000u;
        for (i = 0; i < NL; i++) {
            lane[i] = fm1_lane_tick(lane[i]);
            lane_report(i);
        }
        tick_count++;
        if (progression && tick_count % (96u * rate_bars) == 0) { chord_index++; lanes_remask(); }   /* a chord every bar or more */
    }
}

static void play_start(void)
{
    running = 1; tick_count = 0; chord_index = 0;
    lanes_remask();
}

/* ---- pages: four values on screen, four knobs under them */
enum { G_HOME, G_SEQ, G_EDIT, G_GLO, G_FX, G_LFO };
enum { P_HOME, P_RHYTHM, P_FEEL, P_NOTES, P_RANGE, P_SOUND, P_ENVELOPE, P_MIX, P_REVERB, P_DELAY, P_HARMONY, P_SYSTEM, P_MIDI,
       P_BANKS, P_LFO, NPAGES };
#define NGROUPS 6u
static const char *const GROUP_NAME[NGROUPS] = {"HOME", "SEQ", "EDIT", "GLO", "FX", "LFO"};
static const uint8_t GROUP_PAGE[NGROUPS][4] = {{P_HOME, 255, 255, 255}, {P_RHYTHM, P_FEEL, P_NOTES, P_RANGE},
                                               {P_SOUND, P_ENVELOPE, P_MIX, 255}, {P_HARMONY, P_SYSTEM, P_MIDI, P_BANKS},
                                               {P_REVERB, P_DELAY, 255, 255}, {P_LFO, 255, 255, 255}};
static const uint8_t PAGE_GROUP[NPAGES] = {G_HOME, G_SEQ, G_SEQ, G_SEQ, G_SEQ, G_EDIT, G_EDIT, G_EDIT, G_FX, G_FX, G_GLO, G_GLO, G_GLO,
                                           G_GLO, G_LFO};
static const char *const PAGE_NAME[NPAGES] = {"OVERVIEW", "RHYTHM", "FEEL", "NOTES", "RANGE", "SOUND", "ENVELOPE", "MIX", "REVERB", "DELAY",
                                              "HARMONY", "SYSTEM", "MIDI", "BANKS", "LANE"};
static const char *const PAGE_LABEL[NPAGES][4] = {
    {"HITS", "STEPS", "SPEED", "CHANCE"}, {"HITS", "STEPS", "SPEED", "CHANCE"}, {"FEEL", "", "", ""}, {"ALGO", "AMOUNT", "MUTATE", "RANGE"},
    {"SCALE", "LOW", "CHORD", ""}, {"SHAPE", "TIMBRE", "COLOUR", "LEVEL"}, {"ATTACK", "RELEASE", "ENV", ""},
    {"LANE 1", "LANE 2", "LANE 3", "LANE 4"}, {"SEND", "DECAY", "BRIGHT", "RETURN"}, {"TIME", "FEEDBK", "TONE", "RETURN"},
    {"KEY", "LOCK", "CHORDS", "BARS"}, {"TEMPO", "OCTAVE", "LOOK", ""},
    {"IN", "OUT", "", ""}, {"PATCH", "SLOT", "DEMO", ""}, {"TARGET", "RATE", "DEPTH", ""}};
static uint32_t page = P_HOME, group_page[NGROUPS] = {P_HOME, P_RHYTHM, P_SOUND, P_HARMONY, P_REVERB, P_LFO};
static uint32_t browse_mode, browse_until, browse_family, browse_pos;   /* 0 closed, 1 sounds, 2 patches */
static uint32_t browse_by, browse_type;                                  /* sounds grouped by engine (0) or by type (1) */
static uint8_t browse_list[NSOUNDS > NBROWSE ? NSOUNDS : NBROWSE];
/* the patch browser's groups: patch_t.group + 1, then the user slots */
static const char *const PATCH_GROUP[] = {"ALL", "DEMOS", "SONGS", "CALM", "DREAM", "DRIVE", "PULSE", "DRIFT", "SHIMMER",
                                          "MACHINE", "FOLK", "USER"};
#define NPATCH_GROUP (sizeof PATCH_GROUP / sizeof PATCH_GROUP[0])
static uint32_t browse_patch_group, demo_pick;
static uint32_t browse_count;

static struct { uint8_t oct, ch, look; } set = {0, 0, ALFRED_LOOK};   /* what survives a power-off */
#define TH (THEMES[set.look < NTHEMES ? set.look : 0])

static int32_t clamp(int32_t v, int32_t lo, int32_t hi) { return v < lo ? lo : v > hi ? hi : v; }
static uint32_t frac(int32_t v, int32_t max) { return max > 0 ? (uint32_t)(clamp(v, 0, max) * 255 / max) : 0u; }

static char *put_str(char *p, const char *a)
{
    while (*a) *p++ = *a++;
    return p;
}

static char *put_num(char *p, uint32_t v)
{
    if (v >= 1000u) *p++ = (char)('0' + v / 1000u % 10u);
    if (v >= 100u) *p++ = (char)('0' + v / 100u % 10u);
    if (v >= 10u) *p++ = (char)('0' + v / 10u % 10u);
    *p++ = (char)('0' + v % 10u);
    return p;
}

static char *put_note(char *p, uint32_t note)
{
    p = put_str(p, KEY_NAME[note % 12u]);
    *p++ = (char)('0' + note / 12u - 1u);
    return p;
}

/* the label of value `k` on page `pg`: the FEEL and NOTES pages name their knobs after the source chosen */
static const char *page_label(uint32_t pg, uint32_t k)
{
    if (pg == P_FEEL && k > 0u) return FEEL_LABEL[cfg[selected].feel % NFEEL][k - 1u];
    if (pg == P_NOTES && (k == 1u || k == 2u)) return ALGO_LABEL[cfg[selected].algo % NALGO][k - 1u];
    return PAGE_LABEL[pg][k];
}

/* the text and the bar fill (0..255) of value `k` on page `pg` for the chosen lane */
static void param_text(uint32_t pg, uint32_t k, char *out, uint32_t *fill)
{
    char *p = out;
    const sound_t *snd = &cfg[selected].sound;
    *fill = 0;
    if (pg == P_HOME) pg = P_RHYTHM;
    switch (pg) {
    case P_RHYTHM:
        if (k == 0) { p = put_num(p, cfg[selected].hits); *fill = frac(cfg[selected].hits, cfg[selected].steps); }
        if (k == 1) { p = put_num(p, cfg[selected].steps); *fill = frac(cfg[selected].steps, 32); }
        if (k == 2) { p = put_str(p, SPEED_NAME[cfg[selected].speed]); *fill = frac(cfg[selected].speed, NSPEED - 1u); }
        if (k == 3) { p = put_num(p, cfg[selected].chance); *p++ = '%'; *fill = frac(cfg[selected].chance, 100); }
        break;
    case P_FEEL: {
        uint32_t feel = cfg[selected].feel % NFEEL;
        if (k == 0) { p = put_str(p, FEEL_NAME[feel]); *fill = frac(feel, NFEEL - 1u); }
        if (feel == 1u) {
            if (k == 1) { p = put_num(p, cfg[selected].rotate); *fill = frac(cfg[selected].rotate, cfg[selected].steps - 1); }
            if (k == 2) { p = put_num(p, cfg[selected].accents); *fill = frac(cfg[selected].accents, cfg[selected].hits); }
        } else if (feel == 2u) {
            if (k == 1) { p = put_num(p, cfg[selected].rule); *fill = frac(cfg[selected].rule, 255); }
        } else if (feel == 3u) {
            if (k == 1) { p = put_num(p, cfg[selected].ratchet); *fill = frac(cfg[selected].ratchet, 4); }
            if (k == 2) { p = put_num(p, cfg[selected].subhits); *fill = frac(cfg[selected].subhits, cfg[selected].ratchet); }
        }
        break;
    }
    case P_NOTES: {
        uint32_t algo = cfg[selected].algo % NALGO;
        if (k == 0) { p = put_str(p, ALGO_NAME[algo]); *fill = frac(algo, NALGO - 1u); }
        if (k == 1) {
            if (algo == 8u) { p = put_str(p, STYLE_NAME[(cfg[selected].amount - 1u) % 4u]); *fill = frac((cfg[selected].amount - 1u) % 4u, 3); }
            else if (algo == 9u) { p = put_str(p, GRAMMAR_NAME[(cfg[selected].amount - 1u) % 4u]); *fill = frac((cfg[selected].amount - 1u) % 4u, 3); }
            else { p = put_num(p, cfg[selected].amount); *fill = frac(cfg[selected].amount, 16); }
        }
        if (k == 2) {
            if (algo == 9u) { p = put_num(p, cfg[selected].mutate / 25u); *fill = frac(cfg[selected].mutate / 25u, 4); }
            else { p = put_num(p, cfg[selected].mutate); *p++ = '%'; *fill = frac(cfg[selected].mutate, 100); }
        }
        if (k == 3) { p = put_num(p, cfg[selected].span); p = put_str(p, " ST"); *fill = frac(cfg[selected].span, 36); }
        break;
    }
    case P_RANGE:
        if (k == 0) { p = put_str(p, scale_lock ? "LOCKED" : SCALE_NAME[cfg[selected].scale]); *fill = frac(cfg[selected].scale, NSCALE - 1u); }
        if (k == 1) { p = put_note(p, cfg[selected].low); *fill = frac(cfg[selected].low - 12, 84); }
        if (k == 2) { p = put_str(p, CHORD_NAME[cfg[selected].chord]); *fill = frac(cfg[selected].chord, 2); }
        break;
    case P_SOUND:
        if (k == 0) { p = put_str(p, braids_shape_name(snd->shape)); *fill = frac(snd->shape, BRAIDS_SHAPES - 1u); }
        if (k == 1) { p = put_num(p, (uint32_t)snd->timbre >> 7); *fill = frac(snd->timbre, 32767); }
        if (k == 2) { p = put_num(p, (uint32_t)snd->color >> 7); *fill = frac(snd->color, 32767); }
        if (k == 3) { p = put_num(p, snd->gain * 100u / 256u); *p++ = '%'; *fill = frac(snd->gain, 1024); }
        break;
    case P_ENVELOPE:
        if (k == 0) { p = put_num(p, ATTACK_MS[snd->attack]); p = put_str(p, " MS"); *fill = frac(snd->attack, 3); }
        if (k == 1) { p = put_num(p, RELEASE_MS[snd->release]); p = put_str(p, " MS"); *fill = frac(snd->release, 6); }
        if (k == 2) { p = put_num(p, snd->env); *fill = frac(snd->env, 16); }
        break;
    case P_MIX:
        p = put_num(p, cfg[k].level); *p++ = '%';
        if (cfg[k].muted) p = put_str(p, " MUTE");
        *fill = frac(cfg[k].level, 100);
        break;
    case P_REVERB:
        if (k == 0) { p = put_num(p, cfg[selected].send); *p++ = '%'; *fill = frac(cfg[selected].send, 100); }
        if (k == 1) { p = put_num(p, reverb_time); *p++ = '%'; *fill = frac(reverb_time, 100); }
        if (k == 2) { p = put_num(p, reverb_bright); *p++ = '%'; *fill = frac(reverb_bright, 100); }
        if (k == 3) { p = put_num(p, reverb_amount); *p++ = '%'; *fill = frac(reverb_amount, 100); }
        break;
    case P_DELAY:
        if (k == 0) { p = put_str(p, DELAY_TIME_NAME[delay_time % FM1_DELAY_TIMES]); *fill = frac((int32_t)delay_time, FM1_DELAY_TIMES - 1); }
        if (k == 1) { p = put_num(p, delay_feedback); *p++ = '%'; *fill = frac(delay_feedback, 100); }
        if (k == 2) { p = put_num(p, delay_tone); *p++ = '%'; *fill = frac(delay_tone, 100); }
        if (k == 3) { p = put_num(p, delay_amount); *p++ = '%'; *fill = frac(delay_amount, 100); }
        break;
    case P_HARMONY:
        if (k == 0) { p = put_str(p, KEY_NAME[key]); *fill = frac(key, 11); }
        if (k == 1) { p = put_str(p, scale_lock ? SCALE_NAME[scale_lock - 1u] : "LANES"); *fill = frac(scale_lock, NSCALE); }
        if (k == 2) { p = put_str(p, PROGRESSION_NAME[progression]); *fill = frac(progression, NPROGRESSION - 1u); }
        if (k == 3) { p = put_num(p, rate_bars); p = put_str(p, " BAR"); *fill = frac(rate_bars, 4); }
        break;
    case P_SYSTEM:
        if (k == 0) { p = put_num(p, bpm); p = put_str(p, " BPM"); *fill = frac((int32_t)bpm - 40, 200); }
        if (k == 2) { p = put_str(p, TH.name); *fill = frac(set.look, NTHEMES - 1u); }
        if (k == 1) { *p++ = set.oct & 0x80u ? '-' : '+'; p = put_num(p, (int8_t)set.oct < 0 ? (uint32_t)-(int8_t)set.oct : set.oct); *fill = frac((int8_t)set.oct + 2, 4); }
        break;
    case P_MIDI:
        if (k == 0) { if (set.ch) { p = put_str(p, "CH "); p = put_num(p, set.ch); } else p = put_str(p, "OMNI"); *fill = frac(set.ch, 16); }
        if (k == 1) { p = put_str(p, "CH "); p = put_num(p, midi_out_base + 1u); p = put_str(p, "-"); p = put_num(p, midi_out_base + 4u); *fill = frac(midi_out_base, 12); }
        break;
    case P_LFO:
        if (k == 0) { p = put_str(p, LFO_TARGET[lfo[selected].target]); *fill = frac(lfo[selected].target, NLFO_TARGET - 1u); }
        if (k == 1) { p = put_num(p, LFO_BARS[lfo[selected].rate]); p = put_str(p, " BAR"); *fill = frac(lfo[selected].rate, 4); }
        if (k == 2) { p = put_num(p, lfo[selected].depth); *p++ = '%'; *fill = frac(lfo[selected].depth, 100); }
        break;
    case P_BANKS:
        if (k == 0) { p = patch_index >= NPATCHES ? put_str(p, "U") : put_str(p, "P"); p = put_num(p, patch_index >= NPATCHES ? patch_index - NPATCHES + 1u : patch_index + 1u); *fill = frac(patch_index, NBROWSE - 1u); }
        if (k == 1) { p = put_str(p, "USER "); p = put_num(p, save_slot + 1u); *fill = frac(save_slot, NUSER - 1u); }
        if (k == 2) {                           /* the demo song playing, or the one the knob would load */
            uint32_t demo = patch_index < NPATCHES && PATCHES[patch_index].group == 0u ? patch_index : demo_pick;
            p = put_str(p, PATCHES[demo].name); *fill = frac(demo, NDEMO - 1u);
        }
        break;
    default: break;
    }
    *p = 0;
}

static void param_turn(uint32_t pg, uint32_t k, int32_t d)
{
    sound_t *snd = &cfg[selected].sound;
    uint32_t i;
    if (pg == P_HOME) pg = P_RHYTHM;
    switch (pg) {
    case P_RHYTHM:
        if (k == 0) cfg[selected].hits = (uint8_t)clamp(cfg[selected].hits + d, 0, cfg[selected].steps);
        if (k == 1) {
            cfg[selected].steps = (uint8_t)clamp(cfg[selected].steps + d, 1, 32);
            if (cfg[selected].hits > cfg[selected].steps) cfg[selected].hits = cfg[selected].steps;
            if (cfg[selected].rotate >= cfg[selected].steps) cfg[selected].rotate = (uint8_t)(cfg[selected].steps - 1u);
        }
        if (cfg[selected].accents > cfg[selected].hits) cfg[selected].accents = cfg[selected].hits;
        if (k == 2) cfg[selected].speed = (uint8_t)clamp(cfg[selected].speed + d, 0, (int32_t)NSPEED - 1);
        if (k == 3) cfg[selected].chance = (uint8_t)clamp(cfg[selected].chance + 5 * d, 0, 100);
        lane_apply(selected);
        break;
    case P_FEEL: {
        uint32_t feel = cfg[selected].feel % NFEEL;
        if (k == 0) cfg[selected].feel = (uint8_t)clamp(cfg[selected].feel + d, 0, (int32_t)NFEEL - 1);
        if (feel == 1u && k == 1) cfg[selected].rotate = (uint8_t)clamp(cfg[selected].rotate + d, 0, cfg[selected].steps - 1);
        if (feel == 1u && k == 2) cfg[selected].accents = (uint8_t)clamp(cfg[selected].accents + d, 0, cfg[selected].hits);
        if (feel == 2u && k == 1) cfg[selected].rule = (uint8_t)clamp(cfg[selected].rule + d, 0, 255);
        if (feel == 3u && k == 1) cfg[selected].ratchet = (uint8_t)clamp(cfg[selected].ratchet + d, 1, 4);
        if (feel == 3u && k == 2) cfg[selected].subhits = (uint8_t)clamp(cfg[selected].subhits + d, 1, cfg[selected].ratchet);
        if (cfg[selected].subhits > cfg[selected].ratchet) cfg[selected].subhits = cfg[selected].ratchet;
        lane_apply(selected);
        break;
    }
    case P_NOTES:
        if (k == 0) cfg[selected].algo = (uint8_t)clamp(cfg[selected].algo + d, 0, (int32_t)NALGO - 1);
        if (k == 1) cfg[selected].amount = (uint8_t)clamp(cfg[selected].amount + d, 1, 16);
        if (k == 2) cfg[selected].mutate = (uint8_t)clamp(cfg[selected].mutate + (cfg[selected].algo == 9u ? 25 : 5) * d, 0, 100);   /* GRAMMAR: a depth a click */
        if (k == 3) { cfg[selected].span = (uint8_t)clamp(cfg[selected].span + d, 1, 36); lane_remake(selected); }
        else lane_apply(selected);
        break;
    case P_RANGE:
        if (k == 0) cfg[selected].scale = (uint8_t)clamp(cfg[selected].scale + d, 0, (int32_t)NSCALE - 1);
        if (k == 1) { cfg[selected].low = (uint8_t)clamp(cfg[selected].low + d, 12, 96); lane_remake(selected); return; }
        if (k == 2) cfg[selected].chord = (uint8_t)clamp(cfg[selected].chord + d, 0, 2);
        lane_apply(selected);
        break;
    case P_SOUND:
        if (k == 0) snd->shape = (uint8_t)clamp(snd->shape + d, 0, (int32_t)BRAIDS_SHAPES - 1);
        if (k == 1) snd->timbre = (uint16_t)clamp(snd->timbre + d * 512, 0, 32767);
        if (k == 2) snd->color = (uint16_t)clamp(snd->color + d * 512, 0, 32767);
        if (k == 3) snd->gain = (uint16_t)clamp(snd->gain + d * 16, 32, 1024);
        break;
    case P_ENVELOPE:
        if (k == 0) snd->attack = (uint8_t)clamp(snd->attack + d, 0, 3);
        if (k == 1) snd->release = (uint8_t)clamp(snd->release + d, 0, 6);
        if (k == 2) snd->env = (uint8_t)clamp(snd->env + d, 0, 16);
        break;
    case P_MIX:
        cfg[k].level = (uint8_t)clamp(cfg[k].level + 5 * d, 0, 100);
        break;
    case P_REVERB:
        if (k == 0) cfg[selected].send = (uint8_t)clamp(cfg[selected].send + 5 * d, 0, 100);
        if (k == 1) reverb_time = (uint32_t)clamp((int32_t)reverb_time + 5 * d, 0, 100);
        if (k == 2) reverb_bright = (uint32_t)clamp((int32_t)reverb_bright + 5 * d, 0, 100);
        if (k == 3) reverb_amount = (uint32_t)clamp((int32_t)reverb_amount + 5 * d, 0, 100);
        reverb_apply();
        break;
    case P_DELAY:
        if (k == 0) delay_time = (uint32_t)clamp((int32_t)delay_time + d, 0, FM1_DELAY_TIMES - 1);
        if (k == 1) delay_feedback = (uint32_t)clamp((int32_t)delay_feedback + 5 * d, 0, 100);
        if (k == 2) delay_tone = (uint32_t)clamp((int32_t)delay_tone + 5 * d, 0, 100);
        if (k == 3) delay_amount = (uint32_t)clamp((int32_t)delay_amount + 5 * d, 0, 100);
        delay_apply();
        break;
    case P_HARMONY:
        if (k == 0) key = (uint32_t)clamp((int32_t)key + d, 0, 11);
        if (k == 1) scale_lock = (uint32_t)clamp((int32_t)scale_lock + d, 0, (int32_t)NSCALE);
        if (k == 2) progression = (uint32_t)clamp((int32_t)progression + d, 0, (int32_t)NPROGRESSION - 1);
        if (k == 3) {
            for (i = 0; i < 3u && RATE_BARS[i] != rate_bars; i++) {}
            rate_bars = RATE_BARS[clamp((int32_t)i + d, 0, 2)];
        }
        chord_index = 0;
        lanes_remask();
        break;
    case P_SYSTEM:
        if (k == 0) bpm = (uint32_t)clamp((int32_t)bpm + 2 * d, 40, 240);
        if (k == 1) set.oct = (uint8_t)clamp((int8_t)set.oct + d, -2, 2);
        if (k == 2) set.look = (uint8_t)clamp(set.look + d, 0, (int32_t)NTHEMES - 1);
        break;
    case P_MIDI:
        if (k == 0) set.ch = (uint8_t)clamp(set.ch + d, 0, 16);
        if (k == 1) midi_out_base = (uint32_t)clamp((int32_t)midi_out_base + d, 0, 12);
        break;
    case P_LFO:
        if (k == 0) lfo[selected].target = (uint8_t)clamp(lfo[selected].target + d, 0, (int32_t)NLFO_TARGET - 1);
        if (k == 1) lfo[selected].rate = (uint8_t)clamp(lfo[selected].rate + d, 0, 4);
        if (k == 2) lfo[selected].depth = (uint8_t)clamp(lfo[selected].depth + 5 * d, 0, 100);
        break;
    case P_BANKS:
        if (k == 0) patch_load((uint32_t)clamp((int32_t)patch_index + d, 0, (int32_t)NBROWSE - 1));
        if (k == 1) save_slot = (uint32_t)clamp((int32_t)save_slot + d, 0, (int32_t)NUSER - 1);
        if (k == 2) {                           /* DEMO: step through the demo songs, loading each */
            uint32_t demo = patch_index < NPATCHES && PATCHES[patch_index].group == 0u ? patch_index : demo_pick;
            demo_pick = (uint32_t)clamp((int32_t)demo + d, 0, (int32_t)NDEMO - 1);
            patch_load(demo_pick);
        }
        break;
    default: break;
    }
}

static void goto_group(uint32_t g)              /* tap a group button: enter it, or move to its next page */
{
    uint32_t pages = 0, i;
    while (pages < 4u && GROUP_PAGE[g][pages] != 255u) pages++;
    if (PAGE_GROUP[page] == g) {
        for (i = 0; i < pages && GROUP_PAGE[g][i] != page; i++) {}
        page = GROUP_PAGE[g][(i + 1u) % pages];
    } else {
        page = group_page[g];
    }
    group_page[g] = page;
    browse_mode = 0;
}

/* ---- the browser: sounds by family, or patches */
static int browse_fits(uint32_t i)              /* is sound `i` in the chosen group? */
{
    if (browse_by) return !browse_type || SOUNDS[i].type + 1u == browse_type;
    return SOUNDS[i].shape >= FAMILY_FIRST[browse_family] && SOUNDS[i].shape <= FAMILY_LAST[browse_family];
}

static int browse_patch_fits(uint32_t i)        /* is patch `i` (a user slot from NPATCHES) in the chosen group? */
{
    if (!browse_patch_group) return 1;
    if (i >= NPATCHES) return browse_patch_group == NPATCH_GROUP - 1u;
    return PATCHES[i].group + 1u == browse_patch_group;
}

static void browse_build(void)                  /* the sounds or patches of the chosen group, in preset order */
{
    uint32_t i, n = browse_mode == 1u ? NSOUNDS : NBROWSE;
    browse_count = 0;
    for (i = 0; i < n; i++)
        if (browse_mode == 1u ? browse_fits(i) : browse_patch_fits(i)) browse_list[browse_count++] = (uint8_t)i;
}

static void browse_find(uint32_t item)          /* put the cursor on `item` of the list, or at the top */
{
    uint32_t i;
    for (i = 0; i < browse_count && browse_list[i] != item; i++) {}
    browse_pos = i < browse_count ? i : 0u;
}

static const char *browse_group(void)           /* the name of the chosen group */
{
    return browse_by ? TYPE_NAME[browse_type] : FAMILY_NAME[browse_family];
}

static void browse_open(uint32_t mode)
{
    if (browse_mode != mode) {
        browse_mode = mode;
        if (mode == 1u) {
            browse_family = 0; browse_type = 0;
            browse_build();
            browse_find(cfg[selected].preset);
        } else {
            browse_patch_group = 0;
            browse_build();
            browse_find(patch_index);
        }
    }
    browse_until = fm1_ms + 2500u;
}

static void browse_turn(int32_t d)              /* PRESETS: scroll, and the lane or patch follows at once */
{
    browse_open(PAGE_GROUP[page] == G_EDIT ? 1u : 2u);
    if (browse_mode == 1u) {
        if (!browse_count) return;
        browse_pos = (uint32_t)clamp((int32_t)browse_pos + d, 0, (int32_t)browse_count - 1);
        set_sound(selected, browse_list[browse_pos]);
    } else {
        if (!browse_count) return;
        browse_pos = (uint32_t)clamp((int32_t)browse_pos + d, 0, (int32_t)browse_count - 1);
        patch_load(browse_list[browse_pos]);
    }
}

static void browse_patch_group_turn(int32_t d)  /* SELECT while patches are open: another group */
{
    uint32_t next = (uint32_t)clamp((int32_t)browse_patch_group + d, 0, (int32_t)NPATCH_GROUP - 1);
    browse_open(2u);
    if (next != browse_patch_group) { browse_patch_group = next; browse_build(); browse_pos = 0; }
    if (browse_count) patch_load(browse_list[browse_pos]);
}

static void browse_family_turn(int32_t d)       /* SELECT while sounds are open: another group (engine or type) */
{
    uint32_t *group = browse_by ? &browse_type : &browse_family;
    uint32_t next = (uint32_t)clamp((int32_t)*group + d, 0, browse_by ? (int32_t)NTYPE - 1 : (int32_t)NFAMILY - 1);
    browse_open(1u);
    if (next != *group) { *group = next; browse_build(); browse_pos = 0; }
    if (browse_count) set_sound(selected, browse_list[browse_pos]);
}

static void browse_by_turn(void)                /* ALGO while sounds are open: group by engine or by type, keeping the sound */
{
    browse_open(1u);
    browse_by = !browse_by;
    browse_family = 0; browse_type = 0;
    browse_build();
    browse_find(cfg[selected].preset);
}

/* ---- the screen */
#define C_ACC TH.acc
#define C_OFF TH.mid
#define C_REST TH.dim
#define LANE_COLOUR(i) TH.lane[i]
/* text on the look's background: draw_text_box (gfx.c) always clears to black */
static void text_box(uint32_t x, uint32_t y, uint32_t w, const felucca_font_t *f, const char *s, uint16_t c, int align)
{
    int32_t tw = text_w(f, s), tx = 0;
    cv_begin(w, f->h, TH.bg);
    if (align == 1) tx = ((int32_t)w - tw) / 2;
    else if (align == 2) tx = (int32_t)w - tw;
    cv_text(tx, 0, f, s, c);
    cv_blit(x, y);
    lcd_sync();
}

/* The screen. A title bar (0..20), lane rows, the page's four columns, a status bar (218..239).
 * HOME: a ledger of the four lanes, and Alfred standing in when the clock is stopped. */
#define BAR_H 21u
#define HOME_ROW_Y(i) (28u + (i) * 36u)
#define STRIP_ROW_Y(i) (26u + (i) * 14u)
#define ALFRED_X 188u
#define ALFRED_Y 172u

static uint16_t blend(uint16_t a, uint16_t b)   /* halfway between two colours */
{
    return (uint16_t)(((((a >> 11) + (b >> 11)) / 2u) << 11) | (((((a >> 5) & 63u) + ((b >> 5) & 63u)) / 2u) << 5) |
                      (((a & 31u) + (b & 31u)) / 2u));
}

static void draw_steps(uint32_t x, uint32_t y, uint32_t i, uint16_t col, uint32_t w, uint32_t h, uint32_t gap)
{
    uint32_t k, cur = fm1_lane_step_of(lane[i]);
    for (k = 0; k < cfg[i].steps; k++) {
        int32_t sx = (int32_t)(x + k * gap);
        uint16_t c = k == cur ? TH.hi : fm1_lane_hit_at_of(lane[i], k) ? col : TH.dim;
        if (fm1_lane_hit_at_of(lane[i], k) || k == cur) cv_rect(sx, (int32_t)y, (int32_t)w, (int32_t)h, c);
        else cv_rect(sx + (int32_t)(w / 2u) - 1, (int32_t)(y + h / 2u) - 1, 2, 2, c);
    }
}

static void draw_lane(uint32_t i)               /* one lane row: the ledger on HOME, a thin strip elsewhere */
{
    uint16_t live = cfg[i].muted || !cfg[i].level ? TH.dim : LANE_COLOUR(i);
    uint16_t ink = i == selected ? live : TH.mid;
    char s[40], *p = s;
    if (page == P_HOME) {
        cv_begin(240, 36, TH.bg);
        if (i == selected) cv_rect(0, 0, 2, 33, live);
        s[0] = (char)('1' + i); s[1] = 0;
        cv_text(8, 0, &FONT_S, s, live);
        draw_steps(24, 3, i, live, 6, 10, 7);
        cv_text(150, 0, &FONT_S, SCALE_NAME[scale_lock ? scale_lock - 1u : cfg[i].scale], TH.mid);
        p = put_num(s, cfg[i].hits); *p++ = '/'; p = put_num(p, cfg[i].steps); *p++ = ' ';
        p = put_str(p, SPEED_NAME[cfg[i].speed]); *p = 0;
        cv_text(8, 16, &FONT_S, s, ink);
        cv_text(232 - text_w(&FONT_S, braids_shape_name(cfg[i].sound.shape)), 16, &FONT_S, braids_shape_name(cfg[i].sound.shape), ink);
        cv_rect(8, 33, 224, 1, TH.dim);
        cv_blit(0, HOME_ROW_Y(i));
    } else {
        cv_begin(240, 14, TH.bg);
        s[0] = (char)('1' + i); s[1] = 0;
        cv_text(6, -2, &FONT_S, s, i == selected ? live : TH.dim);
        draw_steps(22, 2, i, i == selected ? live : TH.dim, 5, 8, 6);
        cv_text(232 - text_w(&FONT_S, braids_shape_name(cfg[i].sound.shape)), -2, &FONT_S, braids_shape_name(cfg[i].sound.shape),
                i == selected ? live : TH.dim);
        cv_blit(0, STRIP_ROW_Y(i));
    }
}

static void draw_title(void)                    /* the group and page, or the name on HOME; the tempo on the right */
{
    char s[24], *p = s;
    cv_begin(240, BAR_H, TH.dim);
    if (page == P_HOME) p = put_str(s, "FORMALFRED");
    else { p = put_str(s, GROUP_NAME[PAGE_GROUP[page]]); p = put_str(p, "  "); p = put_str(p, PAGE_NAME[page]); if (page == P_LFO) { *p++ = ' '; *p++ = (char)('1' + selected); } }
    *p = 0;
    cv_text(6, 2, &FONT_S, s, TH.hi);
    p = put_num(s, bpm); *p = 0;
    cv_text(234 - text_w(&FONT_S, s), 2, &FONT_S, s, running ? TH.hi : TH.mid);
    cv_blit(0, 0);
}

/* RHYTHM: the chosen lane's bar as a circle in place of the HITS and STEPS meters. One dot a step, clockwise
 * from the top; the hits are filled and joined, the current step is bright. Braids' sine table places the dots. */
uint16_t fm1_braids_wav_sine(uint32_t index);
#define CIRCLE_CX 62
#define CIRCLE_CY 40
#define CIRCLE_R 33
static void circle_point(uint32_t k, uint32_t steps, int32_t *x, int32_t *y)
{
    uint32_t a = (k * 256u) / steps;
    *x = CIRCLE_CX + ((int32_t)(int16_t)fm1_braids_wav_sine(a) * CIRCLE_R + 16384) / 32768;
    *y = CIRCLE_CY - ((int32_t)(int16_t)fm1_braids_wav_sine((a + 64u) & 255u) * CIRCLE_R + 16384) / 32768;
}

static void draw_circle(void)
{
    uint32_t steps = cfg[selected].steps, cur = fm1_lane_step_of(lane[selected]), k, last = ~0u, first = ~0u;
    uint16_t col = cfg[selected].muted || !cfg[selected].level ? TH.dim : LANE_COLOUR(selected), faint = blend(TH.bg, col);
    int32_t x, y, px = 0, py = 0, fx = 0, fy = 0;
    cv_begin(116, 82, TH.bg);
    for (k = 0; k < steps; k++) {                           /* the polygon of hits first, under the dots */
        if (!fm1_lane_hit_at_of(lane[selected], k)) continue;
        circle_point(k, steps, &x, &y);
        if (last == ~0u) { fx = x; fy = y; first = k; } else cv_line(px, py, x, y, faint);
        px = x; py = y; last = k;
    }
    if (first != ~0u && last != first) cv_line(px, py, fx, fy, faint);
    for (k = 0; k < steps; k++) {
        int hit = fm1_lane_hit_at_of(lane[selected], k), loud = fm1_lane_accent_at_of(lane[selected], k);
        uint16_t c = k == cur ? TH.hi : hit ? col : TH.dim;
        circle_point(k, steps, &x, &y);
        if (loud) cv_rect(x - 3, y - 3, 7, 7, c);
        else if (hit || k == cur) cv_rect(x - 2, y - 2, 5, 5, c);
        else cv_rect(x - 1, y - 1, 2, 2, c);
    }
    cv_blit(4, 90);
}

static void draw_columns(void)                  /* the page's four values: a meter, the value, the label */
{
    char value[24];
    uint32_t k, fill;
    uint16_t well = blend(TH.bg, TH.dim);
    cv_begin(240, 82, TH.bg);
    for (k = 0; k < 4u; k++) {
        int32_t x = 10 + (int32_t)k * 58;
        uint16_t col = page == P_MIX ? LANE_COLOUR(k) : LANE_COLOUR(selected);
        if (!page_label(page, k)[0]) continue;
        if ((page == P_RHYTHM || page == P_FEEL) && k < 2u) continue;           /* the circle stands in for these two meters */
        param_text(page, k, value, &fill);
        cv_rect(x, 0, 46, 80, well);
        cv_rect(x, 80 - (int32_t)(fill * 80u / 255u), 46, (int32_t)(fill * 80u / 255u), col);
    }
    cv_blit(0, 90);
    if (page == P_RHYTHM || page == P_FEEL) draw_circle();
    cv_begin(240, 36, TH.bg);
    for (k = 0; k < 4u; k++) {
        int32_t cx = 33 + (int32_t)k * 58;
        if (!page_label(page, k)[0]) continue;
        param_text(page, k, value, &fill);
        cv_text(cx - text_w(&FONT_S, value) / 2, 0, &FONT_S, value, TH.hi);
        cv_text(cx - text_w(&FONT_S, page_label(page, k)) / 2, 18, &FONT_S, page_label(page, k), TH.mid);
    }
    cv_blit(0, 176);
}

static void draw_status(void)                   /* the patch on the left, the chosen lane's sound on the right */
{
    char s[44], *p = s;
    const sound_t *snd = &cfg[selected].sound;
    cv_begin(240, 22, TH.dim);
    p = put_str(s, patch_index >= NPATCHES ? "U" : "P");
    p = put_num(p, patch_index >= NPATCHES ? patch_index - NPATCHES + 1u : patch_index + 1u);
    *p++ = ' '; p = put_str(p, patch_name); *p = 0;
    cv_text(6, 3, &FONT_S, s, TH.hi);
    if (page == P_HOME && !running) { cv_blit(0, 218); return; }   /* Alfred stands there */
    p = s;
    *p++ = (char)('1' + selected); *p++ = ' ';
    p = put_str(p, SOUNDS[cfg[selected].preset].name);
    if (snd->timbre != SOUNDS[cfg[selected].preset].timbre || snd->color != SOUNDS[cfg[selected].preset].color ||
        snd->shape != SOUNDS[cfg[selected].preset].shape) *p++ = '*';
    *p = 0;
    cv_text(234 - text_w(&FONT_S, s), 3, &FONT_S, s, LANE_COLOUR(selected));
    cv_blit(0, 218);
}

static void draw_home_foot(void)                /* HOME: the key and the chord; Alfred's corner is left clear when stopped */
{
    char s[32], *p = s;
    cv_begin(240, 40, TH.bg);
    cv_rect(8, 0, 224, 1, TH.dim);
    p = put_str(s, "KEY "); p = put_str(p, KEY_NAME[key]);
    if (progression) { p = put_str(p, "  CHORD "); p = put_str(p, KEY_NAME[(key + chord_root()) % 12u]); }
    *p = 0;
    cv_text(8, 6, &FONT_S, s, TH.mid);
    cv_text(8, 22, &FONT_S, running ? "PLAYING" : "STOPPED", running ? TH.acc : TH.mid);
    cv_blit(0, 176);
}

static void draw_browser(void)
{
    uint32_t row, rows = 9, first, count = browse_count;
    char s[44], *p = s;
    cv_begin(240, BAR_H, TH.dim);
    p = put_str(s, browse_mode == 1u ? "SOUNDS  " : "PATCHES  ");
    if (browse_mode == 1u) { p = put_str(p, browse_by ? "BY TYPE  " : "BY ENGINE  "); p = put_str(p, browse_group()); }
    else p = put_str(p, PATCH_GROUP[browse_patch_group]);
    *p = 0;
    cv_text(6, 2, &FONT_S, s, TH.hi);
    cv_blit(0, 0);
    lcd_fill(0, BAR_H, 240, 218u - BAR_H, TH.bg);
    first = browse_pos < rows / 2u ? 0u : browse_pos - rows / 2u;
    if (first + rows > count) first = count > rows ? count - rows : 0u;
    for (row = 0; row < rows && first + row < count; row++) {
        uint32_t index = first + row, item = browse_list[index];
        const char *name;
        char line[44], *q = line;
        uint16_t col = index == browse_pos ? LANE_COLOUR(selected) : TH.mid;
        if (browse_mode == 1u) name = SOUNDS[item].name;
        else if (item < NPATCHES) name = PATCHES[item].name;
        else name = "USER SLOT";
        q = put_num(q, item + 1u); *q++ = ' ';
        q = put_str(q, name);
        if (browse_mode == 2u && item >= NPATCHES) { *q++ = ' '; q = put_num(q, item - NPATCHES + 1u); }
        *q = 0;
        cv_begin(240, 20, TH.bg);
        if (index == browse_pos) cv_rect(0, 0, 3, 20, col);
        cv_text(12, 2, &FONT_S, line, col);
        cv_blit(0, 26 + row * 20);
    }
    cv_begin(240, 22, TH.dim);
    cv_text(6, 3, &FONT_S, browse_mode == 1u ? (browse_by ? "SELECT TYPE   ALGO BY ENGINE" : "SELECT ENGINE   ALGO BY TYPE")
                                           : "SELECT GROUP   SAVE KEEPS", TH.mid);
    cv_blit(0, 218);
}

/* ---- MIDI in: notes play the chosen lane's sound; from the main loop and from app_idle while the screen draws */
static uint32_t idle_ok;

static void midi_in(void)
{
    uint8_t st, d1, d2;
    while (midi_get(&st, &d1, &d2) != 0) {
        uint32_t ty = st & 0xF0u;
        if (set.ch && (st & 15u) != set.ch - 1u) continue;
        if (ty == 0x90u && d2) play(d1, d2, &cfg[selected].sound, cfg[selected].send);
        else if (ty == 0x80u || ty == 0x90u) stop(d1);
    }
}
static void app_idle(void)
{
    if (idle_ok) midi_in();
}

#define KEY0 53u                                /* key 0 = F3 */

static uint32_t ui_hash(void)                   /* changes whenever something outside the lane rows is drawn differently */
{
    const uint8_t *b = (const uint8_t *)cfg;
    uint32_t h = 2166136261u, i;
    uint32_t g[] = {page, selected, patch_index, bpm, key, progression, rate_bars, scale_lock, running, browse_mode, browse_pos,
                    browse_family, browse_by, browse_type, chord_index, save_slot, midi_out_base, set.oct, set.ch, set.look, reverb_time, reverb_bright,
                    reverb_amount, delay_time, delay_feedback, delay_tone, delay_amount};
    for (i = 0; i < sizeof cfg; i++) h = (h ^ b[i]) * 16777619u;
    for (i = 0; i < NL; i++) h = (h ^ (lfo[i].target | lfo[i].rate << 8 | lfo[i].depth << 16)) * 16777619u;
    for (i = 0; i < sizeof g / sizeof g[0]; i++) h = (h ^ g[i]) * 16777619u;
    return h;
}


/* ---- the startup screen: the title, Alfred, and a line from him. Any button or key skips it after a moment. */
#define BOOT_MS 3000u

static uint16_t alfred_colour(uint32_t c)
{
    switch (c) {
    case A_OUTLINE: return TH.outline;
    case A_SKIN: return RGB(238, 190, 150);
    case A_SHADE: return RGB(205, 150, 115);
    case A_EYE: return RGB(20, 20, 30);
    case A_WHITE: return RGB(240, 236, 226);
    case A_GREY: return RGB(150, 150, 160);
    case A_SUIT: return TH.suit;
    case A_SUIT_LIGHT: return TH.suit_light;
    default: return TH.acc;
    }
}

/* Alfred `scale` pixels a sprite pixel, his head `dip` sprite rows lower (a bow), eyes shut if `blink`. Drawn as bands. */
static void draw_alfred(uint32_t x, uint32_t y, uint32_t scale, uint32_t dip, int blink)
{
    uint32_t row, col, band, rows_per_band = 8u;
    for (band = 0; band * rows_per_band < ALFRED_H + dip; band++) {
        cv_begin(ALFRED_W * scale, rows_per_band * scale, TH.bg);
        for (row = 0; row < rows_per_band; row++) {
            uint32_t out_row = band * rows_per_band + row, src, dx, dy;
            if (out_row >= ALFRED_H + dip) break;
            if (out_row < dip) continue;                                     /* blank above the dipped head */
            src = out_row - dip < ALFRED_HEAD_ROWS ? out_row - dip : out_row;   /* the head rides down over the collar */
            if (src >= ALFRED_H) continue;
            for (col = 0; col < ALFRED_W; col++) {
                uint32_t c = ALFRED[src][col];
                if (!c) continue;
                if (c == A_EYE && blink) c = A_SKIN;
                for (dy = 0; dy < scale; dy++)
                    for (dx = 0; dx < scale; dx++)
                        cv_pset((int32_t)(col * scale + dx), (int32_t)(row * scale + dy), alfred_colour(c));
            }
        }
        cv_blit(x, y + band * rows_per_band * scale);
    }
}

static void boot_screen(void)
{
    static const char LINE[] = "AT YOUR SERVICE";
    uint32_t t0 = fm1_ms, shown = 0, skip_at = 700u, dip_drawn = ~0u, blink_drawn = ~0u, ax = (240u - ALFRED_W * 4u) / 2u;
    uint32_t rel, k;
    char line[sizeof LINE];
    lcd_fill(0, 0, 240, 240, TH.bg);
    text_box(0, 14, 240, &FONT_L, "FORMALFRED", TH.hi, 1);
    cv_begin(240, 2, TH.bg);
    cv_rect(60, 0, 120, 2, TH.acc);
    cv_blit(0, 50);
    text_box(0, 58, 240, &FONT_S, "a generative sequencer", TH.mid, 1);
    for (;;) {
        uint32_t t, dip, blink, chars;
        platform_poll();
        t = fm1_ms - t0;
        if (t > skip_at && (fm1_input_edges(&rel) || fm1_in.notes)) break;
        if (t >= BOOT_MS) break;
        dip = t >= 1500u && t < 1900u ? 2u : t >= 1900u && t < 2100u ? 1u : 0u;      /* a short bow */
        blink = t >= 900u && t < 1050u;
        if (dip != dip_drawn || blink != blink_drawn) { dip_drawn = dip; blink_drawn = blink; draw_alfred(ax, 82, 4u, dip, (int)blink); }
        chars = t < 1700u ? 0u : (t - 1700u) / 40u;
        if (chars > sizeof LINE - 1u) chars = sizeof LINE - 1u;
        if (chars != shown) {
            shown = chars;
            for (k = 0; k < chars; k++) line[k] = LINE[k];
            line[chars] = 0;
            text_box(0, 220, 240, &FONT_S, line, TH.acc, 1);
        }
    }
    lcd_fill(0, 0, 240, 240, TH.bg);
}

static void app_main(void)
{
    uint32_t prev = 0, k, t_change = 0, dirty = 0, shown = 0, alfred_shown = ~0u, stopped_ms = 0;
    uint32_t row_sig[NL];
    uint8_t held[27] = {0};                     /* the note each key plays */
    if (settings_load(&set, sizeof set) || (int8_t)set.oct < -2 || (int8_t)set.oct > 2 || set.ch > 16u || set.look >= NTHEMES)
        set.oct = 0, set.ch = 0, set.look = ALFRED_LOOK;
    for (k = 0; k < NV; k++) braids_voice_init(vmem[k]);
    for (k = 0; k < NL; k++) lane[k] = fm1_lane_make(1, 1, 1, 1, 36, 1, 1u);
    fm1_reverb_init(FM1_REVERB_SCALE_44K, 48694);              /* a half hertz at 44.1 kHz */
    reverb_ready = 1;
    patch_load(0);
    boot_screen();
    lcd_fill(0, 0, 240, 240, TH.bg);

    for (;;) {
        uint32_t keys, down, up, rel, b, lit = 0, h;
        int32_t oct = (int8_t)set.oct, e;
        uint32_t base = (uint32_t)((int32_t)KEY0 + 12 * oct);
        platform_poll();
        clock_poll();
        if (delay_bpm != bpm) delay_apply();    /* the echo follows the tempo */
        { static uint32_t lfo_ms; if (fm1_ms != lfo_ms) { lfo_tick(fm1_ms - lfo_ms); lfo_ms = fm1_ms; } }

        keys = fm1_in.notes;                    /* bit k: key k (0 = F3 .. 26 = G5) */
        down = keys & ~prev;
        up = prev & ~keys;
        prev = keys;
        for (k = 0; k < 27u; k++) {             /* a key stops the note it started: the octave may change meanwhile */
            if (down >> k & 1u) {
                held[k] = (uint8_t)(base + k); play(held[k], 100, &cfg[selected].sound, cfg[selected].send); midi_send(0x90u | 15u, held[k], 100);
                if (cfg[selected].algo == 7u || cfg[selected].algo == 8u) lane[selected] = fm1_lane_learn(lane[selected], held[k]);   /* STEP writes it, MARKOV counts it */
            }
            if (up >> k & 1u) { stop(held[k]); midi_send(0x80u | 15u, held[k], 0); }
        }

        b = fm1_input_edges(&rel);
        if (b & ~(1u << BTN_PLAY)) browse_mode = 0;
        if (b & (1u << BTN_OCT_DOWN) && oct > -2) { set.oct = (uint8_t)(oct - 1); dirty = 1; t_change = fm1_ms; }
        if (b & (1u << BTN_OCT_UP) && oct < 2) { set.oct = (uint8_t)(oct + 1); dirty = 1; t_change = fm1_ms; }
        if (b & (1u << BTN_PLAY)) { if (running) { running = 0; stopped_ms = fm1_ms; silence_lanes(); } else play_start(); }
        if (b & (1u << BTN_HOME)) goto_group(G_HOME);
        if (b & (1u << BTN_SEQ)) goto_group(G_SEQ);
        if (b & (1u << BTN_EDIT)) goto_group(G_EDIT);
        if (b & (1u << BTN_GLO)) goto_group(G_GLO);
        if (b & (1u << BTN_FX)) goto_group(G_FX);
        if (b & (1u << BTN_LFO)) goto_group(G_LFO);
        if (b & (1u << BTN_ENV)) { page = P_ENVELOPE; group_page[G_EDIT] = page; browse_mode = 0; }
        if (b & (1u << BTN_SEL)) cfg[selected].muted ^= 1u;
        if (b & (1u << BTN_REC)) { cfg[selected].seed = (uint16_t)(cfg[selected].seed * 5u + 1u); lane_remake(selected); }
        if (b & (1u << BTN_SAVE)) patch_save(save_slot);

        if ((e = fm1_enc_take(ENC_PRESETS)) != 0) browse_turn(e);
        if ((e = fm1_enc_take(ENC_SELECT)) != 0) {
            if (browse_mode == 1u) browse_family_turn(e);
            else if (browse_mode == 2u) browse_patch_group_turn(e);
            else selected = (selected + NL + (uint32_t)(e % (int32_t)NL)) % NL;
        }
        if ((e = fm1_enc_take(ENC_ALGORITHM)) != 0) {
            if (browse_mode == 1u) browse_by_turn();
            else bpm = (uint32_t)clamp((int32_t)bpm + 2 * e, 40, 240);
        }
        for (k = 0; k < 4u; k++) {
            static const uint32_t KNOB[4] = {ENC_KNOB1, ENC_KNOB2, ENC_KNOB3, ENC_KNOB4};
            if ((e = fm1_enc_take(KNOB[k])) != 0) { browse_mode = 0; param_turn(page, k, e); dirty |= page == P_SYSTEM || page == P_MIDI; t_change = fm1_ms; }
        }
        if (browse_mode && fm1_ms > browse_until) browse_mode = 0;

        midi_in();

        oct = (int8_t)set.oct;
        base = (uint32_t)((int32_t)KEY0 + 12 * oct);
        for (k = 0; k < NV; k++)                /* what sounds, on the keys of this octave */
            if (voice[k].gate && voice[k].note >= base && voice[k].note < base + 27u)
                lit |= 1u << (voice[k].note - base);
        for (k = 0; k < 27u; k++)
            fm1_led_key(KEY_LED(k), lit >> k & 1u);
        fm1_led_key(BTN_OCT_DOWN, oct < 0);
        fm1_led_key(BTN_OCT_UP, oct > 0);
        fm1_led_key(BTN_PLAY, running);
        fm1_led_key(BTN_HOME, PAGE_GROUP[page] == G_HOME);
        fm1_led_key(BTN_SEQ, PAGE_GROUP[page] == G_SEQ);
        fm1_led_key(BTN_EDIT, PAGE_GROUP[page] == G_EDIT);
        fm1_led_key(BTN_GLO, PAGE_GROUP[page] == G_GLO);
        fm1_led_key(BTN_FX, PAGE_GROUP[page] == G_FX);
        fm1_led_key(BTN_LFO, PAGE_GROUP[page] == G_LFO);
        fm1_led_key(BTN_ENV, page == P_ENVELOPE);
        fm1_led_key(BTN_SEL, cfg[selected].muted);

        idle_ok = 1;                            /* the drawing below may read MIDI meanwhile (LCD_IDLE) */
        h = ui_hash();
        if (h != shown) {                       /* something outside the lane rows changed: draw the page again */
            shown = h;
            if (browse_mode) draw_browser();
            else {
                lcd_fill(0, 0, 240, 240, TH.bg);
                draw_title();
                draw_status();
                if (page == P_HOME) draw_home_foot(); else draw_columns();
            }
            for (k = 0; k < NL; k++) row_sig[k] = ~0u;
            alfred_shown = ~0u;
        }
        if (!browse_mode)
            for (k = 0; k < NL; k++) {
                uint32_t sig = fm1_lane_step_of(lane[k]) + 1u;
                if (sig != row_sig[k]) {
                    row_sig[k] = sig;
                    draw_lane(k);
                    if (k == selected && (page == P_RHYTHM || page == P_FEEL)) draw_circle();
                }
            }
        if (!browse_mode && page == P_HOME && !running) {   /* Alfred waits in the corner: a bow on arrival, a blink now and then */
            uint32_t since = fm1_ms - stopped_ms, dip = since >= 300u && since < 700u ? 2u : since >= 700u && since < 900u ? 1u : 0u;
            uint32_t blink = (since % 4000u) >= 3000u && (since % 4000u) < 3150u, state = dip << 1 | blink;
            if (state != alfred_shown) { alfred_shown = state; draw_alfred(ALFRED_X, ALFRED_Y, 2u, dip, (int)blink); }
        }
        idle_ok = 0;

        if (dirty && quiet() && fm1_ms - t_change > 2000u) {   /* 2 s after the change, when silent (an erase stalls the sound) */
            settings_save(&set, sizeof set);
            dirty = 0;
        }
    }
}
