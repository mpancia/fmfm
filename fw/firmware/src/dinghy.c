/* SPDX-License-Identifier: GPL-3.0-only */
/* Generative music box for the FM-1: four lanes, each a clock divider driving a Euclidean rhythm; a note
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
#define LCD_IDLE app_idle
#include "platform.c"
#include "fm1_lean.h"
#include "voice.h"
#include "presets.h"

/* ---- the sound (audio ISR: keep it short, no flash, no screen) */
#define NV 6u                                   /* voices */
static uint8_t vmem[NV][BRAIDS_VOICE_BYTES] __attribute__((aligned(8), section(".pool")));
static struct {
    volatile int32_t gate;                      /* target level: 0 = released */
    volatile int32_t pitch, timbre, color;      /* the voice's pitch (1/128 semitone) and its two timbre values */
    volatile uint16_t gain;                     /* levels the shapes out, 256 = 1 */
    volatile uint8_t shape, attack, release, env, strike;
    int32_t amp;                                /* the level now: glides to gate, no clicks */
    uint32_t age;
    uint8_t note;
} voice[NV];

static const int32_t ATTACK[4] = {1024, 256, 64, 12};              /* level steps a sample: 2 ms to 190 ms */
static const int32_t RELEASE[7] = {250, 80, 25, 10, 4, 2, 1};      /* 10 ms to 2.3 s */

static void render_voice(uint32_t v, int32_t *out, uint32_t n)
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
            int32_t s;
            if (amp < g) { amp += up; if (amp > g) amp = g; }
            else if (amp > g) { amp -= down; if (amp < g) amp = g; }
            s = (((int32_t)block[j] * voice[v].gain >> 8) * (amp >> 4)) >> 15;
            out[2u * (i + j)] += s;
            out[2u * (i + j) + 1u] += s;
        }
    }
    voice[v].amp = amp;
}

static void app_audio(int32_t *out, uint32_t n)
{
    uint32_t v;
    for (v = 0; v < NV; v++)
        if (voice[v].amp || voice[v].gate)
            render_voice(v, out, n);
}

/* ---- notes (main loop) */
static uint32_t ages;

static void play(uint32_t note, uint32_t vel, const sound_t *sound)
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
static const uint16_t SCALE_MASK[] = {0xAB5, 0x5AD, 0x295, 0x4A9, 0x6AD, 0x9AD, 0x555, 0xFFF,
                                      0x5AB, 0xAD5, 0x4E9, 0x6CD, 0x9B3, 0x9B5};
static const char *const SCALE_NAME[] = {"MAJOR", "MINOR", "PENT+", "PENT-", "DORIAN", "H.MIN", "WHOLE", "CHROM",
                                         "PHRYG", "LYDIAN", "BLUES", "UKR.D", "DBL.H", "H.MAJ"};
#define NSCALE (sizeof SCALE_MASK / sizeof SCALE_MASK[0])
static const uint8_t SPEED[] = {2, 3, 4, 6, 8, 12, 16, 24};   /* clock ticks per step: 6 = sixteenth notes */
static const char *const SPEED_NAME[] = {"1/48", "1/32", "1/24", "1/16", "1/12", "1/8", "1/6", "1/4"};
#define NSPEED (sizeof SPEED / sizeof SPEED[0])
static const char *const ALGO_NAME[] = {"RANDOM", "WALK", "UP", "DOWN", "BOUNCE", "LOOP"};
#define NALGO (sizeof ALGO_NAME / sizeof ALGO_NAME[0])
static const char *const CHORD_NAME[] = {"OFF", "SCALE", "TRIAD"};
static const char *const KEY_NAME[12] = {"C", "C#", "D", "D#", "E", "F", "F#", "G", "G#", "A", "A#", "B"};
/* chord progressions: semitones above the key, one chord a step; index 0 is no progression */
static const uint8_t PROGRESSION[][4] = {{0, 0, 0, 0}, {0, 5, 7, 0}, {0, 7, 9, 5}, {9, 5, 0, 7}, {2, 7, 0, 0},
                                         {0, 8, 3, 10}, {0, 4, 5, 7}, {0, 5, 7, 0}};
static const char *const PROGRESSION_NAME[] = {"OFF", "I-IV-V-I", "I-V-vi-IV", "vi-IV-I-V", "ii-V-I-I", "i-VI-III-VII",
                                               "I-iii-IV-V", "i-iv-v-i"};
#define NPROGRESSION (sizeof PROGRESSION_NAME / sizeof PROGRESSION_NAME[0])
static const uint8_t RATE_BARS[] = {1, 2, 4};
static const uint16_t ATTACK_MS[4] = {2, 6, 25, 190};
static const uint16_t RELEASE_MS[7] = {10, 30, 90, 230, 580, 1200, 2300};
static const char *const FAMILY_NAME[] = {"ALL", "ANALOG", "FILTER", "VOICE", "FM", "PHYSICAL", "PERCUSSION", "WAVETABLE", "NOISE"};
static const uint8_t FAMILY_FIRST[] = {0, 0, 17, 21, 25, 28, 32, 37, 41}, FAMILY_LAST[] = {47, 16, 20, 24, 27, 31, 36, 40, 47};
#define NFAMILY (sizeof FAMILY_NAME / sizeof FAMILY_NAME[0])

static lean_object *lane[NL];
static struct {
    uint8_t hits, steps, speed, scale, low, span, preset, muted, algo, chance, amount, mutate, chord, level;
    uint16_t seed;
    sound_t sound;                              /* the lane's sound: a preset, then whatever the knobs changed */
} cfg[NL];
static uint32_t bpm = 100, key, progression, rate_bars = 1, scale_lock, running = 1, tick_acc, tick_ms, tick_count, chord_index;
static uint32_t selected, patch_index, save_slot, midi_out_base;
static char patch_name[20] = "INIT";

#define NUSER 8u
#define NBROWSE (NPATCHES + NUSER)
typedef struct { uint8_t magic, bpm, key, progression, rate, scale_lock; char name[16]; patch_lane_t lane[NL]; } user_patch_t;
#define USER_MAGIC 0xA6u

static uint32_t rotate12(uint32_t m, uint32_t r)
{
    r %= 12u;
    return ((m << r) | (m >> (12u - r))) & 0xFFFu;
}

static uint32_t triad(uint32_t m, uint32_t root)   /* the 1st, 3rd and 5th degree of the scale from the root */
{
    uint32_t tone[12], n = 0, d, out = 0;
    for (d = 0; d < 12u; d++)
        if (m >> ((root + d) % 12u) & 1u) tone[n++] = (root + d) % 12u;
    if (!n) return m;
    for (d = 0; d < 3u; d++) out |= 1u << tone[(d * 2u) % n];
    return out;
}

static uint32_t chord_root(void) { return progression ? PROGRESSION[progression][chord_index & 3u] : 0u; }

static uint32_t lane_mask(uint32_t i)           /* the scale, turned to the key and the current chord */
{
    uint32_t scale = scale_lock ? scale_lock - 1u : cfg[i].scale;
    uint32_t root = key + (cfg[i].chord && progression ? chord_root() : 0u);
    uint32_t m = rotate12(SCALE_MASK[scale], root);
    return cfg[i].chord == 2u ? triad(m, root % 12u) : m;
}

static void lane_apply(uint32_t i)
{
    lane[i] = fm1_lane_reconfigure(lane[i], cfg[i].hits, cfg[i].steps, SPEED[cfg[i].speed], lane_mask(i));
    lane[i] = fm1_lane_set_notes(lane[i], cfg[i].algo, cfg[i].chance, cfg[i].amount, cfg[i].mutate);
}

static void lane_report(uint32_t i)             /* play what the lane just started, stop what it stopped */
{
    uint32_t off = fm1_lane_off_of(lane[i]), on = fm1_lane_on_of(lane[i]);
    if (off < 128u) { stop(off); midi_send(0x80u | (midi_out_base + i), off, 0); }
    if (on < 128u && !cfg[i].muted && cfg[i].level) {
        uint32_t vel = 100u * cfg[i].level / 100u;
        play(on, vel ? vel : 1u, &cfg[i].sound);
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
}

static void lanes_remask(void)                  /* the key, scale lock or chord changed */
{
    uint32_t i;
    for (i = 0; i < NL; i++) lane_apply(i);
}

static void patch_set(const char *name, uint32_t new_bpm, uint32_t new_key, uint32_t prog, uint32_t rate, uint32_t lock,
                      const patch_lane_t *src)
{
    uint32_t i;
    silence_lanes();
    for (i = 0; i < sizeof patch_name - 1u && name[i]; i++) patch_name[i] = name[i];
    patch_name[i] = 0;
    bpm = new_bpm; key = new_key % 12u; progression = prog < NPROGRESSION ? prog : 0u; rate_bars = rate; scale_lock = lock;
    chord_index = 0; tick_count = 0;
    for (i = 0; i < NL; i++) {
        cfg[i].hits = src[i].hits; cfg[i].steps = src[i].steps; cfg[i].speed = src[i].speed; cfg[i].scale = src[i].scale;
        cfg[i].low = src[i].low; cfg[i].span = src[i].span; cfg[i].seed = src[i].seed; cfg[i].algo = src[i].algo;
        cfg[i].chance = src[i].chance; cfg[i].amount = src[i].amount; cfg[i].mutate = src[i].mutate;
        cfg[i].chord = src[i].chord; cfg[i].level = src[i].level; cfg[i].muted = 0;
        set_sound(i, src[i].sound);
        lean_dec(lane[i]);
        lane[i] = fm1_lane_make(cfg[i].hits, cfg[i].steps, SPEED[cfg[i].speed], lane_mask(i), cfg[i].low, cfg[i].span,
                                0x9E3779B9u * (cfg[i].seed + 1u));
        lane[i] = fm1_lane_set_notes(lane[i], cfg[i].algo, cfg[i].chance, cfg[i].amount, cfg[i].mutate);
    }
}

static void patch_load(uint32_t index)
{
    user_patch_t user;
    patch_index = index;
    if (index < NPATCHES) {
        const patch_t *p = &PATCHES[index];
        patch_set(p->name, p->bpm, p->key, p->progression, p->rate, p->scale_lock, p->lane);
    } else if (slot_load(index - NPATCHES, &user, sizeof user) == 0 && user.magic == USER_MAGIC) {
        patch_set(user.name, user.bpm, user.key, user.progression, user.rate, user.scale_lock, user.lane);
    } else {
        const patch_t *p = &PATCHES[0];
        patch_set("EMPTY", p->bpm, 0, 0, 1, 0, p->lane);
    }
}

static void patch_save(uint32_t slot)
{
    user_patch_t user;
    uint32_t i;
    user.magic = USER_MAGIC; user.bpm = (uint8_t)bpm; user.key = (uint8_t)key; user.progression = (uint8_t)progression;
    user.rate = (uint8_t)rate_bars; user.scale_lock = (uint8_t)scale_lock;
    for (i = 0; i < sizeof user.name; i++) user.name[i] = 0;
    user.name[0] = 'U'; user.name[1] = 'S'; user.name[2] = 'E'; user.name[3] = 'R'; user.name[4] = ' '; user.name[5] = (char)('1' + slot);
    for (i = 0; i < NL; i++) {
        patch_lane_t *d = &user.lane[i];
        d->hits = cfg[i].hits; d->steps = cfg[i].steps; d->speed = cfg[i].speed; d->scale = cfg[i].scale;
        d->sound = cfg[i].preset; d->low = cfg[i].low; d->span = cfg[i].span; d->algo = cfg[i].algo;
        d->chance = cfg[i].chance; d->amount = cfg[i].amount; d->mutate = cfg[i].mutate; d->chord = cfg[i].chord;
        d->level = cfg[i].level; d->seed = cfg[i].seed;
    }
    silence_lanes();                            /* a flash write stalls the sound */
    slot_save(slot, &user, sizeof user);
    patch_index = NPATCHES + slot;
    for (i = 0; i < sizeof patch_name - 1u && user.name[i]; i++) patch_name[i] = user.name[i];
    patch_name[i] = 0;
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
enum { G_HOME, G_SEQ, G_EDIT, G_GLO };
enum { P_HOME, P_RHYTHM, P_NOTES, P_RANGE, P_SOUND, P_ENVELOPE, P_MIX, P_HARMONY, P_SYSTEM, P_MIDI, P_BANKS, NPAGES };
static const char *const GROUP_NAME[] = {"HOME", "SEQ", "EDIT", "GLO"};
static const uint8_t GROUP_PAGE[4][4] = {{P_HOME, 255, 255, 255}, {P_RHYTHM, P_NOTES, P_RANGE, 255},
                                         {P_SOUND, P_ENVELOPE, P_MIX, 255}, {P_HARMONY, P_SYSTEM, P_MIDI, P_BANKS}};
static const uint8_t PAGE_GROUP[NPAGES] = {G_HOME, G_SEQ, G_SEQ, G_SEQ, G_EDIT, G_EDIT, G_EDIT, G_GLO, G_GLO, G_GLO, G_GLO};
static const char *const PAGE_NAME[NPAGES] = {"OVERVIEW", "RHYTHM", "NOTES", "RANGE", "SOUND", "ENVELOPE", "MIX", "HARMONY",
                                              "SYSTEM", "MIDI", "BANKS"};
static const char *const PAGE_LABEL[NPAGES][4] = {
    {"HITS", "STEPS", "SPEED", "CHANCE"}, {"HITS", "STEPS", "SPEED", "CHANCE"}, {"ALGORITHM", "AMOUNT", "MUTATE", "RANGE"},
    {"SCALE", "LOW NOTE", "CHORD", ""}, {"SHAPE", "TIMBRE", "COLOUR", "LEVEL"}, {"ATTACK", "RELEASE", "ENV>TIMBRE", ""},
    {"LANE 1", "LANE 2", "LANE 3", "LANE 4"}, {"KEY", "SCALE LOCK", "CHORDS", "CHANGE"}, {"TEMPO", "KEYS OCTAVE", "", ""},
    {"MIDI IN", "MIDI OUT", "", ""}, {"PATCH", "SAVE TO", "", ""}};
static uint32_t page = P_HOME, group_page[4] = {P_HOME, P_RHYTHM, P_SOUND, P_HARMONY};
static uint32_t browse_mode, browse_until, browse_family, browse_pos;   /* 0 closed, 1 sounds, 2 patches */
static uint8_t browse_list[NSOUNDS];
static uint32_t browse_count;

static struct { uint8_t oct, ch; } set = {0, 0};   /* what survives a power-off */

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
    case P_NOTES:
        if (k == 0) { p = put_str(p, ALGO_NAME[cfg[selected].algo]); *fill = frac(cfg[selected].algo, NALGO - 1u); }
        if (k == 1) {
            if (cfg[selected].algo == 1u) p = put_str(p, "STEP ");
            else if (cfg[selected].algo == 5u) p = put_str(p, "LOOP ");
            p = put_num(p, cfg[selected].amount); *fill = frac(cfg[selected].amount, 16);
        }
        if (k == 2) { p = put_num(p, cfg[selected].mutate); *p++ = '%'; *fill = frac(cfg[selected].mutate, 100); }
        if (k == 3) { p = put_num(p, cfg[selected].span); p = put_str(p, " ST"); *fill = frac(cfg[selected].span, 36); }
        break;
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
    case P_HARMONY:
        if (k == 0) { p = put_str(p, KEY_NAME[key]); *fill = frac(key, 11); }
        if (k == 1) { p = put_str(p, scale_lock ? SCALE_NAME[scale_lock - 1u] : "LANES"); *fill = frac(scale_lock, NSCALE); }
        if (k == 2) { p = put_str(p, PROGRESSION_NAME[progression]); *fill = frac(progression, NPROGRESSION - 1u); }
        if (k == 3) { p = put_num(p, rate_bars); p = put_str(p, " BAR"); *fill = frac(rate_bars, 4); }
        break;
    case P_SYSTEM:
        if (k == 0) { p = put_num(p, bpm); p = put_str(p, " BPM"); *fill = frac((int32_t)bpm - 40, 200); }
        if (k == 1) { *p++ = set.oct & 0x80u ? '-' : '+'; p = put_num(p, (int8_t)set.oct < 0 ? (uint32_t)-(int8_t)set.oct : set.oct); *fill = frac((int8_t)set.oct + 2, 4); }
        break;
    case P_MIDI:
        if (k == 0) { if (set.ch) { p = put_str(p, "CH "); p = put_num(p, set.ch); } else p = put_str(p, "OMNI"); *fill = frac(set.ch, 16); }
        if (k == 1) { p = put_str(p, "CH "); p = put_num(p, midi_out_base + 1u); p = put_str(p, "-"); p = put_num(p, midi_out_base + 4u); *fill = frac(midi_out_base, 12); }
        break;
    case P_BANKS:
        if (k == 0) { p = patch_index >= NPATCHES ? put_str(p, "U") : put_str(p, "P"); p = put_num(p, patch_index >= NPATCHES ? patch_index - NPATCHES + 1u : patch_index + 1u); *fill = frac(patch_index, NBROWSE - 1u); }
        if (k == 1) { p = put_str(p, "USER "); p = put_num(p, save_slot + 1u); *fill = frac(save_slot, NUSER - 1u); }
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
        }
        if (k == 2) cfg[selected].speed = (uint8_t)clamp(cfg[selected].speed + d, 0, (int32_t)NSPEED - 1);
        if (k == 3) cfg[selected].chance = (uint8_t)clamp(cfg[selected].chance + 5 * d, 0, 100);
        lane_apply(selected);
        break;
    case P_NOTES:
        if (k == 0) cfg[selected].algo = (uint8_t)clamp(cfg[selected].algo + d, 0, (int32_t)NALGO - 1);
        if (k == 1) cfg[selected].amount = (uint8_t)clamp(cfg[selected].amount + d, 1, 16);
        if (k == 2) cfg[selected].mutate = (uint8_t)clamp(cfg[selected].mutate + 5 * d, 0, 100);
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
        break;
    case P_MIDI:
        if (k == 0) set.ch = (uint8_t)clamp(set.ch + d, 0, 16);
        if (k == 1) midi_out_base = (uint32_t)clamp((int32_t)midi_out_base + d, 0, 12);
        break;
    case P_BANKS:
        if (k == 0) patch_load((uint32_t)clamp((int32_t)patch_index + d, 0, (int32_t)NBROWSE - 1));
        if (k == 1) save_slot = (uint32_t)clamp((int32_t)save_slot + d, 0, (int32_t)NUSER - 1);
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
static void browse_build(void)                  /* the sounds of the chosen family, in preset order */
{
    uint32_t i;
    browse_count = 0;
    for (i = 0; i < NSOUNDS; i++)
        if (SOUNDS[i].shape >= FAMILY_FIRST[browse_family] && SOUNDS[i].shape <= FAMILY_LAST[browse_family])
            browse_list[browse_count++] = (uint8_t)i;
}

static void browse_open(uint32_t mode)
{
    if (browse_mode != mode) {
        browse_mode = mode;
        if (mode == 1u) {
            uint32_t i;
            browse_family = 0;
            browse_build();
            for (i = 0; i < browse_count && browse_list[i] != cfg[selected].preset; i++) {}
            browse_pos = i < browse_count ? i : 0u;
        } else {
            browse_pos = patch_index;
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
        browse_pos = (uint32_t)clamp((int32_t)browse_pos + d, 0, (int32_t)NBROWSE - 1);
        patch_load(browse_pos);
    }
}

static void browse_family_turn(int32_t d)       /* SELECT while sounds are open: another family */
{
    uint32_t family = (uint32_t)clamp((int32_t)browse_family + d, 0, (int32_t)NFAMILY - 1);
    browse_open(1u);
    if (family != browse_family) { browse_family = family; browse_build(); browse_pos = 0; }
    if (browse_count) set_sound(selected, browse_list[browse_pos]);
}

/* ---- the screen */
#define C_ACC RGB(180, 140, 255)                /* lilac */
#define C_OFF RGB(90, 90, 90)
#define C_REST RGB(50, 50, 60)
#define C_BAR RGB(70, 70, 90)
#define LANE_COLOUR(i) ((uint16_t[]){RGB(255, 120, 120), RGB(255, 190, 90), RGB(120, 220, 140), RGB(110, 170, 255)}[i])
#define STRIP_Y 22u
static uint32_t row_h(void) { return page == P_HOME ? 38u : 20u; }

static void draw_lane(uint32_t i)
{
    uint32_t k, steps = cfg[i].steps, cur = fm1_lane_step_of(lane[i]), h = row_h(), x0 = page == P_HOME ? (240u - steps * 7u) / 2u : 16u;
    uint16_t col = cfg[i].muted || !cfg[i].level ? C_REST : LANE_COLOUR(i);
    char s[40], *p = s;
    cv_begin(240, h, C_BLACK);
    for (k = 0; k < steps; k++) {
        int32_t x = (int32_t)(x0 + k * 7u);
        if (fm1_lane_hit_at_of(lane[i], k)) cv_rect(x, 2, 6, page == P_HOME ? 12 : 10, k == cur ? C_WHITE : col);
        else cv_rect(x + 2, page == P_HOME ? 8 : 6, 2, 2, k == cur ? C_WHITE : C_REST);
    }
    if (i == selected) cv_rect(0, 0, 2, (int32_t)h, col);
    if (page == P_HOME) {
        *p++ = (char)('1' + i); *p++ = ' ';
        p = put_num(p, cfg[i].hits); *p++ = '/'; p = put_num(p, cfg[i].steps); *p++ = ' ';
        p = put_str(p, SPEED_NAME[cfg[i].speed]); *p++ = ' ';
        p = put_str(p, SCALE_NAME[scale_lock ? scale_lock - 1u : cfg[i].scale]);
        *p = 0;
        cv_text(6, 18, &FONT_S, s, i == selected ? col : C_OFF);
        cv_text(160, 18, &FONT_S, braids_shape_name(cfg[i].sound.shape), i == selected ? col : C_OFF);
    } else {
        s[0] = (char)('1' + i); s[1] = 0;
        cv_text(5, 2, &FONT_S, s, i == selected ? col : C_OFF);
    }
    cv_blit(0, STRIP_Y + i * h);
}

static void draw_tabs(void)
{
    uint32_t g;
    char s[12], *p = s;
    cv_begin(240, 18, C_BLACK);
    for (g = 0; g < 4u; g++) {
        uint16_t on = PAGE_GROUP[page] == g;
        int32_t x = (int32_t)(g * 48u);
        if (on) cv_rect(x, 0, 46, 18, C_ACC);
        cv_text(x + (int32_t)(23u - 4u * (g == 0u ? 4u : g == 2u ? 4u : g == 1u ? 3u : 3u)), 1, &FONT_S, GROUP_NAME[g], on ? C_BLACK : C_OFF);
    }
    p = put_num(p, bpm);
    *p = 0;
    cv_text(200, 1, &FONT_S, s, running ? C_WHITE : C_OFF);
    cv_blit(0, 0);
}

static void draw_cell(uint32_t k, const char *label, const char *value, uint32_t fill)
{
    uint32_t x = 4u + (k & 1u) * 120u, y = (page == P_HOME ? 0u : 104u) + (k >> 1) * 42u;
    uint16_t col = page == P_MIX ? LANE_COLOUR(k) : C_WHITE;
    cv_begin(112, 40, C_BLACK);
    cv_text(0, 0, &FONT_S, label, C_OFF);
    cv_text(0, 15, &FONT_S, value, col);
    cv_rect(0, 33, 112, 3, C_REST);
    cv_rect(0, 33, (int32_t)(fill * 112u / 255u), 3, page == P_MIX ? LANE_COLOUR(k) : C_ACC);
    cv_blit(x, y);
}

static void draw_cells(void)
{
    uint32_t k;
    char value[24];
    uint32_t fill;
    lcd_fill(0, 102, 240, 84, C_BLACK);
    for (k = 0; k < 4u; k++) {
        if (!PAGE_LABEL[page][k][0]) continue;
        param_text(page, k, value, &fill);
        draw_cell(k, PAGE_LABEL[page][k], value, fill);
    }
}

static void draw_footer(void)
{
    char s[44], *p = s;
    const sound_t *snd = &cfg[selected].sound;
    lcd_fill(0, 186, 240, 54, C_BLACK);
    p = put_str(p, patch_index >= NPATCHES ? "U" : "P"); p = put_num(p, patch_index >= NPATCHES ? patch_index - NPATCHES + 1u : patch_index + 1u);
    *p++ = ' '; p = put_str(p, patch_name); *p = 0;
    draw_text_box(0, 188, 240, &FONT_S, s, C_WHITE, 1);
    p = s;
    *p++ = (char)('1' + selected); *p++ = ' ';
    p = put_str(p, SOUNDS[cfg[selected].preset].name);
    if (snd->timbre != SOUNDS[cfg[selected].preset].timbre || snd->color != SOUNDS[cfg[selected].preset].color ||
        snd->shape != SOUNDS[cfg[selected].preset].shape) *p++ = '*';
    *p = 0;
    draw_text_box(0, 206, 240, &FONT_S, s, LANE_COLOUR(selected), 1);
    p = put_str(s, running ? "" : "STOP ");
    p = put_str(p, PAGE_NAME[page]); p = put_str(p, "  KEY "); p = put_str(p, KEY_NAME[key]);
    if (progression) { p = put_str(p, " CHORD "); p = put_str(p, KEY_NAME[(key + chord_root()) % 12u]); }
    *p = 0;
    draw_text_box(0, 224, 240, &FONT_S, s, C_ACC, 1);
}

static void draw_browser(void)
{
    uint32_t row, rows = 9, first, count = browse_mode == 1u ? browse_count : NBROWSE;
    char s[44], *p = s;
    lcd_fill(0, 20, 240, 220, C_BLACK);
    p = put_str(s, browse_mode == 1u ? "SOUNDS  " : "PATCHES  ");
    if (browse_mode == 1u) p = put_str(p, FAMILY_NAME[browse_family]);
    *p = 0;
    draw_text_box(0, 24, 240, &FONT_S, s, C_ACC, 1);
    first = browse_pos < rows / 2u ? 0u : browse_pos - rows / 2u;
    if (first + rows > count) first = count > rows ? count - rows : 0u;
    for (row = 0; row < rows && first + row < count; row++) {
        uint32_t index = first + row;
        const char *name;
        char line[44], *q = line;
        uint16_t col = index == browse_pos ? LANE_COLOUR(selected) : C_OFF;
        if (browse_mode == 1u) name = SOUNDS[browse_list[index]].name;
        else if (index < NPATCHES) name = PATCHES[index].name;
        else name = "USER SLOT";
        *q++ = index == browse_pos ? '>' : ' ';
        q = put_num(q, index + 1u); *q++ = ' ';
        q = put_str(q, name);
        if (browse_mode == 2u && index >= NPATCHES) { *q++ = ' '; q = put_num(q, index - NPATCHES + 1u); }
        *q = 0;
        draw_text_box(4, 48 + row * 20, 232, &FONT_S, line, col, 0);
    }
    draw_text_box(0, 226, 240, &FONT_S, browse_mode == 1u ? "PRESETS SCROLL  SELECT FAMILY" : "PRESETS SCROLL  SAVE KEEPS", C_REST, 1);
}

/* ---- MIDI in: notes play the chosen lane's sound; from the main loop and from app_idle while the screen draws */
static uint32_t idle_ok;

static void midi_in(void)
{
    uint8_t st, d1, d2;
    while (midi_get(&st, &d1, &d2) != 0) {
        uint32_t ty = st & 0xF0u;
        if (set.ch && (st & 15u) != set.ch - 1u) continue;
        if (ty == 0x90u && d2) play(d1, d2, &cfg[selected].sound);
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
                    browse_family, chord_index, save_slot, midi_out_base, set.oct, set.ch};
    for (i = 0; i < sizeof cfg; i++) h = (h ^ b[i]) * 16777619u;
    for (i = 0; i < sizeof g / sizeof g[0]; i++) h = (h ^ g[i]) * 16777619u;
    return h;
}

static void app_main(void)
{
    uint32_t prev = 0, k, t_change = 0, dirty = 0, shown = 0;
    uint32_t row_sig[NL];
    uint8_t held[27] = {0};                     /* the note each key plays */
    if (settings_load(&set, sizeof set) || (int8_t)set.oct < -2 || (int8_t)set.oct > 2 || set.ch > 16u)
        set.oct = 0, set.ch = 0;
    for (k = 0; k < NV; k++) braids_voice_init(vmem[k]);
    for (k = 0; k < NL; k++) lane[k] = fm1_lane_make(1, 1, 1, 1, 36, 1, 1u);
    patch_load(0);
    lcd_fill(0, 0, 240, 240, C_BLACK);

    for (;;) {
        uint32_t keys, down, up, rel, b, lit = 0, h;
        int32_t oct = (int8_t)set.oct, e;
        uint32_t base = (uint32_t)((int32_t)KEY0 + 12 * oct);
        platform_poll();
        clock_poll();

        keys = fm1_in.notes;                    /* bit k: key k (0 = F3 .. 26 = G5) */
        down = keys & ~prev;
        up = prev & ~keys;
        prev = keys;
        for (k = 0; k < 27u; k++) {             /* a key stops the note it started: the octave may change meanwhile */
            if (down >> k & 1u) { held[k] = (uint8_t)(base + k); play(held[k], 100, &cfg[selected].sound); midi_send(0x90u | 15u, held[k], 100); }
            if (up >> k & 1u) { stop(held[k]); midi_send(0x80u | 15u, held[k], 0); }
        }

        b = fm1_input_edges(&rel);
        if (b & ~(1u << BTN_PLAY)) browse_mode = 0;
        if (b & (1u << BTN_OCT_DOWN) && oct > -2) { set.oct = (uint8_t)(oct - 1); dirty = 1; t_change = fm1_ms; }
        if (b & (1u << BTN_OCT_UP) && oct < 2) { set.oct = (uint8_t)(oct + 1); dirty = 1; t_change = fm1_ms; }
        if (b & (1u << BTN_PLAY)) { if (running) { running = 0; silence_lanes(); } else play_start(); }
        if (b & (1u << BTN_HOME)) goto_group(G_HOME);
        if (b & (1u << BTN_SEQ)) goto_group(G_SEQ);
        if (b & (1u << BTN_EDIT)) goto_group(G_EDIT);
        if (b & (1u << BTN_GLO)) goto_group(G_GLO);
        if (b & (1u << BTN_SEL)) cfg[selected].muted ^= 1u;
        if (b & (1u << BTN_REC)) { cfg[selected].seed = (uint16_t)(cfg[selected].seed * 5u + 1u); lane_remake(selected); }
        if (b & (1u << BTN_SAVE)) patch_save(save_slot);

        if ((e = fm1_enc_take(ENC_PRESETS)) != 0) browse_turn(e);
        if ((e = fm1_enc_take(ENC_SELECT)) != 0) {
            if (browse_mode == 1u) browse_family_turn(e);
            else if (browse_mode == 2u) { browse_pos = (uint32_t)clamp((int32_t)browse_pos + 10 * e, 0, (int32_t)NBROWSE - 1); browse_until = fm1_ms + 2500u; patch_load(browse_pos); }
            else selected = (selected + NL + (uint32_t)(e % (int32_t)NL)) % NL;
        }
        if ((e = fm1_enc_take(ENC_ALGORITHM)) != 0) bpm = (uint32_t)clamp((int32_t)bpm + 2 * e, 40, 240);
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
        fm1_led_key(BTN_SEL, cfg[selected].muted);

        idle_ok = 1;                            /* the drawing below may read MIDI meanwhile (LCD_IDLE) */
        h = ui_hash();
        if (h != shown) {                       /* something outside the lane rows changed: draw the page again */
            shown = h;
            if (browse_mode) draw_browser();
            else {
                lcd_fill(0, 0, 240, 240, C_BLACK);
                draw_tabs();
                draw_footer();
                if (page != P_HOME) draw_cells();
            }
            for (k = 0; k < NL; k++) row_sig[k] = ~0u;
        }
        if (!browse_mode)
            for (k = 0; k < NL; k++) {
                uint32_t sig = fm1_lane_step_of(lane[k]) + 1u;
                if (sig != row_sig[k]) { row_sig[k] = sig; draw_lane(k); }
            }
        idle_ok = 0;

        if (dirty && quiet() && fm1_ms - t_change > 2000u) {   /* 2 s after the change, when silent (an erase stalls the sound) */
            settings_save(&set, sizeof set);
            dirty = 0;
        }
    }
}
