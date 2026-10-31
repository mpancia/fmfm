/* SPDX-License-Identifier: GPL-3.0-only */
/* Generative music box for the FM-1: four lanes, each a clock divider driving a Euclidean rhythm that picks
 * random notes and snaps them to a scale, played by Braids voices (voices/, Mutable Instruments, MIT). The lane
 * logic is Lean (Firmware/Lane.lean, proved in Proofs/Lane.lean); this file holds the sound, the controls and the
 * screen. Derived from Dinghy (see UPSTREAM.md).
 *
 * Always:  PLAY start/stop   SELECT lane   SEL mute lane   ALGORITHM tempo (SOUND page: shape)
 *          PRESETS sound preset of the lane   OCT-/OCT+ octave of the keys (they play the lane's sound)
 *          HOME held + PRESETS patch   GLO held + PRESETS MIDI channel, + ALGORITHM key   SAVE keep the patch
 * Pages:   (none) PATTERN: KNOB 1-4 hits, steps, speed, scale   EDIT SOUND: timbre, colour, level, octave
 *          ENV: attack, release, envelope-to-timbre amount
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
static const uint32_t SCALE_MASK[] = {0xAB5u, 0x5ADu, 0x295u, 0x4A9u, 0x6ADu, 0x9ADu, 0x555u, 0xFFFu,
                                      0x5ABu, 0xAD5u, 0x4E9u, 0x6CDu, 0x9B3u, 0x9B5u};
static const char *const SCALE_NAME[] = {"MAJOR", "MINOR", "PENT+", "PENT-", "DORIAN", "H.MIN", "WHOLE", "CHROM",
                                         "PHRYG", "LYDIAN", "BLUES", "UKR.D", "DBL.H", "H.MAJ"};
#define NSCALE (sizeof SCALE_MASK / sizeof SCALE_MASK[0])
static const uint32_t SPEED[] = {2, 3, 4, 6, 8, 12, 16, 24};   /* clock ticks per step: 6 = sixteenth notes */
static const char *const SPEED_NAME[] = {"1/48", "1/32", "1/24", "1/16", "1/12", "1/8", "1/6", "1/4"};
#define NSPEED (sizeof SPEED / sizeof SPEED[0])
static const char *const KEY_NAME[12] = {"C", "C#", "D", "D#", "E", "F", "F#", "G", "G#", "A", "A#", "B"};

static lean_object *lane[NL];
static struct {
    uint8_t hits, steps, speed, scale, low, span, preset, muted, last;
    uint16_t seed;
    sound_t sound;                              /* the lane's sound: a preset, then whatever the knobs changed */
} cfg[NL];
static uint32_t bpm = 100, key, running = 1, tick_acc, tick_ms, selected, patch_index;
static char patch_name[20] = "INIT";

#define NUSER 8u
#define NBROWSE (NPATCHES + NUSER)
typedef struct { uint8_t magic, bpm, key; char name[16]; patch_lane_t lane[NL]; } user_patch_t;
#define USER_MAGIC 0xA5u

static uint32_t lane_mask(uint32_t i)           /* the scale, turned to the patch's key */
{
    uint32_t m = SCALE_MASK[cfg[i].scale];
    return ((m << key) | (m >> (12u - key))) & 0xFFFu;
}

static void lane_apply(uint32_t i)
{
    lane[i] = fm1_lane_reconfigure(lane[i], cfg[i].hits, cfg[i].steps, SPEED[cfg[i].speed], lane_mask(i));
}

static void lane_report(uint32_t i, uint32_t out_ch)   /* play what the lane just started, stop what it stopped */
{
    uint32_t off = fm1_lane_off_of(lane[i]), on = fm1_lane_on_of(lane[i]);
    if (off < 128u) { stop(off); midi_send(0x80u | (out_ch + i), off, 0); }
    if (on < 128u) {
        cfg[i].last = (uint8_t)on;
        if (!cfg[i].muted) { play(on, 100, &cfg[i].sound); midi_send(0x90u | (out_ch + i), on, 100); }
    }
}

static void set_sound(uint32_t i, uint32_t index)
{
    cfg[i].preset = (uint8_t)index;
    cfg[i].sound = SOUNDS[index];
}

static void silence_lanes(uint32_t out_ch)
{
    uint32_t i;
    for (i = 0; i < NL; i++) {
        lane[i] = fm1_lane_silence(lane[i]);
        lane_report(i, out_ch);
    }
}

static void patch_set(const char *name, uint32_t new_bpm, uint32_t new_key, const patch_lane_t *src)
{
    uint32_t i;
    silence_lanes(0);
    for (i = 0; i < sizeof patch_name - 1u && name[i]; i++) patch_name[i] = name[i];
    patch_name[i] = 0;
    bpm = new_bpm; key = new_key % 12u;
    for (i = 0; i < NL; i++) {
        cfg[i].hits = src[i].hits; cfg[i].steps = src[i].steps; cfg[i].speed = src[i].speed; cfg[i].scale = src[i].scale;
        cfg[i].low = src[i].low; cfg[i].span = src[i].span; cfg[i].seed = src[i].seed;
        cfg[i].last = 0; cfg[i].muted = 0;
        set_sound(i, src[i].sound);
        lean_dec(lane[i]);
        lane[i] = fm1_lane_make(cfg[i].hits, cfg[i].steps, SPEED[cfg[i].speed], lane_mask(i), cfg[i].low, cfg[i].span,
                                0x9E3779B9u * (cfg[i].seed + 1u));
    }
}

static void lane_remake(uint32_t i)             /* a new lane from the settings: stops its note first */
{
    lane[i] = fm1_lane_silence(lane[i]);
    lane_report(i, 0);
    lean_dec(lane[i]);
    lane[i] = fm1_lane_make(cfg[i].hits, cfg[i].steps, SPEED[cfg[i].speed], lane_mask(i), cfg[i].low, cfg[i].span,
                            0x9E3779B9u * (cfg[i].seed + 1u));
}

static void patch_load(uint32_t index)
{
    user_patch_t user;
    patch_index = index;
    if (index < NPATCHES) {
        patch_set(PATCHES[index].name, PATCHES[index].bpm, PATCHES[index].key, PATCHES[index].lane);
    } else if (slot_load(index - NPATCHES, &user, sizeof user) == 0 && user.magic == USER_MAGIC) {
        patch_set(user.name, user.bpm, user.key, user.lane);
    } else {
        patch_set("EMPTY", PATCHES[0].bpm, 0, PATCHES[0].lane);
    }
}

static void patch_save(void)                    /* into the chosen user slot, or the first one if a factory patch is chosen */
{
    user_patch_t user;
    uint32_t i, slot = patch_index >= NPATCHES ? patch_index - NPATCHES : 0;
    user.magic = USER_MAGIC; user.bpm = (uint8_t)bpm; user.key = (uint8_t)key;
    for (i = 0; i < 16u; i++) user.name[i] = i < 6u ? "USER  "[i] : 0;
    user.name[4] = (char)('1' + slot);
    for (i = 0; i < NL; i++) {
        user.lane[i].hits = cfg[i].hits; user.lane[i].steps = cfg[i].steps; user.lane[i].speed = cfg[i].speed;
        user.lane[i].scale = cfg[i].scale; user.lane[i].sound = cfg[i].preset; user.lane[i].low = cfg[i].low;
        user.lane[i].span = cfg[i].span; user.lane[i].seed = cfg[i].seed;
    }
    silence_lanes(0);                           /* a flash write stalls the sound */
    slot_save(slot, &user, sizeof user);
    patch_index = NPATCHES + slot;
    for (i = 0; i < 16u && user.name[i]; i++) patch_name[i] = user.name[i];
    patch_name[i] = 0;
}

static void clock_poll(uint32_t out_ch)         /* 24 ticks a quarter note: bpm * 4 hundred-thousandths of a tick a ms */
{
    uint32_t dt = fm1_ms - tick_ms, i;
    tick_ms = fm1_ms;
    if (!running) return;
    tick_acc += dt * bpm * 4u;
    while (tick_acc >= 10000u) {
        tick_acc -= 10000u;
        for (i = 0; i < NL; i++) {
            lane[i] = fm1_lane_tick(lane[i]);
            lane_report(i, out_ch);
        }
    }
}

/* ---- the screen: a row a lane (its steps as dots, what it plays), then the patch and the sound being edited */
#define C_ACC RGB(180, 140, 255)                /* lilac */
#define C_OFF RGB(90, 90, 90)
#define C_REST RGB(50, 50, 60)
#define LANE_COLOUR(i) ((uint16_t[]){RGB(255, 120, 120), RGB(255, 190, 90), RGB(120, 220, 140), RGB(110, 170, 255)}[i])
#define ROW_Y(i) (22u + (i) * 40u)
enum { PAGE_PATTERN, PAGE_SOUND, PAGE_ENV };
static uint32_t page;
static const char *const PAGE_NAME[] = {"PATTERN", "SOUND", "ENVELOPE"};

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

static void draw_lane(uint32_t i)
{
    uint32_t k, steps = cfg[i].steps, cur = fm1_lane_step_of(lane[i]), x0 = (240u - steps * 7u) / 2u;
    uint16_t col = cfg[i].muted ? C_REST : LANE_COLOUR(i);
    char s[40], *p = s;
    cv_begin(240, 38, C_BLACK);
    for (k = 0; k < steps; k++) {
        int32_t x = (int32_t)(x0 + k * 7u);
        if (fm1_lane_hit_at_of(lane[i], k)) cv_rect(x, 2, 6, 12, k == cur ? C_WHITE : col);
        else cv_rect(x + 2, 8, 2, 2, k == cur ? C_WHITE : C_REST);
    }
    if (i == selected) cv_rect(0, 0, 2, 38, col);
    *p++ = (char)('1' + i); *p++ = ' ';
    p = put_num(p, cfg[i].hits); *p++ = '/'; p = put_num(p, cfg[i].steps); *p++ = ' ';
    p = put_str(p, SPEED_NAME[cfg[i].speed]); *p++ = ' ';
    p = put_str(p, SCALE_NAME[cfg[i].scale]);
    *p = 0;
    cv_text(6, 18, &FONT_S, s, i == selected ? col : C_OFF);
    cv_text(160, 18, &FONT_S, braids_shape_name(cfg[i].sound.shape), i == selected ? col : C_OFF);
    cv_blit(0, ROW_Y(i));
}

static void draw_status(int32_t oct, uint32_t ch)
{
    char s[40], *p = s;
    p = put_str(p, running ? "PLAY " : "STOP ");
    p = put_num(p, bpm);
    p = put_str(p, " KEY "); p = put_str(p, KEY_NAME[key]);
    p = put_str(p, " OCT"); *p++ = oct < 0 ? '-' : '+'; *p++ = (char)('0' + (oct < 0 ? -oct : oct));
    p = put_str(p, ch ? " CH" : " OMNI");
    if (ch) p = put_num(p, ch);
    *p = 0;
    draw_text_box(0, 4, 240, &FONT_S, s, C_ACC, 1);
}

static void draw_panel(void)                    /* patch, the chosen lane's sound, and the page's four values */
{
    char s[44], *p = s;
    const sound_t *snd = &cfg[selected].sound;
    lcd_fill(0, 184, 240, 56, C_BLACK);
    p = put_str(p, patch_index >= NPATCHES ? "U" : "P"); p = put_num(p, patch_index >= NPATCHES ? patch_index - NPATCHES + 1u : patch_index);
    *p++ = ' '; p = put_str(p, patch_name); *p = 0;
    draw_text_box(0, 186, 240, &FONT_S, s, C_WHITE, 1);
    p = s;
    *p++ = (char)('1' + selected); *p++ = ' ';
    p = put_str(p, SOUNDS[cfg[selected].preset].name);
    if (snd->timbre != SOUNDS[cfg[selected].preset].timbre || snd->color != SOUNDS[cfg[selected].preset].color ||
        snd->shape != SOUNDS[cfg[selected].preset].shape) *p++ = '*';
    *p = 0;
    draw_text_box(0, 204, 240, &FONT_S, s, LANE_COLOUR(selected), 1);
    p = put_str(s, PAGE_NAME[page]); *p++ = ' ';
    if (page == PAGE_PATTERN) {
        p = put_num(p, cfg[selected].hits); *p++ = ' '; p = put_num(p, cfg[selected].steps); *p++ = ' ';
        p = put_str(p, SPEED_NAME[cfg[selected].speed]);
    } else if (page == PAGE_SOUND) {
        p = put_num(p, (uint32_t)snd->timbre >> 7); *p++ = ' '; p = put_num(p, (uint32_t)snd->color >> 7); *p++ = ' ';
        p = put_num(p, snd->gain * 100u / 256u); *p++ = '%';
    } else {
        p = put_num(p, snd->attack); *p++ = ' '; p = put_num(p, snd->release); *p++ = ' '; p = put_num(p, snd->env);
    }
    *p = 0;
    draw_text_box(0, 222, 240, &FONT_S, s, C_OFF, 1);
}

/* ---- MIDI in: notes play the chosen lane's sound; from the main loop and from app_idle while the screen draws */
static struct { uint8_t oct, ch; } set = {0, 0};   /* what survives a power-off */
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

static uint32_t hash_panel(void)               /* changes whenever something draw_panel shows changes */
{
    const sound_t *snd = &cfg[selected].sound;
    uint32_t v[] = {selected, page, patch_index, cfg[selected].preset, snd->timbre, snd->color, snd->gain, snd->attack,
                    snd->release, snd->env, snd->shape, cfg[selected].hits, cfg[selected].steps, cfg[selected].speed};
    uint32_t h = 2166136261u, i;
    for (i = 0; i < sizeof v / sizeof v[0]; i++) h = (h ^ v[i]) * 16777619u;
    return h;
}

static int32_t clamp(int32_t v, int32_t lo, int32_t hi) { return v < lo ? lo : v > hi ? hi : v; }

static void knobs(void)                         /* four knobs, meaning set by the page */
{
    int32_t e1 = fm1_enc_take(ENC_KNOB1), e2 = fm1_enc_take(ENC_KNOB2), e3 = fm1_enc_take(ENC_KNOB3), e4 = fm1_enc_take(ENC_KNOB4);
    sound_t *snd = &cfg[selected].sound;
    if (!(e1 | e2 | e3 | e4)) return;
    if (page == PAGE_PATTERN) {
        int32_t s = clamp((int32_t)cfg[selected].steps + e2, 1, 32);
        cfg[selected].hits = (uint8_t)clamp((int32_t)cfg[selected].hits + e1, 0, s);
        cfg[selected].steps = (uint8_t)s;
        cfg[selected].speed = (uint8_t)clamp((int32_t)cfg[selected].speed + e3, 0, (int32_t)NSPEED - 1);
        cfg[selected].scale = (uint8_t)clamp((int32_t)cfg[selected].scale + e4, 0, (int32_t)NSCALE - 1);
        cfg[selected].hits = (uint8_t)clamp(cfg[selected].hits, 0, s);
        lane_apply(selected);
    } else if (page == PAGE_SOUND) {
        snd->timbre = (uint16_t)clamp(snd->timbre + e1 * 512, 0, 32767);
        snd->color = (uint16_t)clamp(snd->color + e2 * 512, 0, 32767);
        snd->gain = (uint16_t)clamp(snd->gain + e3 * 16, 32, 2048);
        if (e4) {                                                       /* a whole octave a click */
            cfg[selected].low = (uint8_t)clamp((int32_t)cfg[selected].low + e4 * 12, 12, 96);
            lane_remake(selected);
        }
    } else {
        snd->attack = (uint8_t)clamp(snd->attack + e1, 0, 3);
        snd->release = (uint8_t)clamp(snd->release + e2, 0, 6);
        snd->env = (uint8_t)clamp(snd->env + e3, 0, 16);
    }
}

static void app_main(void)
{
    uint32_t prev = 0, k, t_change = 0, dirty = 0, status_drawn = ~0u, panel_drawn = ~0u;
    uint64_t row_drawn[NL];
    uint8_t held[27] = {0};                     /* the note each key plays */
    if (settings_load(&set, sizeof set) || (int8_t)set.oct < -2 || (int8_t)set.oct > 2 || set.ch > 16u)
        set.oct = 0, set.ch = 0;
    for (k = 0; k < NV; k++) braids_voice_init(vmem[k]);
    for (k = 0; k < NL; k++) lane[k] = fm1_lane_make(1, 1, 1, 1, 36, 1, 1u);
    patch_load(0);
    for (k = 0; k < NL; k++) row_drawn[k] = ~0ull;
    lcd_fill(0, 0, 240, 240, C_BLACK);

    for (;;) {
        uint32_t keys, down, up, rel, b, lit = 0, st, home, glo;
        int32_t oct = (int8_t)set.oct, e;
        uint32_t base = (uint32_t)((int32_t)KEY0 + 12 * oct);
        platform_poll();
        clock_poll(0);
        home = fm1_in.buttons >> BTN_HOME & 1u;
        glo = fm1_in.buttons >> BTN_GLO & 1u;

        keys = fm1_in.notes;                    /* bit k: key k (0 = F3 .. 26 = G5) */
        down = keys & ~prev;
        up = prev & ~keys;
        prev = keys;
        for (k = 0; k < 27u; k++) {             /* a key stops the note it started: the octave may change meanwhile */
            if (down >> k & 1u) { held[k] = (uint8_t)(base + k); play(held[k], 100, &cfg[selected].sound); midi_send(0x90u | 15u, held[k], 100); }
            if (up >> k & 1u) { stop(held[k]); midi_send(0x80u | 15u, held[k], 0); }
        }

        b = fm1_input_edges(&rel);
        if (b & (1u << BTN_OCT_DOWN) && oct > -2) { set.oct = (uint8_t)(oct - 1); dirty = 1; t_change = fm1_ms; }
        if (b & (1u << BTN_OCT_UP) && oct < 2) { set.oct = (uint8_t)(oct + 1); dirty = 1; t_change = fm1_ms; }
        if (b & (1u << BTN_PLAY)) { if (running) { running = 0; silence_lanes(0); } else running = 1; }
        if (b & (1u << BTN_EDIT)) page = page == PAGE_SOUND ? PAGE_PATTERN : PAGE_SOUND;
        if (b & (1u << BTN_ENV)) page = page == PAGE_ENV ? PAGE_PATTERN : PAGE_ENV;
        if (b & (1u << BTN_SEL)) cfg[selected].muted ^= 1u;
        if (b & (1u << BTN_SAVE)) patch_save();

        if ((e = fm1_enc_take(ENC_PRESETS)) != 0) {
            if (home) patch_load((uint32_t)clamp((int32_t)patch_index + e, 0, (int32_t)NBROWSE - 1));
            else if (glo) { set.ch = (uint8_t)clamp((int32_t)set.ch + e, 0, 16); dirty = 1; t_change = fm1_ms; }
            else set_sound(selected, (uint32_t)clamp((int32_t)cfg[selected].preset + e, 0, (int32_t)NSOUNDS - 1));
        }
        if ((e = fm1_enc_take(ENC_SELECT)) != 0) selected = (selected + NL + (uint32_t)(e % (int32_t)NL)) % NL;
        if ((e = fm1_enc_take(ENC_ALGORITHM)) != 0) {
            if (glo) { key = (uint32_t)clamp((int32_t)key + e, 0, 11); for (k = 0; k < NL; k++) lane_apply(k); }
            else if (page == PAGE_SOUND) cfg[selected].sound.shape = (uint8_t)clamp(cfg[selected].sound.shape + e, 0, (int32_t)BRAIDS_SHAPES - 1);
            else bpm = (uint32_t)clamp((int32_t)bpm + 2 * e, 40, 240);
        }
        knobs();

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
        fm1_led_key(BTN_EDIT, page == PAGE_SOUND);
        fm1_led_key(BTN_ENV, page == PAGE_ENV);
        fm1_led_key(BTN_SEL, cfg[selected].muted);

        idle_ok = 1;                            /* the drawing below may read MIDI meanwhile (LCD_IDLE) */
        for (k = 0; k < NL; k++) {
            uint64_t sig = (uint64_t)fm1_lane_step_of(lane[k]) | (uint64_t)cfg[k].hits << 6 | (uint64_t)cfg[k].steps << 12
                         | (uint64_t)cfg[k].speed << 18 | (uint64_t)cfg[k].scale << 22 | (uint64_t)cfg[k].sound.shape << 26
                         | (uint64_t)cfg[k].muted << 32 | (uint64_t)(k == selected) << 33 | (uint64_t)patch_index << 34;
            if (sig != row_drawn[k]) { row_drawn[k] = sig; draw_lane(k); }
        }
        if ((st = (uint32_t)(oct + 2) | (uint32_t)set.ch << 4 | bpm << 10 | running << 20 | key << 21) != status_drawn) {
            status_drawn = st;
            draw_status(oct, set.ch);
        }
        st = hash_panel();
        if (st != panel_drawn) { panel_drawn = st; draw_panel(); }
        idle_ok = 0;

        if (dirty && quiet() && fm1_ms - t_change > 2000u) {   /* 2 s after the change, when silent (an erase stalls the sound) */
            settings_save(&set, sizeof set);
            dirty = 0;
        }
    }
}
