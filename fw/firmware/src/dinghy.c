/* SPDX-License-Identifier: GPL-3.0-only */
/* Generative music box for the FM-1: four lanes, each a clock divider driving a Euclidean rhythm that picks
 * random notes and snaps them to a scale. The lane logic is Lean (Firmware/Lane.lean, proved in Proofs/Lane.lean);
 * this file holds the sound, the controls and the screen. Derived from Dinghy (see UPSTREAM.md).
 *
 *   PLAY       start / stop the clock
 *   SELECT     choose a lane
 *   KNOB 1-4   hits per bar, steps per bar, speed, scale (of the chosen lane)
 *   ALGORITHM  tempo
 *   PRESETS    MIDI channel for notes coming in
 *   OCT- OCT+  octave of the keys; the keys play the sines too
 *
 * Rules of the chip (no FPU, no 64-bit division): docs/RULES.md. Platform calls: docs/API.md. */
static void app_idle(void);
#define LCD_IDLE app_idle
#include "platform.c"
#include "fm1_lean.h"
#include "braids.h"

/* ---- the sound (runs in the audio ISR: keep it short, no flash, no screen) */
#define NV 6u                                   /* voices */
static struct {
    volatile uint32_t inc;                      /* phase step per frame: f * 2^32 / 44100 */
    volatile uint32_t mod_inc;                  /* the FM modulator's step */
    volatile int32_t gate;                      /* target level, Q15: 0 = released */
    volatile int32_t attenuation;               /* feedback FM: less index on high notes */
    int32_t amp;                                /* the level now: glides to gate, no clicks */
    uint32_t age;
    braids_t osc;
    volatile uint8_t shape;
    uint8_t note;
} voice[NV];

/* one sample of a voice. The timbre follows the level: bright and narrow at the attack, softer as it dies away. */
static int32_t voice_sample(uint32_t v, int32_t amp)
{
    int32_t out, index = amp * 4 > 32767 ? 32767 : amp * 4;
    switch (voice[v].shape) {
    case BRAIDS_SAW: out = braids_saw(&voice[v].osc, voice[v].inc); break;
    case BRAIDS_SQUARE: out = braids_square(&voice[v].osc, voice[v].inc, amp * 3); break;
    case BRAIDS_FM: out = braids_fm(&voice[v].osc, voice[v].inc, voice[v].mod_inc, index); break;
    case BRAIDS_FEEDBACK_FM:
        out = braids_feedback_fm(&voice[v].osc, voice[v].inc, voice[v].mod_inc, index, voice[v].attenuation);
        break;
    default:
        voice[v].osc.phase += voice[v].inc;
        out = braids_sine(voice[v].osc.phase);
    }
    return out;
}

static void app_audio(int32_t *out, uint32_t n)
{
    uint32_t v, i;
    for (v = 0; v < NV; v++) {
        int32_t amp = voice[v].amp, g = voice[v].gate;
        if (!amp && !g)
            continue;
        for (i = 0; i < n; i++) {
            int32_t s;
            if (amp < g) { amp += 48; if (amp > g) amp = g; }        /* attack ~5 ms */
            else if (amp > g) { amp -= 6; if (amp < g) amp = g; }    /* release ~45 ms */
            s = (voice_sample(v, amp) * amp) >> 15;
            out[2u * i] += s;
            out[2u * i + 1u] += s;
        }
        voice[v].amp = amp;
    }
}

/* ---- notes (main loop) */
static uint32_t ages;
#define FM_RATIO_SHIFT 0                        /* modulator pitch above the carrier, in 1/128 semitone: 0 = same pitch */

static void play(uint32_t note, uint32_t vel, uint32_t shape)
{
    uint32_t v, pick = 0, best = 0xFFFFFFFFu;
    int32_t pitch = (int32_t)note << 7, att;
    if (note > 127u || !vel) return;
    for (v = 0; v < NV; v++) {                  /* the same note, else a free voice, else the oldest */
        uint32_t score = voice[v].note == note && voice[v].gate ? 0u
                       : voice[v].gate ? 0x80000000u + voice[v].age : (uint32_t)voice[v].amp + 1u;
        if (score < best) { best = score; pick = v; }
    }
    att = 32767 - (pitch - (72 << 7) + FM_RATIO_SHIFT) * 4;
    voice[pick].note = (uint8_t)note;
    voice[pick].age = ++ages;
    voice[pick].shape = (uint8_t)shape;
    voice[pick].inc = braids_pitch_inc(pitch);
    voice[pick].mod_inc = braids_pitch_inc(pitch + (12 << 7) + FM_RATIO_SHIFT) >> 1;   /* an octave up, halved: same pitch */
    voice[pick].attenuation = att < 0 ? 0 : att > 32767 ? 32767 : att;
    voice[pick].osc.mod_phase = 0;
    voice[pick].gate = (int32_t)(vel * 40u);    /* 127 -> 5080: six voices stay under full scale */
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

/* ---- the lanes */
#define NL 4u
static const uint32_t SCALE_MASK[] = {0xAB5u, 0x5ADu, 0x295u, 0x4A9u, 0x6ADu, 0x9ADu, 0x555u, 0xFFFu};
static const char *const SCALE_NAME[] = {"MAJOR", "MINOR", "PENT+", "PENT-", "DORIAN", "HARM.M", "WHOLE", "CHROM"};
#define NSCALE (sizeof SCALE_MASK / sizeof SCALE_MASK[0])
static const uint32_t SPEED[] = {2, 3, 4, 6, 8, 12, 16, 24};   /* clock ticks per step: 6 = sixteenth notes */
static const char *const SPEED_NAME[] = {"1/48", "1/32", "1/24", "1/16", "1/12", "1/8", "1/6", "1/4"};
#define NSPEED (sizeof SPEED / sizeof SPEED[0])

static lean_object *lane[NL];
static struct { uint8_t hits, steps, speed, scale, last; } cfg[NL] = {
    {4, 16, 3, 0, 0}, {5, 8, 5, 0, 0}, {7, 16, 3, 0, 0}, {3, 8, 4, 0, 0}};
static const uint8_t LANE_SHAPE[NL] = {BRAIDS_SAW, BRAIDS_SQUARE, BRAIDS_FM, BRAIDS_FEEDBACK_FM};
static const uint8_t LANE_LOW[NL] = {36, 48, 60, 72};
static const uint8_t LANE_SPAN[NL] = {12, 12, 24, 12};
static uint32_t bpm = 100, running = 1, tick_acc, tick_ms, selected;

static void lane_apply(uint32_t i)
{
    lane[i] = fm1_lane_reconfigure(lane[i], cfg[i].hits, cfg[i].steps, SPEED[cfg[i].speed], SCALE_MASK[cfg[i].scale]);
}

static void lanes_init(void)
{
    uint32_t i;
    for (i = 0; i < NL; i++)
        lane[i] = fm1_lane_make(cfg[i].hits, cfg[i].steps, SPEED[cfg[i].speed], SCALE_MASK[cfg[i].scale],
                                LANE_LOW[i], LANE_SPAN[i], 0x9E3779B9u * (i + 1u));
}

static void lane_report(uint32_t i, uint32_t out_ch)   /* play what the lane just started, stop what it stopped */
{
    uint32_t off = fm1_lane_off_of(lane[i]), on = fm1_lane_on_of(lane[i]);
    if (off < 128u) { stop(off); midi_send(0x80u | (out_ch + i), off, 0); }
    if (on < 128u) { play(on, 100, LANE_SHAPE[i]); midi_send(0x90u | (out_ch + i), on, 100); cfg[i].last = (uint8_t)on; }
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

static void clock_stop(uint32_t out_ch)
{
    uint32_t i;
    running = 0;
    for (i = 0; i < NL; i++) {
        lane[i] = fm1_lane_silence(lane[i]);
        lane_report(i, out_ch);
    }
}

/* ---- the screen: a row a lane (its steps as dots, what it plays), the tempo, the octave */
#define C_ACC RGB(180, 140, 255)                /* lilac */
#define C_OFF RGB(90, 90, 90)
#define C_REST RGB(50, 50, 60)
#define LANE_COLOUR(i) ((uint16_t[]){RGB(255, 120, 120), RGB(255, 190, 90), RGB(120, 220, 140), RGB(110, 170, 255)}[i])
#define ROW_Y(i) (22u + (i) * 42u)

static void note_name(char *s, uint32_t note)
{
    static const char *const NAME[12] = {"C", "C#", "D", "D#", "E", "F", "F#", "G", "G#", "A", "A#", "B"};
    const char *p = NAME[note % 12u];
    uint32_t i = 0;
    while (*p) s[i++] = *p++;
    s[i++] = (char)('0' + note / 12u - 1u);
    s[i] = 0;
}

static char *put_num(char *p, uint32_t v)
{
    if (v >= 100u) *p++ = (char)('0' + v / 100u);
    if (v >= 10u) *p++ = (char)('0' + v / 10u % 10u);
    *p++ = (char)('0' + v % 10u);
    return p;
}

static void draw_lane(uint32_t i)
{
    uint32_t k, steps = cfg[i].steps, cur = fm1_lane_step_of(lane[i]), x0 = (240u - steps * 7u) / 2u;
    uint16_t col = LANE_COLOUR(i);
    char s[40], *p = s, name[8];
    const char *a;
    cv_begin(240, 40, C_BLACK);
    for (k = 0; k < steps; k++) {
        int32_t x = (int32_t)(x0 + k * 7u);
        if (fm1_lane_hit_at_of(lane[i], k)) cv_rect(x, 2, 6, 12, k == cur ? C_WHITE : col);
        else cv_rect(x + 2, 8, 2, 2, k == cur ? C_WHITE : C_REST);
    }
    if (i == selected) cv_rect(0, 0, 2, 40, col);
    *p++ = (char)('1' + i); *p++ = ' ';
    p = put_num(p, cfg[i].hits); *p++ = '/'; p = put_num(p, cfg[i].steps); *p++ = ' ';
    for (a = SPEED_NAME[cfg[i].speed]; *a; ) *p++ = *a++;
    *p++ = ' ';
    for (a = SCALE_NAME[cfg[i].scale]; *a; ) *p++ = *a++;
    *p = 0;
    cv_text(6, 20, &FONT_S, s, i == selected ? col : C_OFF);
    if (cfg[i].last) { note_name(name, cfg[i].last); cv_text(200, 20, &FONT_S, name, col); }
    cv_blit(0, ROW_Y(i));
}

static void draw_status(int32_t oct, uint32_t ch)
{
    char s[40], *p = s;
    const char *a = running ? "PLAY  " : "STOP  ";
    while (*a) *p++ = *a++;
    p = put_num(p, bpm);
    for (a = " BPM  OCT "; *a; ) *p++ = *a++;
    *p++ = oct < 0 ? '-' : '+'; *p++ = (char)('0' + (oct < 0 ? -oct : oct));
    *p++ = ' '; *p++ = ' ';
    if (ch) { *p++ = 'C'; *p++ = 'H'; p = put_num(p, ch); } else { *p++ = 'O'; *p++ = 'M'; *p++ = 'N'; *p++ = 'I'; }
    *p = 0;
    draw_text_box(0, 4, 240, &FONT_S, s, C_ACC, 1);
}

/* ---- MIDI in: notes play the sines; from the main loop and from app_idle while the screen draws */
static struct { uint8_t oct, ch; } set = {0, 0};   /* what survives a power-off */
static uint32_t idle_ok;

static void midi_in(void)
{
    uint8_t st, d1, d2;
    while (midi_get(&st, &d1, &d2) != 0) {
        uint32_t ty = st & 0xF0u;
        if (set.ch && (st & 15u) != set.ch - 1u) continue;
        if (ty == 0x90u && d2) play(d1, d2, BRAIDS_SINE);
        else if (ty == 0x80u || ty == 0x90u) stop(d1);
    }
}
static void app_idle(void)
{
    if (idle_ok) midi_in();
}

#define KEY0 53u                                /* key 0 = F3 */

static void app_main(void)
{
    uint32_t prev = 0, k, t_change = 0, dirty = 0, status_drawn = ~0u;
    uint64_t row_drawn[NL];
    uint8_t held[27] = {0};                     /* the note each key plays */
    if (settings_load(&set, sizeof set) || (int8_t)set.oct < -2 || (int8_t)set.oct > 2 || set.ch > 16u)
        set.oct = 0, set.ch = 0;
    lanes_init();
    for (k = 0; k < NL; k++) row_drawn[k] = ~0ull;
    lcd_fill(0, 0, 240, 240, C_BLACK);

    for (;;) {
        uint32_t keys, down, up, rel, b, lit = 0, st;
        int32_t oct = (int8_t)set.oct, e;
        uint32_t base = (uint32_t)((int32_t)KEY0 + 12 * oct);
        platform_poll();
        clock_poll(0);

        keys = fm1_in.notes;                    /* bit k: key k (0 = F3 .. 26 = G5) */
        down = keys & ~prev;
        up = prev & ~keys;
        prev = keys;
        for (k = 0; k < 27u; k++) {             /* a key stops the note it started: the octave may change meanwhile */
            if (down >> k & 1u) { held[k] = (uint8_t)(base + k); play(held[k], 100, BRAIDS_SINE); midi_send(0x90u | 15u, held[k], 100); }
            if (up >> k & 1u) { stop(held[k]); midi_send(0x80u | 15u, held[k], 0); }
        }

        b = fm1_input_edges(&rel);
        if (b & (1u << BTN_OCT_DOWN) && oct > -2) { set.oct = (uint8_t)(oct - 1); dirty = 1; t_change = fm1_ms; }
        if (b & (1u << BTN_OCT_UP) && oct < 2) { set.oct = (uint8_t)(oct + 1); dirty = 1; t_change = fm1_ms; }
        if (b & (1u << BTN_PLAY)) { if (running) clock_stop(0); else running = 1; }
        if ((e = fm1_enc_take(ENC_PRESETS)) != 0) {
            int32_t c = (int32_t)set.ch + e;
            set.ch = (uint8_t)(c < 0 ? 0 : c > 16 ? 16 : c);
            dirty = 1;
            t_change = fm1_ms;
        }
        if ((e = fm1_enc_take(ENC_SELECT)) != 0) selected = (selected + NL + (uint32_t)(e % (int32_t)NL)) % NL;
        if ((e = fm1_enc_take(ENC_ALGORITHM)) != 0) {
            int32_t t = (int32_t)bpm + 2 * e;
            bpm = (uint32_t)(t < 40 ? 40 : t > 240 ? 240 : t);
        }
        {
            int32_t eh = fm1_enc_take(ENC_KNOB1), es = fm1_enc_take(ENC_KNOB2), ev = fm1_enc_take(ENC_KNOB3), ec = fm1_enc_take(ENC_KNOB4);
            if (eh | es | ev | ec) {
                int32_t h = (int32_t)cfg[selected].hits + eh, s = (int32_t)cfg[selected].steps + es;
                int32_t v = (int32_t)cfg[selected].speed + ev, c = (int32_t)cfg[selected].scale + ec;
                s = s < 1 ? 1 : s > 32 ? 32 : s;
                h = h < 0 ? 0 : h > s ? s : h;
                v = v < 0 ? 0 : v >= (int32_t)NSPEED ? (int32_t)NSPEED - 1 : v;
                c = c < 0 ? 0 : c >= (int32_t)NSCALE ? (int32_t)NSCALE - 1 : c;
                cfg[selected].hits = (uint8_t)h; cfg[selected].steps = (uint8_t)s;
                cfg[selected].speed = (uint8_t)v; cfg[selected].scale = (uint8_t)c;
                lane_apply(selected);
            }
        }

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

        idle_ok = 1;                            /* the drawing below may read MIDI meanwhile (LCD_IDLE) */
        for (k = 0; k < NL; k++) {
            uint64_t sig = (uint64_t)fm1_lane_step_of(lane[k]) | (uint64_t)cfg[k].hits << 6 | (uint64_t)cfg[k].steps << 12
                         | (uint64_t)cfg[k].speed << 18 | (uint64_t)cfg[k].scale << 22 | (uint64_t)cfg[k].last << 26
                         | (uint64_t)(k == selected) << 34;
            if (sig != row_drawn[k]) { row_drawn[k] = sig; draw_lane(k); }
        }
        if ((st = (uint32_t)(oct + 2) | (uint32_t)set.ch << 4 | bpm << 10 | running << 20) != status_drawn) {
            status_drawn = st;
            draw_status(oct, set.ch);
        }
        idle_ok = 0;

        if (dirty && quiet() && fm1_ms - t_change > 2000u) {   /* 2 s after the change, when silent (an erase stalls the sound) */
            settings_save(&set, sizeof set);
            dirty = 0;
        }
    }
}
