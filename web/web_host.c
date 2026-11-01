/* SPDX-License-Identifier: GPL-3.0-only */
/* The FM-1 in a web browser. Derived from fw/tests/host.c (Leo Kuroshita / Hügelton Instruments, GPL-3.0):
 * platform.c includes this file instead of the hardware when DINGHY_WEB is set, so the app
 * (fw/firmware/src/dinghy.c) runs unchanged, compiled to WebAssembly.
 *
 * The wasm instance runs in a Web Worker. app_main() never returns, so time is driven from inside:
 * every platform_poll() is one millisecond and calls the JS import js_sync(), which applies the player's
 * input and may block until the audio buffer wants more. Audio, not the wall clock, sets the pace.
 *
 *   JS -> C:  web_in (input struct, written by JS before each ms; address from web_in_ptr())
 *   C  -> JS: js_audio(ptr, frames)  one 256-frame block of 16-bit stereo
 *             js_frame(fb, leds_lo, leds_hi)  the screen, 240x240 RGB565, plus the LEDs
 * FM-1 only (no SMK-37). */
#include <stdint.h>
#include "fm1_lean.h"

#define WEB_IMPORT(n) __attribute__((import_module("env"), import_name(#n)))
WEB_IMPORT(js_sync) void js_sync(uint32_t ms);
WEB_IMPORT(js_audio) void js_audio(const int16_t *pcm, uint32_t frames);
WEB_IMPORT(js_frame) void js_frame(const uint16_t *fb, uint32_t leds_lo, uint32_t leds_hi);
WEB_IMPORT(js_report) void js_report(const char *msg, int fatal);   /* a message from the Lean runtime (NUL-terminated) */
void fm1_lean_report(const char *msg, int fatal) { js_report(msg, fatal); }   /* rt/lean_rt.c's hook */

#ifndef APP_NAME
#define APP_NAME "DINGHY"
#endif
#ifndef APP_VER
#define APP_VER "web"
#endif
#define FS 44100u
#define HALF_FRAMES 256u
#define HOST_NENC 7

/* what the page tells the firmware; JS fills it in js_sync, C consumes it in platform_poll */
struct web_input {
    uint32_t notes;                     /* keys held, bit k = key k (0 = F3) */
    uint32_t buttons;                   /* buttons held */
    uint32_t press, release;            /* button edges since the last ms (bit = button id) */
    int32_t enc[HOST_NENC];             /* detents turned since the last ms, + = clockwise */
    uint32_t midi_n;                    /* MIDI messages queued below (0..16), consumed each ms */
    uint8_t midi[16][4];                /* status, data 1, data 2, source (1 USB, 2 TRS) */
    uint32_t patch;                     /* a patch to load, index plus one (0: none); the page's demo list */
};
static uint32_t web_patch_request;      /* the same, for the app to take (dinghy.c's main loop) */
static struct web_input web_in;
__attribute__((export_name("web_in_ptr"))) struct web_input *web_in_ptr(void) { return &web_in; }

static volatile uint32_t fm1_ms;
static struct { uint32_t notes, buttons; } fm1_in;
static uint32_t host_edges, host_rel, host_rel_next;
static uint32_t fm1_input_edges(uint32_t *released)
{
    uint32_t b = host_edges;
    host_edges = 0;
    *released = host_rel;
    host_rel = host_rel_next;
    host_rel_next = 0;
    return b;
}
static uint32_t fm1_input_note_edges(void) { return 0; }
static int32_t host_enc[HOST_NENC];
static int32_t fm1_enc_take(uint32_t e) { int32_t v = host_enc[e % HOST_NENC]; host_enc[e % HOST_NENC] = 0; return v; }
static uint64_t host_leds;                      /* bit id: LED id lit (0..13 buttons, 14..40 keys) */
static void fm1_irq_off(void) {}
static void fm1_irq_on(void) {}
static void fm1_led_key(uint32_t id, int on) { if (on) host_leds |= (uint64_t)1 << id; else host_leds &= ~((uint64_t)1 << id); }
static void fm1_led_key_glow(uint32_t id, int on) { (void)id; (void)on; }

static uint16_t fb[240 * 240];
static void lcd_sync(void) {}
static void lcd_fill(uint32_t x, uint32_t y, uint32_t w, uint32_t h, uint16_t c)
{
    uint32_t i, j;
    for (j = y; j < y + h && j < 240u; j++)
        for (i = x; i < x + w && i < 240u; i++)
            fb[j * 240u + i] = c;
}
static void lcd_blit(uint32_t x, uint32_t y, uint32_t w, uint32_t h, const uint16_t *px)
{
    uint32_t i, j;
    for (j = 0; j < h; j++)
        for (i = 0; i < w; i++)
            if (x + i < 240u && y + j < 240u) {
                uint16_t c = px[j * w + i];
                fb[(y + j) * 240u + x + i] = (uint16_t)(c >> 8 | c << 8);
            }
}
#ifndef CV_MAX
#define CV_MAX (240u * 64u)
#endif
#include "gfx.c"

/* the compiler's implicit memset/memcpy/memcmp (there is no libc in the wasm) */
#include "libc.c"

/* storage in RAM: lost when the page closes */
#include "store.h"
static uint8_t host_set[SECTOR_MAX + 4], host_blob[NBLOB][SECTOR_MAX + 4], host_slot[NSLOT][SLOT_MAX + 4];
static int host_load(uint8_t *a, uint32_t max, void *p, uint32_t n)
{
    if (!a[0] || n > max || (uint32_t)(a[1] | a[2] << 8 | a[3] << 16) != n) return -1;
    memcpy(p, a + 4, n);
    return 0;
}
static int host_save(uint8_t *a, uint32_t max, const void *p, uint32_t n)
{
    if (n > max) return -1;
    a[0] = 1; a[1] = (uint8_t)n; a[2] = (uint8_t)(n >> 8); a[3] = (uint8_t)(n >> 16);
    memcpy(a + 4, p, n);
    return 0;
}
static int settings_load(void *p, uint32_t n) { return host_load(host_set, SECTOR_MAX, p, n); }
static int settings_save(const void *p, uint32_t n) { return host_save(host_set, SECTOR_MAX, p, n); }
static int blob_load(uint32_t i, void *p, uint32_t n) { return i < NBLOB ? host_load(host_blob[i], SECTOR_MAX, p, n) : -1; }
static int blob_save(uint32_t i, const void *p, uint32_t n) { return i < NBLOB ? host_save(host_blob[i], SECTOR_MAX, p, n) : -1; }
static int slot_load(uint32_t i, void *p, uint32_t n) { return i < NSLOT ? host_load(host_slot[i], SLOT_MAX, p, n) : -1; }
static int slot_save(uint32_t i, const void *p, uint32_t n) { return i < NSLOT ? host_save(host_slot[i], SLOT_MAX, p, n) : -1; }

static uint8_t mq[64][4];
static uint32_t mq_w, mq_r;
static int midi_get(uint8_t *st, uint8_t *d1, uint8_t *d2)
{
    int src;
    if (mq_r == mq_w) return 0;
    *st = mq[mq_r % 64u][0]; *d1 = mq[mq_r % 64u][1]; *d2 = mq[mq_r % 64u][2]; src = mq[mq_r % 64u][3] ? mq[mq_r % 64u][3] : 1;
    mq_r++;
    return src;
}
static void midi_send(uint32_t st, uint32_t d1, uint32_t d2) { (void)st; (void)d1; (void)d2; }   /* no MIDI out in the page yet */

static void app_audio(int32_t *out, uint32_t n);
static void app_main(void);

static void platform_poll(void)                 /* one call = one millisecond */
{
    static uint32_t owed, since_frame;
    static int32_t blk[2u * HALF_FRAMES];
    static int16_t pcm[2u * HALF_FRAMES];
    uint32_t i, p, r;

    fm1_ms++;
    js_sync(fm1_ms);                            /* the page's input lands in web_in (and we may wait here for audio) */
    fm1_in.notes = web_in.notes;
    p = web_in.press; r = web_in.release;
    web_in.press = web_in.release = 0;
    host_edges |= p; host_rel |= r;
    fm1_in.buttons = web_in.buttons;
    for (i = 0; i < HOST_NENC; i++) { host_enc[i] += web_in.enc[i]; web_in.enc[i] = 0; }
    for (i = 0; i < web_in.midi_n && i < 16u; i++) {
        mq[mq_w % 64u][0] = web_in.midi[i][0]; mq[mq_w % 64u][1] = web_in.midi[i][1];
        mq[mq_w % 64u][2] = web_in.midi[i][2]; mq[mq_w % 64u][3] = web_in.midi[i][3];
        mq_w++;
    }
    web_in.midi_n = 0;
    if (web_in.patch) { web_patch_request = web_in.patch; web_in.patch = 0; }

    owed += FS;                                 /* the frames this millisecond is worth, in blocks as the ISR renders */
    while (owed >= 1000u * HALF_FRAMES) {
        owed -= 1000u * HALF_FRAMES;
        memset(blk, 0, sizeof blk);
        app_audio(blk, HALF_FRAMES);
        for (i = 0; i < 2u * HALF_FRAMES; i++) {
            int32_t v = blk[i];
            pcm[i] = (int16_t)(v > 32767 ? 32767 : v < -32767 ? -32767 : v);
        }
        js_audio(pcm, HALF_FRAMES);
    }
    if (++since_frame >= 16u) {                 /* the screen, about 60 times a second */
        since_frame = 0;
        js_frame(fb, (uint32_t)host_leds, (uint32_t)(host_leds >> 32));
    }
}

__attribute__((export_name("web_run"))) void web_run(void) { app_main(); }
size_t fm1_lean_pool_used(void);
__attribute__((export_name("web_lean_pool_used"))) uint32_t web_lean_pool_used(void) { return (uint32_t)fm1_lean_pool_used(); }
/* the Lean scale table, for tools/smoke_web.mjs: an uninitialised table reads as chromatic and nothing else notices */
__attribute__((export_name("web_harmony_mask"))) uint32_t web_harmony_mask(uint32_t scale, uint32_t key, uint32_t root, uint32_t follow)
{
    return fm1_harmony_mask(scale, key, root, follow);
}
