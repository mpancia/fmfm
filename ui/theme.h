/* SPDX-License-Identifier: GPL-3.0-only */
/* The looks of the instrument. Each is a background, three greys of text, an accent, four lane colours, and the
 * colours of Alfred's suit. Alfred's skin, shirt and hair are the same in every look. Needs RGB() from gfx.c. */
#pragma once
#include <stdint.h>

typedef struct {
    const char *name;
    uint16_t bg, hi, mid, dim, acc;             /* background; bright text; labels; inactive; accent */
    uint16_t lane[4];
    uint16_t suit, suit_light, outline;         /* Alfred */
} theme_t;

static const theme_t THEMES[] = {
    {"BLACK TIE", RGB(11, 11, 14), RGB(242, 234, 216), RGB(154, 147, 127), RGB(58, 55, 47), RGB(217, 164, 65),
     {RGB(217, 164, 65), RGB(196, 85, 61), RGB(127, 168, 138), RGB(122, 148, 184)},
     RGB(44, 44, 58), RGB(86, 86, 108), RGB(4, 4, 6)},
    {"WEDGWOOD", RGB(13, 26, 43), RGB(238, 242, 247), RGB(138, 160, 186), RGB(45, 64, 96), RGB(127, 178, 229),
     {RGB(127, 178, 229), RGB(232, 217, 168), RGB(224, 138, 122), RGB(165, 214, 167)},
     RGB(28, 48, 82), RGB(70, 104, 150), RGB(5, 10, 20)},
    {"BAIZE", RGB(10, 31, 20), RGB(240, 234, 214), RGB(143, 174, 143), RGB(35, 68, 51), RGB(224, 184, 78),
     {RGB(224, 184, 78), RGB(217, 105, 95), RGB(140, 201, 160), RGB(201, 160, 220)},
     RGB(22, 54, 38), RGB(60, 104, 80), RGB(3, 12, 7)},
    {"EARL GREY", RGB(23, 17, 12), RGB(245, 222, 179), RGB(168, 138, 98), RGB(74, 56, 38), RGB(224, 138, 46),
     {RGB(224, 138, 46), RGB(196, 77, 53), RGB(138, 160, 92), RGB(111, 154, 168)},
     RGB(58, 42, 30), RGB(110, 84, 58), RGB(10, 6, 3)},
    {"SILVER SERVICE", RGB(16, 20, 23), RGB(232, 238, 242), RGB(139, 155, 165), RGB(47, 59, 66), RGB(127, 224, 196),
     {RGB(127, 224, 196), RGB(240, 198, 116), RGB(229, 127, 154), RGB(130, 170, 255)},
     RGB(38, 50, 58), RGB(88, 108, 120), RGB(6, 8, 10)},
    {"SUNDAY BEST", RGB(26, 15, 28), RGB(247, 232, 238), RGB(168, 138, 160), RGB(67, 40, 74), RGB(255, 143, 177),
     {RGB(255, 143, 177), RGB(255, 198, 109), RGB(155, 227, 184), RGB(160, 168, 255)},
     RGB(52, 30, 62), RGB(104, 70, 122), RGB(10, 5, 12)},
    {"CATALOGUE", RGB(246, 248, 247), RGB(0, 0, 0), RGB(111, 111, 111), RGB(229, 229, 229), RGB(255, 143, 177),
     {RGB(224, 77, 120), RGB(15, 14, 18), RGB(111, 111, 111), RGB(160, 160, 168)},
     RGB(15, 14, 18), RGB(58, 53, 66), RGB(0, 0, 0)},
};
#define NTHEMES (sizeof THEMES / sizeof THEMES[0])
