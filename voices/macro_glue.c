/* SPDX-License-Identifier: GPL-3.0-only */
#include <lean/lean.h>
#include <stddef.h>
#include <stdint.h>

#undef LEAN_EXPORT
#define LEAN_EXPORT static inline
#include "MacroApi.c"
