/* SPDX-License-Identifier: GPL-3.0-only */
/* A small Lean runtime for the FM-1 (and its browser simulator): just enough for Lean-generated C that uses
 * structures, lists and arrays of small values. Everything here is TRUSTED: the proofs say nothing about it.
 * List it in the README's trusted surface.
 *
 * What it does:    allocate and free Lean objects from one fixed pool; free an object's children when its
 *                  reference count reaches zero; grow arrays; report panics.
 * What it does not: threads, tasks, big numbers (Nat/Int above 2^31), strings beyond what the code needs,
 *                  IO, closures' external objects. Using them stops the program with a message (fm1_lean_report).
 *
 * Memory: a fixed pool (FM1_LEAN_POOL_BYTES) with size-class free lists, no compaction. When it runs out the
 * program stops with "Lean pool exhausted". Lean code must not run in the audio interrupt.
 * Build for 32-bit targets (pi32v2, wasm32): the reference-count word doubles as a list link while freeing. */
#include <lean/lean.h>

#ifndef FM1_LEAN_POOL_BYTES
#define FM1_LEAN_POOL_BYTES (64u * 1024u)
#endif
#ifndef FM1_LEAN_POOL_ATTR
#ifdef FM1_CHIP
#define FM1_LEAN_POOL_ATTR __attribute__((section(".pool")))   /* the chip's big zeroed RAM region */
#else
#define FM1_LEAN_POOL_ATTR
#endif
#endif

_Static_assert(sizeof(void *) == sizeof(int), "lean_rt.c needs a 32-bit target");

/* hook: the platform shows or logs the message. fatal != 0: the program is about to stop. */
__attribute__((weak)) void fm1_lean_report(const char *msg, int fatal) { (void)msg; (void)fatal; }

static LEAN_NORETURN void die(const char *msg)
{
    fm1_lean_report(msg, 1);
    __builtin_trap();
}

void *memmove(void *d, const void *s, size_t n)
{
    unsigned char *p = d;
    const unsigned char *q = s;
    if (p < q) while (n--) *p++ = *q++;
    else { p += n; q += n; while (n--) *--p = *--q; }
    return d;
}

/* ---- the pool: 8-byte header (size class), payload 8-aligned. Sizes up to 256 B: classes of 8 B;
 * above: powers of two up to 1 MiB. */
#define HDR 8u
#define NSMALL 33u                                 /* classes 1..32: 8..256 B */
#define NCLASS (NSMALL + 12u)                      /* 33..44: 512 B .. 1 MiB */
static uint64_t pool[FM1_LEAN_POOL_BYTES / 8u] FM1_LEAN_POOL_ATTR;
static size_t pool_used;                           /* in 8-byte words */
static void *freelist[NCLASS];

static unsigned size_class(size_t n, size_t *bytes)
{
    unsigned c;
    if (n <= 256u) { c = (unsigned)((n + 7u) / 8u); if (!c) c = 1u; *bytes = (size_t)c * 8u; return c; }
    for (c = NSMALL, *bytes = 512u; *bytes < n; c++, *bytes <<= 1) if (c >= NCLASS - 1u) die("Lean object too large");
    return c;
}

static void *heap_alloc(size_t n)
{
    size_t bytes, words;
    unsigned c = size_class(n, &bytes);
    uint32_t *h;
    if (freelist[c]) { void **p = freelist[c]; freelist[c] = *p; return p; }
    words = 1u + bytes / 8u;
    if (pool_used + words > sizeof pool / 8u) die("Lean pool exhausted");
    h = (uint32_t *)&pool[pool_used];
    pool_used += words;
    h[0] = c;
    return h + 2;
}

static void heap_free(void *p)
{
    unsigned c = ((uint32_t *)p)[-2];
    *(void **)p = freelist[c];
    freelist[c] = p;
}

/* Bytes of pool in use at the high-water mark (for the simulator's status line). */
size_t fm1_lean_pool_used(void) { return pool_used * 8u; }

lean_object *lean_alloc_small_object_core(unsigned sz)
{
    lean_object *o = heap_alloc(sz);
    o->m_cs_sz = sz;
    return o;
}
lean_object *lean_alloc_object(size_t sz) { return heap_alloc(sz); }
void lean_free_object(lean_object *o) { heap_free(o); }
void *mi_malloc(size_t n) { return heap_alloc(n); }
void mi_free(void *p) { heap_free(p); }

/* ---- freeing: when the count reaches zero, free the object and drop one reference on each child.
 * The to-do list is threaded through the (dead) reference-count words, so deep lists cannot overflow the stack. */
static lean_object *todo;

static void drop(lean_object *c)
{
    if (!c || lean_is_scalar(c)) return;
    if (c->m_rc > 1) c->m_rc--;
    else if (c->m_rc == 1) { c->m_rc = (int)(uintptr_t)todo; todo = c; }
    else if (c->m_rc < 0) die("Lean: object shared between threads");
    /* m_rc == 0: a persistent object, never freed */
}

static void free_children(lean_object *o)
{
    unsigned i, n;
    switch (lean_ptr_tag(o)) {
    case LeanClosure: {
        lean_closure_object *c = (lean_closure_object *)o;
        for (i = 0, n = c->m_num_fixed; i < n; i++) drop(c->m_objs[i]);
        break;
    }
    case LeanArray: {
        lean_array_object *a = (lean_array_object *)o;
        for (i = 0, n = (unsigned)a->m_size; i < n; i++) drop(a->m_data[i]);
        break;
    }
    case LeanScalarArray: case LeanString: break;
    case LeanThunk: {
        lean_thunk_object *t = (lean_thunk_object *)o;
        drop(t->m_value); drop(t->m_closure);
        break;
    }
    case LeanRef: drop(((lean_ref_object *)o)->m_value); break;
    case LeanMPZ: case LeanTask: case LeanExternal: case LeanStructArray: case LeanReserved:
        die("Lean: unsupported object kind"); break;
    default: {                                     /* constructor */
        lean_ctor_object *c = (lean_ctor_object *)o;
        for (i = 0, n = lean_ctor_num_objs(o); i < n; i++) drop(c->m_objs[i]);
    }
    }
}

void lean_dec_ref_cold(lean_object *o)
{
    if (o->m_rc != 1) die("Lean: bad reference count");
    o->m_rc = 0;
    todo = 0;                                      /* (only ever empty here: this is not re-entered) */
    o->m_rc = (int)(uintptr_t)todo; todo = o;
    while (todo) {
        lean_object *cur = todo;
        todo = (lean_object *)(uintptr_t)cur->m_rc;
        free_children(cur);
        heap_free(cur);
    }
}

/* ---- arrays */
lean_object *lean_copy_expand_array(lean_object *a, bool expand)
{
    size_t sz = lean_array_size(a), cap = lean_array_capacity(a), i;
    lean_object *r;
    if (expand) cap = (cap + 1u) * 2u;
    r = lean_alloc_array(sz, cap);
    for (i = 0; i < sz; i++) {
        lean_object *x = lean_array_get_core(a, i);
        lean_inc(x);
        lean_array_set_core(r, i, x);
    }
    lean_dec(a);
    return r;
}

lean_object *lean_array_push(lean_object *a, lean_object *v)
{
    lean_object *r = lean_is_exclusive(a) && lean_array_capacity(a) > lean_array_size(a) ? a : lean_copy_expand_array(a, lean_array_capacity(a) < lean_array_size(a) + 1u);
    size_t sz = lean_array_size(r);
    ((lean_array_object *)r)->m_size = sz + 1u;     /* first: set_core checks the index against the size */
    lean_array_set_core(r, sz, v);
    return r;
}

/* ---- panics and unsupported operations */
void lean_notify_assert(const char *file, int line, const char *cond) { (void)file; (void)line; die(cond); }
void lean_internal_panic(const char *msg) { die(msg); }
void lean_internal_panic_out_of_memory(void) { die("Lean: out of memory"); }
void lean_internal_panic_unreachable(void) { die("Lean: unreachable code"); }
void lean_internal_panic_rc_overflow(void) { die("Lean: reference count overflow"); }
void lean_internal_panic_overflow(void) { die("Lean: size overflow"); }

lean_object *lean_panic_fn(lean_object *def, lean_object *msg)
{
    if (!lean_is_scalar(msg) && lean_ptr_tag(msg) == LeanString) fm1_lean_report(lean_string_cstr(msg), 0);
    lean_dec(msg);
    return def;
}
lean_object *lean_panic_fn_borrowed(lean_object *def, lean_object *msg) { return lean_panic_fn(def, msg); }
void lean_panic(const char *msg, bool force_stderr) { (void)force_stderr; fm1_lean_report(msg, 0); }

lean_object *lean_array_get_panic(lean_object *def) { fm1_lean_report("Lean: array index out of bounds", 0); return def; }
lean_object *lean_array_set_panic(lean_object *a, lean_object *v) { lean_dec(v); fm1_lean_report("Lean: array index out of bounds", 0); return a; }

/* Numbers above 2^31 need big integers, which this runtime does not have: stop with a message instead.
 * (Nat/Int values below 2^31 are plain integers and never get here. A UInt32 above 2^31 converted with
 * `toNat` does.) One macro per signature shape in lean.h. */
#define NOBIG "Lean: number too big (over 2^31)"
#define O1(n) lean_object *n(lean_object *a) { (void)a; die(NOBIG); }
#define O2(n) lean_object *n(lean_object *a, lean_object *b) { (void)a; (void)b; die(NOBIG); }
#define B2(n) bool n(lean_object *a, lean_object *b) { (void)a; (void)b; die(NOBIG); }
O1(lean_nat_big_succ) O2(lean_nat_big_add) O2(lean_nat_big_sub) O2(lean_nat_big_mul) O2(lean_nat_big_div)
O2(lean_nat_big_div_exact) O2(lean_nat_big_mod) O2(lean_nat_big_land) O2(lean_nat_big_lor) O2(lean_nat_big_xor)
B2(lean_nat_big_eq) B2(lean_nat_big_le) B2(lean_nat_big_lt)
lean_object *lean_nat_overflow_mul(size_t a, size_t b) { (void)a; (void)b; die(NOBIG); }
lean_obj_res lean_nat_big_shiftr(b_lean_obj_arg a, b_lean_obj_arg b) { (void)a; (void)b; die(NOBIG); }
lean_obj_res lean_big_usize_to_nat(size_t n) { (void)n; die(NOBIG); }
lean_obj_res lean_big_uint64_to_nat(uint64_t n) { (void)n; die(NOBIG); }
O1(lean_int_big_neg) O2(lean_int_big_add) O2(lean_int_big_sub) O2(lean_int_big_mul) O2(lean_int_big_div)
O2(lean_int_big_div_exact) O2(lean_int_big_mod) O2(lean_int_big_ediv) O2(lean_int_big_emod)
B2(lean_int_big_eq) B2(lean_int_big_le) B2(lean_int_big_lt)
bool lean_int_big_nonneg(lean_object *a) { (void)a; die(NOBIG); }
lean_object *lean_big_int_to_int(int n) { (void)n; die(NOBIG); }
lean_object *lean_big_size_t_to_int(size_t n) { (void)n; die(NOBIG); }
lean_object *lean_big_int64_to_int(int64_t n) { (void)n; die(NOBIG); }
lean_obj_res lean_big_int_to_nat(lean_obj_arg a) { (void)a; die(NOBIG); }
uint8_t lean_uint8_of_big_nat(b_lean_obj_arg a) { (void)a; die(NOBIG); }
uint16_t lean_uint16_of_big_nat(b_lean_obj_arg a) { (void)a; die(NOBIG); }
uint32_t lean_uint32_of_big_nat(b_lean_obj_arg a) { (void)a; die(NOBIG); }
uint64_t lean_uint64_of_big_nat(b_lean_obj_arg a) { (void)a; die(NOBIG); }
size_t lean_usize_of_big_nat(b_lean_obj_arg a) { (void)a; die(NOBIG); }
int8_t lean_int8_of_big_int(b_lean_obj_arg a) { (void)a; die(NOBIG); }
int16_t lean_int16_of_big_int(b_lean_obj_arg a) { (void)a; die(NOBIG); }
int32_t lean_int32_of_big_int(b_lean_obj_arg a) { (void)a; die(NOBIG); }
int64_t lean_int64_of_big_int(b_lean_obj_arg a) { (void)a; die(NOBIG); }
ptrdiff_t lean_isize_of_big_int(b_lean_obj_arg a) { (void)a; die(NOBIG); }

/* Shifts and powers of small numbers; anything that would not fit a small number stops the firmware. */
lean_obj_res lean_nat_shiftl(b_lean_obj_arg a, b_lean_obj_arg b)
{
    size_t x, n;
    if (!lean_is_scalar(a) || !lean_is_scalar(b)) die(NOBIG);
    x = lean_unbox(a); n = lean_unbox(b);
    if (n >= 31 || (x >> (31 - n)) != 0) die(NOBIG);
    return lean_box(x << n);
}

lean_obj_res lean_nat_pow(b_lean_obj_arg a, b_lean_obj_arg b)
{
    size_t x, n, r = 1;
    if (!lean_is_scalar(a) || !lean_is_scalar(b)) die(NOBIG);
    x = lean_unbox(a); n = lean_unbox(b);
    while (n--) { if (x && r > LEAN_MAX_SMALL_NAT / x) die(NOBIG); r *= x; }
    return lean_box(r);
}

/* On the chip there are no atomic instructions; objects are never shared between threads, so the
 * atomic paths in lean.h are never taken. These satisfy the linker. */
#ifdef FM1_CHIP
/* (asm labels: the compiler treats the __sync_* names as builtins and refuses a definition) */
int sync_sub4(volatile int *p, int v) __asm__("__sync_fetch_and_sub_4");
int sync_add4(volatile int *p, int v) __asm__("__sync_fetch_and_add_4");
int sync_cas4(volatile int *p, int e, int d) __asm__("__sync_val_compare_and_swap_4");
int sync_sub4(volatile int *p, int v) { int o = *p; *p = o - v; return o; }
int sync_add4(volatile int *p, int v) { int o = *p; *p = o + v; return o; }
int sync_cas4(volatile int *p, int e, int d) { int o = *p; if (o == e) *p = d; return o; }
#endif
