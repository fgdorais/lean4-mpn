/*
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
*/

/*
GMP's own kernels, the `mpn` column of the benches: the `mpn_*` functions of the GMP that Lean
links into every executable for `Nat`, called on the limbs of `UInt64Array`s. The library does not
use them; only the bench executables link this file.

Each function takes its operands borrowed and returns an O(1) check of its result, like the
checks of the benches, as a `UInt32`, which Lean boxes without allocating, where a `UInt64` would
cost an allocation per call in the polymorphic timing loop. Results go into scratch buffers that
persist between calls, so that the time is the kernel's alone, without the allocation of a result;
the operands that a kernel destroys (`mpn_gcd`, `mpn_get_str`) are copied first, which GMP's own
`mpz` functions also do.

The prototypes are those of GMP 6 (`gmp.h` maps `mpn_x` to `__gmpn_x`), declared here so that the
benches need no header. Limbs are 64 bits, as on the platforms Lean supports.
*/

#include <lean/lean.h>
#include <stdint.h>

/* The C library, declared: the toolchain's compiler, which Lake uses, comes without its headers. */
void *malloc(size_t);
void free(void *);
void abort(void);
void *memcpy(void *, const void *, size_t);
void *memset(void *, int, size_t);

typedef uint64_t mp_limb_t;
typedef long mp_size_t;

mp_limb_t __gmpn_add(mp_limb_t *, const mp_limb_t *, mp_size_t, const mp_limb_t *, mp_size_t);
mp_limb_t __gmpn_sub(mp_limb_t *, const mp_limb_t *, mp_size_t, const mp_limb_t *, mp_size_t);
mp_limb_t __gmpn_lshift(mp_limb_t *, const mp_limb_t *, mp_size_t, unsigned int);
mp_limb_t __gmpn_rshift(mp_limb_t *, const mp_limb_t *, mp_size_t, unsigned int);
mp_limb_t __gmpn_mul_1(mp_limb_t *, const mp_limb_t *, mp_size_t, mp_limb_t);
mp_limb_t __gmpn_addmul_1(mp_limb_t *, const mp_limb_t *, mp_size_t, mp_limb_t);
mp_limb_t __gmpn_mul(mp_limb_t *, const mp_limb_t *, mp_size_t, const mp_limb_t *, mp_size_t);
void __gmpn_sqr(mp_limb_t *, const mp_limb_t *, mp_size_t);
mp_limb_t __gmpn_divrem_1(mp_limb_t *, mp_size_t, const mp_limb_t *, mp_size_t, mp_limb_t);
mp_limb_t __gmpn_mod_1(const mp_limb_t *, mp_size_t, mp_limb_t);
void __gmpn_tdiv_qr(mp_limb_t *, mp_limb_t *, mp_size_t, const mp_limb_t *, mp_size_t,
  const mp_limb_t *, mp_size_t);
mp_size_t __gmpn_sqrtrem(mp_limb_t *, mp_limb_t *, const mp_limb_t *, mp_size_t);
mp_size_t __gmpn_gcd(mp_limb_t *, mp_limb_t *, mp_size_t, mp_limb_t *, mp_size_t);
size_t __gmpn_get_str(unsigned char *, int, mp_limb_t *, mp_size_t);
mp_size_t __gmpn_set_str(mp_limb_t *, const unsigned char *, size_t, int);
void __gmpn_and_n(mp_limb_t *, const mp_limb_t *, const mp_limb_t *, mp_size_t);
void __gmpn_ior_n(mp_limb_t *, const mp_limb_t *, const mp_limb_t *, mp_size_t);
void __gmpn_xor_n(mp_limb_t *, const mp_limb_t *, const mp_limb_t *, mp_size_t);
int __gmpn_cmp(const mp_limb_t *, const mp_limb_t *, mp_size_t);

/* Scratch buffers of at least `n` limbs, kept between calls; the benches run on one thread. */
static mp_limb_t *bufs[4];
static size_t caps[4];

static mp_limb_t *scratch(int i, size_t n) {
  if (n == 0) n = 1;
  if (caps[i] < n) {
    free(bufs[i]);
    bufs[i] = (mp_limb_t *)malloc(n * sizeof(mp_limb_t));
    if (bufs[i] == NULL) abort();
    caps[i] = n;
  }
  return bufs[i];
}

static unsigned char *chars;
static size_t charCap;

static unsigned char *scratchChars(size_t n) {
  if (charCap < n) {
    free(chars);
    chars = (unsigned char *)malloc(n);
    if (chars == NULL) abort();
    charCap = n;
  }
  return chars;
}

static inline const mp_limb_t *limbs(b_lean_obj_arg a) {
  return (const mp_limb_t *)lean_sarray_cptr(a);
}

static inline mp_size_t size(b_lean_obj_arg a) { return (mp_size_t)lean_sarray_size(a); }

/* `a + b`, for `a` at least as long as `b`. */
uint32_t mpnb_add(b_lean_obj_arg a, b_lean_obj_arg b) {
  mp_size_t n = size(a);
  mp_limb_t *r = scratch(0, n + 1);
  r[n] = __gmpn_add(r, limbs(a), n, limbs(b), size(b));
  return (uint32_t)(r[0] + r[n]);
}

/* `a - b`, for `a ≥ b`. */
uint32_t mpnb_sub(b_lean_obj_arg a, b_lean_obj_arg b) {
  mp_size_t n = size(a);
  mp_limb_t *r = scratch(0, n);
  mp_limb_t c = __gmpn_sub(r, limbs(a), n, limbs(b), size(b));
  return (uint32_t)(r[0] + c);
}

/* `a 2ˢ` and `⌊a / 2ˢ⌋`, for `0 < s < 64`. */
uint32_t mpnb_lshift(b_lean_obj_arg a, uint32_t s) {
  mp_size_t n = size(a);
  mp_limb_t *r = scratch(0, n + 1);
  r[n] = __gmpn_lshift(r, limbs(a), n, s);
  return (uint32_t)(r[0] + r[n]);
}

uint32_t mpnb_rshift(b_lean_obj_arg a, uint32_t s) {
  mp_size_t n = size(a);
  mp_limb_t *r = scratch(0, n);
  mp_limb_t c = __gmpn_rshift(r, limbs(a), n, s);
  return (uint32_t)(r[0] + c);
}

/* `a v`, and `r + a v` into a buffer that keeps its limbs between calls. */
uint32_t mpnb_mul_1(b_lean_obj_arg a, uint64_t v) {
  mp_size_t n = size(a);
  mp_limb_t *r = scratch(0, n);
  mp_limb_t c = __gmpn_mul_1(r, limbs(a), n, v);
  return (uint32_t)(r[0] + c);
}

uint32_t mpnb_addmul_1(b_lean_obj_arg a, uint64_t v) {
  mp_size_t n = size(a);
  mp_limb_t *r = scratch(1, n);
  mp_limb_t c = __gmpn_addmul_1(r, limbs(a), n, v);
  return (uint32_t)(r[0] + c);
}

/* `a b`, for `a` at least as long as `b`: GMP's choice of algorithm for the sizes. */
uint32_t mpnb_mul(b_lean_obj_arg a, b_lean_obj_arg b) {
  mp_size_t m = size(a), n = size(b);
  mp_limb_t *r = scratch(0, m + n);
  __gmpn_mul(r, limbs(a), m, limbs(b), n);
  return (uint32_t)(r[0] + r[m + n - 1]);
}

uint32_t mpnb_sqr(b_lean_obj_arg a) {
  mp_size_t n = size(a);
  mp_limb_t *r = scratch(0, 2 * n);
  __gmpn_sqr(r, limbs(a), n);
  return (uint32_t)(r[0] + r[2 * n - 1]);
}

/* `a / d` and `a % d` for a word `d`, and `a % d` alone. */
uint32_t mpnb_divrem_1(b_lean_obj_arg a, uint64_t d) {
  mp_size_t n = size(a);
  mp_limb_t *q = scratch(0, n);
  mp_limb_t r = __gmpn_divrem_1(q, 0, limbs(a), n, d);
  return (uint32_t)(q[0] + r);
}

uint32_t mpnb_mod_1(b_lean_obj_arg a, uint64_t d) {
  return (uint32_t)__gmpn_mod_1(limbs(a), size(a), d);
}

/* `a / b` and `a % b`, for `a` at least as long as `b` and a nonzero top limb of `b`. */
uint32_t mpnb_tdiv_qr(b_lean_obj_arg a, b_lean_obj_arg b) {
  mp_size_t m = size(a), n = size(b);
  mp_limb_t *q = scratch(0, m - n + 1);
  mp_limb_t *r = scratch(1, n);
  __gmpn_tdiv_qr(q, r, 0, limbs(a), m, limbs(b), n);
  return (uint32_t)(q[0] + r[0]);
}

/* `⌊√a⌋` and `a - ⌊√a⌋²`, or the root alone, for a nonzero top limb of `a`. */
uint32_t mpnb_sqrtrem(b_lean_obj_arg a, uint8_t rem) {
  mp_size_t n = size(a);
  mp_limb_t *s = scratch(0, (n + 1) / 2);
  mp_limb_t *r = rem ? scratch(1, n) : NULL;
  mp_size_t rn = __gmpn_sqrtrem(s, r, limbs(a), n);
  return (uint32_t)(s[0] + (uint64_t)rn);
}

/* The limbs of `a` from its lowest nonzero limb, shifted right by its trailing zero bits, into
   `x`, trimmed; returns the size and sets `*tz` to the number of trailing zero bits. */
static mp_size_t oddPart(mp_limb_t *x, const mp_limb_t *a, mp_size_t n, uint64_t *tz) {
  mp_size_t z = 0;
  while (z < n && a[z] == 0) z++;
  unsigned int s = (unsigned int)__builtin_ctzll(a[z]);
  *tz = 64 * (uint64_t)z + s;
  mp_size_t k = n - z;
  if (s == 0) memcpy(x, a + z, k * sizeof(mp_limb_t));
  else __gmpn_rshift(x, a + z, k, s);
  while (k > 1 && x[k - 1] == 0) k--;
  return k;
}

/* `gcd a b` for nonzero `a`, `b`, as `mpz_gcd` does: the common factors of two removed, which
   `mpn_gcd` requires, and put back. */
uint32_t mpnb_gcd(b_lean_obj_arg a, b_lean_obj_arg b) {
  mp_size_t an = size(a), bn = size(b);
  mp_limb_t *x = scratch(0, an), *y = scratch(1, bn);
  uint64_t ta, tb;
  mp_size_t xn = oddPart(x, limbs(a), an, &ta);
  mp_size_t yn = oddPart(y, limbs(b), bn, &tb);
  if (xn < yn || (xn == yn && __gmpn_cmp(x, y, xn) < 0)) {
    mp_limb_t *t = x; x = y; y = t;
    mp_size_t tn = xn; xn = yn; yn = tn;
  }
  mp_limb_t *g = scratch(2, yn + 1);
  mp_size_t gn = __gmpn_gcd(g, x, xn, y, yn);
  uint64_t t = ta < tb ? ta : tb;
  mp_size_t z = (mp_size_t)(t / 64);
  mp_limb_t *h = scratch(3, gn + z + 1);
  memset(h, 0, z * sizeof(mp_limb_t));
  if (t % 64 == 0) {
    memcpy(h + z, g, gn * sizeof(mp_limb_t));
    h[gn + z] = 0;
  } else {
    h[gn + z] = __gmpn_lshift(h + z, g, gn, (unsigned int)(t % 64));
  }
  return (uint32_t)(h[z] + (uint64_t)gn);
}

/* The decimal digits of `a`, as characters, for a nonzero top limb: `mpn_get_str` destroys its
   operand, so on a copy. */
uint32_t mpnb_get_str(b_lean_obj_arg a) {
  mp_size_t n = size(a);
  mp_limb_t *x = scratch(0, n + 1);
  memcpy(x, limbs(a), n * sizeof(mp_limb_t));
  unsigned char *s = scratchChars(20 * (size_t)n + 2);
  size_t len = __gmpn_get_str(s, 10, x, n);
  for (size_t i = 0; i < len; i++) s[i] += '0';
  return (uint32_t)((uint64_t)len + s[0]);
}

/* The limbs of a string of decimal digits, without a leading zero. */
uint32_t mpnb_set_str(b_lean_obj_arg str) {
  size_t len = lean_string_size(str) - 1;
  const char *c = lean_string_cstr(str);
  unsigned char *d = scratchChars(len + 1);
  for (size_t i = 0; i < len; i++) d[i] = (unsigned char)(c[i] - '0');
  mp_limb_t *r = scratch(0, len / 19 + 2);
  mp_size_t rn = __gmpn_set_str(r, d, len, 10);
  return (uint32_t)(r[0] + (uint64_t)rn);
}

/* `a &&& b`, `a ||| b`, `a ^^^ b` on `n` limbs each, and their comparison. */
uint32_t mpnb_and_n(b_lean_obj_arg a, b_lean_obj_arg b) {
  mp_size_t n = size(a);
  mp_limb_t *r = scratch(0, n);
  __gmpn_and_n(r, limbs(a), limbs(b), n);
  return (uint32_t)(r[0]);
}

uint32_t mpnb_ior_n(b_lean_obj_arg a, b_lean_obj_arg b) {
  mp_size_t n = size(a);
  mp_limb_t *r = scratch(0, n);
  __gmpn_ior_n(r, limbs(a), limbs(b), n);
  return (uint32_t)(r[0]);
}

uint32_t mpnb_xor_n(b_lean_obj_arg a, b_lean_obj_arg b) {
  mp_size_t n = size(a);
  mp_limb_t *r = scratch(0, n);
  __gmpn_xor_n(r, limbs(a), limbs(b), n);
  return (uint32_t)(r[0]);
}

uint32_t mpnb_cmp(b_lean_obj_arg a, b_lean_obj_arg b) {
  return (uint32_t)((uint64_t)(int64_t)__gmpn_cmp(limbs(a), limbs(b), size(a)));
}
