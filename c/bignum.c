/*
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
*/
#include <lean/lean.h>
#include <stdint.h>

/* The full product `x * y` as its low word and, through `hi`, its high word. */
#if defined(__SIZEOF_INT128__) && !defined(BIGNUM_NO_INT128)

static inline uint64_t bignum_mul_wide(uint64_t x, uint64_t y, uint64_t *hi) {
  unsigned __int128 p = (unsigned __int128)x * y;
  *hi = (uint64_t)(p >> 64);
  return (uint64_t)p;
}

#elif defined(_MSC_VER) && defined(_M_X64) && !defined(BIGNUM_NO_INT128)

#include <intrin.h>

static inline uint64_t bignum_mul_wide(uint64_t x, uint64_t y, uint64_t *hi) {
  return _umul128(x, y, hi);
}

#else

/* Multiplies by 32-bit halves. The middle column is a sum of three 32-bit numbers, so it fits. */
static inline uint64_t bignum_mul_wide(uint64_t x, uint64_t y, uint64_t *hi) {
  uint64_t x0 = (uint32_t)x, x1 = x >> 32, y0 = (uint32_t)y, y1 = y >> 32;
  uint64_t p00 = x0 * y0, p01 = x0 * y1, p10 = x1 * y0, p11 = x1 * y1;
  uint64_t mid = (p00 >> 32) + (uint32_t)p01 + (uint32_t)p10;
  *hi = p11 + (p01 >> 32) + (p10 >> 32) + (mid >> 32);
  return (mid << 32) | (uint32_t)p00;
}

#endif

/* The high word cannot overflow since `x * y + a + b < 2¹²⁸`. */
static inline uint64_t bignum_mul_add_add(uint64_t x, uint64_t y, uint64_t a, uint64_t b,
                                          uint64_t *hi) {
  uint64_t lo = bignum_mul_wide(x, y, hi);
  lo += a;
  *hi += lo < a;
  lo += b;
  *hi += lo < b;
  return lo;
}

LEAN_EXPORT uint64_t bignum_uint64_mul_add_add_lo(uint64_t x, uint64_t y, uint64_t a, uint64_t b) {
  uint64_t hi;
  return bignum_mul_add_add(x, y, a, b, &hi);
}

LEAN_EXPORT uint64_t bignum_uint64_mul_add_add_hi(uint64_t x, uint64_t y, uint64_t a, uint64_t b) {
  uint64_t hi;
  bignum_mul_add_add(x, y, a, b, &hi);
  return hi;
}
