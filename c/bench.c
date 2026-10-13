/*
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
*/
#include <lean/lean.h>
#include <stdint.h>

/* `x * y + a + b` returned as a Lean pair, which allocates the pair and boxes both words. */
LEAN_EXPORT lean_obj_res bench_uint64_mul_add_add_pair(uint64_t x, uint64_t y, uint64_t a,
                                                       uint64_t b) {
  unsigned __int128 t = (unsigned __int128)x * y + a + b;
  lean_object *p = lean_alloc_ctor(0, 2, 0);
  lean_ctor_set(p, 0, lean_box_uint64((uint64_t)t));
  lean_ctor_set(p, 1, lean_box_uint64((uint64_t)(t >> 64)));
  return p;
}

/* Schoolbook multiplication of two `UInt64Array`s, entirely in C. */
LEAN_EXPORT lean_obj_res bench_mul_c(b_lean_obj_arg a, b_lean_obj_arg b) {
  size_t na = lean_sarray_size(a), nb = lean_sarray_size(b), n = na + nb;
  lean_object *r = lean_alloc_sarray(8, n, n);
  const uint64_t *pa = (const uint64_t *)lean_sarray_cptr(a);
  const uint64_t *pb = (const uint64_t *)lean_sarray_cptr(b);
  uint64_t *pr = (uint64_t *)lean_sarray_cptr(r);
  __builtin_memset(pr, 0, n * 8);
  for (size_t i = 0; i < na; i++) {
    uint64_t c = 0;
    for (size_t j = 0; j < nb; j++) {
      unsigned __int128 t = (unsigned __int128)pa[i] * pb[j] + pr[i + j] + c;
      pr[i + j] = (uint64_t)t;
      c = (uint64_t)(t >> 64);
    }
    pr[i + nb] = c;
  }
  return r;
}

/* GMP's low-level functions, which Lean's runtime links statically. Lean does not ship `gmp.h`,
   so these are declared here. Limbs are 64 bits on the platforms we benchmark. */
typedef uint64_t mp_limb_t;
typedef long mp_size_t;
mp_limb_t __gmpn_addmul_1(mp_limb_t *rp, const mp_limb_t *up, mp_size_t n, mp_limb_t v);
mp_limb_t __gmpn_mul(mp_limb_t *rp, const mp_limb_t *up, mp_size_t un, const mp_limb_t *vp,
                     mp_size_t vn);

/* Adds `x * b` into `r` at offset `i` and stores the carry at `r[i + |b|]`, which must be zero,
   with our own `__int128` loop. Returns `r` unchanged if it is too short. */
LEAN_EXPORT lean_obj_res bench_addmul_row_c(lean_obj_arg r, b_lean_obj_arg b, uint64_t x,
                                            size_t i) {
  size_t nb = lean_sarray_size(b);
  if (i + nb >= lean_sarray_size(r)) return r;
  r = lean_sarray_ensure_exclusive(r);
  const uint64_t *pb = (const uint64_t *)lean_sarray_cptr(b);
  uint64_t *pr = (uint64_t *)lean_sarray_cptr(r) + i;
  uint64_t c = 0;
  for (size_t j = 0; j < nb; j++) {
    unsigned __int128 t = (unsigned __int128)x * pb[j] + pr[j] + c;
    pr[j] = (uint64_t)t;
    c = (uint64_t)(t >> 64);
  }
  pr[nb] = c;
  return r;
}

/* The same as `bench_addmul_row_c` with GMP's `mpn_addmul_1`. */
LEAN_EXPORT lean_obj_res bench_addmul_row_gmp(lean_obj_arg r, b_lean_obj_arg b, uint64_t x,
                                              size_t i) {
  size_t nb = lean_sarray_size(b);
  if (nb == 0 || i + nb >= lean_sarray_size(r)) return r;
  r = lean_sarray_ensure_exclusive(r);
  uint64_t *pr = (uint64_t *)lean_sarray_cptr(r) + i;
  pr[nb] = __gmpn_addmul_1(pr, (const uint64_t *)lean_sarray_cptr(b), nb, x);
  return r;
}

/* Schoolbook multiplication in C, one `mpn_addmul_1` per row. */
LEAN_EXPORT lean_obj_res bench_mul_addmul_gmp(b_lean_obj_arg a, b_lean_obj_arg b) {
  size_t na = lean_sarray_size(a), nb = lean_sarray_size(b), n = na + nb;
  lean_object *r = lean_alloc_sarray(8, n, n);
  const uint64_t *pa = (const uint64_t *)lean_sarray_cptr(a);
  const uint64_t *pb = (const uint64_t *)lean_sarray_cptr(b);
  uint64_t *pr = (uint64_t *)lean_sarray_cptr(r);
  __builtin_memset(pr, 0, n * 8);
  if (nb > 0)
    for (size_t i = 0; i < na; i++) pr[i + nb] = __gmpn_addmul_1(pr + i, pb, nb, pa[i]);
  return r;
}

/* GMP's `mpn_mul`, which switches to Karatsuba and Toom-Cook as the sizes grow. */
LEAN_EXPORT lean_obj_res bench_mul_mpn(b_lean_obj_arg a, b_lean_obj_arg b) {
  size_t na = lean_sarray_size(a), nb = lean_sarray_size(b), n = na + nb;
  lean_object *r = lean_alloc_sarray(8, n, n);
  uint64_t *pr = (uint64_t *)lean_sarray_cptr(r);
  if (na == 0 || nb == 0) {
    __builtin_memset(pr, 0, n * 8);
  } else if (na >= nb) {
    __gmpn_mul(pr, (const uint64_t *)lean_sarray_cptr(a), na, (const uint64_t *)lean_sarray_cptr(b), nb);
  } else {
    __gmpn_mul(pr, (const uint64_t *)lean_sarray_cptr(b), nb, (const uint64_t *)lean_sarray_cptr(a), na);
  }
  return r;
}

/* Conversions between `Nat` and limbs, reading Lean's `Nat` objects directly.

   A `Nat` is a scalar `2n + 1` when `n ≤ LEAN_MAX_SMALL_NAT`, and otherwise a pointer to an
   `mpz_object`: a Lean header followed by a GMP `__mpz_struct`. That layout is internal to
   Lean's runtime and holds only when it is built with GMP. A big `Nat` must exceed
   `LEAN_MAX_SMALL_NAT`, since the runtime compares scalars with big numbers without looking. */

typedef struct {
  int _mp_alloc;
  int _mp_size;
  mp_limb_t *_mp_d;
} bench_mpz_struct;

typedef struct {
  lean_object m_header;
  bench_mpz_struct m_value;
} bench_mpz_object;

LEAN_EXPORT lean_object *lean_alloc_mpz(bench_mpz_struct *v);
void __gmp_get_memory_functions(void *(**alloc)(size_t), void *(**realloc)(void *, size_t, size_t),
                                void (**free)(void *, size_t));

/* The limbs of `n` without copying. A scalar is viewed through `tmp`. */
static inline const uint64_t *bench_nat_limbs(b_lean_obj_arg n, uint64_t *tmp, size_t *len) {
  if (lean_is_scalar(n)) {
    *tmp = lean_unbox(n);
    *len = *tmp != 0;
    return tmp;
  }
  bench_mpz_struct *z = &((bench_mpz_object *)n)->m_value;
  *len = (size_t)z->_mp_size;
  return z->_mp_d;
}

/* The limbs of `n` as a new `UInt64Array`. */
LEAN_EXPORT lean_obj_res bench_of_nat(b_lean_obj_arg n) {
  uint64_t tmp;
  size_t len;
  const uint64_t *p = bench_nat_limbs(n, &tmp, &len);
  lean_object *r = lean_alloc_sarray(8, len, len);
  __builtin_memcpy(lean_sarray_cptr(r), p, len * 8);
  return r;
}

/* The limbs of `a` without trailing zeros, or `NULL` when the result is a scalar `Nat`, which is
   then stored in `small`. */
static inline const uint64_t *bench_big_limbs(b_lean_obj_arg a, size_t *len, lean_object **small) {
  const uint64_t *p = (const uint64_t *)lean_sarray_cptr(a);
  size_t n = lean_sarray_size(a);
  while (n > 0 && p[n - 1] == 0) n--;
  if (n == 0) {
    *small = lean_box(0);
    return NULL;
  }
  if (n == 1 && p[0] <= LEAN_MAX_SMALL_NAT) {
    *small = lean_box(p[0]);
    return NULL;
  }
  *len = n;
  return p;
}

/* `UInt64Array` to `Nat` through the exported `lean_alloc_mpz`, which copies the limbs twice. */
LEAN_EXPORT lean_obj_res bench_to_nat_alloc_mpz(b_lean_obj_arg a) {
  size_t n;
  lean_object *small;
  const uint64_t *p = bench_big_limbs(a, &n, &small);
  if (p == NULL) return small;
  /* A read-only view, which GMP only reads. */
  bench_mpz_struct z = {(int)n, (int)n, (mp_limb_t *)p};
  return lean_alloc_mpz(&z);
}

/* `UInt64Array` to `Nat` by building the `mpz_object` by hand, as the runtime's `alloc_mpz`
   does, which copies the limbs once. */
LEAN_EXPORT lean_obj_res bench_to_nat_hand(b_lean_obj_arg a) {
  size_t n;
  lean_object *small;
  const uint64_t *p = bench_big_limbs(a, &n, &small);
  if (p == NULL) return small;
  void *(*gmp_alloc)(size_t);
  __gmp_get_memory_functions(&gmp_alloc, NULL, NULL);
  mp_limb_t *d = (mp_limb_t *)gmp_alloc(n * 8);
  __builtin_memcpy(d, p, n * 8);
  bench_mpz_object *o = (bench_mpz_object *)lean_alloc_small_object(sizeof(bench_mpz_object));
  lean_set_st_header((lean_object *)o, LeanMPZ, 0);
  o->m_value._mp_alloc = (int)n;
  o->m_value._mp_size = (int)n;
  o->m_value._mp_d = d;
  return (lean_object *)o;
}
