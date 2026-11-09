/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ScalarArray

/-!
# GMP's kernels

The `mpn_*` functions of the GMP that Lean links into its executables for `Nat`, which `Bench/mpn.c`
calls on the limbs of `UInt64Array`s: the `mpn` column of the benches, GMP's kernels without the
`mpz` layer of Lean's `Nat`. Only the bench executables link them; the library never calls GMP.

Each returns an O(1) check of its result, a `UInt32`, which Lean boxes without allocating, unlike
a `UInt64` in the polymorphic timing loop. It writes the result into scratch buffers of its own, so
that the time is the kernel's alone, without allocating the result. The operands must satisfy
GMP's requirements, which the C does not check: no zero top limb where a function says so, and the
first operand at least as long as the second.
-/

open ScalarArray

namespace Bench.Mpn

/-- `mpn_add`: `a + b`, `a` at least as long as `b`. -/
@[extern "mpnb_add"] public opaque add (a b : @& UInt64Array) : UInt32
/-- `mpn_sub`: `a - b`, for `a ≥ b`. -/
@[extern "mpnb_sub"] public opaque sub (a b : @& UInt64Array) : UInt32
/-- `mpn_lshift`: `a 2ˢ`, for `0 < s < 64`. -/
@[extern "mpnb_lshift"] public opaque lshift (a : @& UInt64Array) (s : UInt32) : UInt32
/-- `mpn_rshift`: `⌊a / 2ˢ⌋`, for `0 < s < 64`. -/
@[extern "mpnb_rshift"] public opaque rshift (a : @& UInt64Array) (s : UInt32) : UInt32
/-- `mpn_mul_1`: `a v`. -/
@[extern "mpnb_mul_1"] public opaque mul1 (a : @& UInt64Array) (v : UInt64) : UInt32
/-- `mpn_addmul_1`: `r + a v`, into a buffer of the C. -/
@[extern "mpnb_addmul_1"] public opaque addMul1 (a : @& UInt64Array) (v : UInt64) : UInt32
/-- `mpn_mul`: `a b`, `a` at least as long as `b`, by GMP's choice of algorithm. -/
@[extern "mpnb_mul"] public opaque mul (a b : @& UInt64Array) : UInt32
/-- `mpn_sqr`: `a²`. -/
@[extern "mpnb_sqr"] public opaque sqr (a : @& UInt64Array) : UInt32
/-- `mpn_divrem_1`: `a / d` and `a % d`, for a word `d ≠ 0`. -/
@[extern "mpnb_divrem_1"] public opaque divRem1 (a : @& UInt64Array) (d : UInt64) : UInt32
/-- `mpn_mod_1`: `a % d`, for a word `d ≠ 0`. -/
@[extern "mpnb_mod_1"] public opaque mod1 (a : @& UInt64Array) (d : UInt64) : UInt32
/-- `mpn_tdiv_qr`: `a / b` and `a % b`, `a` at least as long as `b`, whose top limb is not zero. -/
@[extern "mpnb_tdiv_qr"] public opaque tdivQR (a b : @& UInt64Array) : UInt32
/-- `mpn_sqrtrem`: `⌊√a⌋`, and the remainder when `rem`, for a nonzero top limb. -/
@[extern "mpnb_sqrtrem"] public opaque sqrtRem (a : @& UInt64Array) (rem : Bool) : UInt32
/-- `mpn_gcd` on the odd parts, as `mpz_gcd`, for nonzero `a` and `b`. -/
@[extern "mpnb_gcd"] public opaque gcd (a b : @& UInt64Array) : UInt32
/-- `mpn_get_str`: the decimal digits, as characters, for a nonzero top limb. -/
@[extern "mpnb_get_str"] public opaque getStr (a : @& UInt64Array) : UInt32
/-- `mpn_set_str`: the limbs of a string of decimal digits without a leading zero. -/
@[extern "mpnb_set_str"] public opaque setStr (s : @& String) : UInt32
/-- `mpn_and_n`: `a &&& b`, on two numbers of the same size. -/
@[extern "mpnb_and_n"] public opaque andN (a b : @& UInt64Array) : UInt32
/-- `mpn_ior_n`: `a ||| b`, on two numbers of the same size. -/
@[extern "mpnb_ior_n"] public opaque iorN (a b : @& UInt64Array) : UInt32
/-- `mpn_xor_n`: `a ^^^ b`, on two numbers of the same size. -/
@[extern "mpnb_xor_n"] public opaque xorN (a b : @& UInt64Array) : UInt32
/-- `mpn_cmp`: the comparison of two numbers of the same size. -/
@[extern "mpnb_cmp"] public opaque cmp (a b : @& UInt64Array) : UInt32

/-- The 64-bit limbs of `n`, from the lowest, without a zero top limb; `[0]` for `0`. -/
public def limbs (n : Nat) : UInt64Array := Id.run do
  let mut r := UInt64Array.emptyWithCapacity (n.log2 / 64 + 1)
  let mut m := n
  repeat
    r := r.push m.toUInt64
    m := m / 2 ^ 64
    if m = 0 then break
  return r

end Bench.Mpn
