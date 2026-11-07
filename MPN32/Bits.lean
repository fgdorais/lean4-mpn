/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import MPN32.Mul.Limb
public import MPN.Shift
public import MPN.Bitwise
public import MPN32.Basic

/-!
# Shifts and bits

* `shiftLeft a n` is `a * 2ⁿ`: the limbs of `a` shifted left by `n % 32` bits into fresh limbs
  above `n / 32` zero limbs, by `main`'s `WordArray.lshiftW` (or `copyW` for whole limbs), which
  reads `a` where it is.
* `shiftRight a n` is `a / 2ⁿ`: the limbs of `a` from `n / 32` on shifted right by `n % 32` bits
  into fresh limbs, by `WordArray.rshiftW` (or `copyW`).
* `shrLimbs`, a right shift in place from the top limb down, divides the interpolation values of
  the Toom methods by powers of 2 and is the exact division by 2, 4 and 8.
* `land`, `lor` and `xor` of arrays, limb by limb, by `main`'s `WordArray.bitW`.

Both results are trimmed.
-/

open ScalarArray

namespace MPN.W32

/-! ## Moving limbs -/

/-- The limbs of `a` from `k` on hold `⌊a / βᵏ⌋`. -/
public theorem toNat_slice_from (a : UInt32Array.Slice) (k : Nat) (hk : k ≤ a.size) :
    toNat (a.slice k a.size) = toNat a / 2 ^ (32 * k) := by
  have h := toNat_slice_add_toNat_slice a k hk
  have hlt := toNat_lt (a.slice 0 k)
  simp only [UInt32Array.Slice.size_slice] at hlt
  rw [show min k a.size - 0 = k by lia] at hlt
  rw [← h, Nat.mul_comm (2 ^ _), Nat.add_mul_div_right _ _ (Nat.two_pow_pos _),
    Nat.div_eq_of_lt hlt, Nat.zero_add]

/-! ## Shifts -/

/--
Limb `v` shifted left by `s < 32` bits, plus the carry `c < 2^s`; the bits above go up. The carry
out depends on `v` only, not on `c`, which keeps the loop free of a dependency chain: `c` lands in
the `s` low bits, which the shift leaves zero, so the sum doesn't wrap.
-/
@[inline] public def shlStep (s : UInt64) (v c : UInt32) : UInt32 × UInt32 :=
  let w := v.toUInt64 <<< s
  (w.toUInt32 + c, (w >>> 32).toUInt32)

public theorem shlStep_spec (s : Nat) (hs : s < 32) (v c : UInt32) (hc : c.toNat < 2 ^ s) :
    (shlStep s.toUInt64 v c).1.toNat + 2 ^ 32 * (shlStep s.toUInt64 v c).2.toNat =
      v.toNat * 2 ^ s + c.toNat ∧ (shlStep s.toUInt64 v c).2.toNat < 2 ^ s := by
  have hv := v.toNat_lt
  have hs' : s.toUInt64.toNat = s := by
    simp only [Nat.toUInt64, UInt64.toNat_ofNat']
    exact Nat.mod_eq_of_lt (by lia)
  have hQ : (2 : Nat) ^ 32 = 2 ^ s * 2 ^ (32 - s) := by
    rw [← Nat.pow_add]; congr 1; lia
  have hlt : v.toNat * 2 ^ s < 2 ^ 32 * 2 ^ s := Nat.mul_lt_mul_of_pos_right hv (Nat.two_pow_pos _)
  have h64 : 2 ^ 32 * 2 ^ s ≤ 2 ^ 64 := by
    rw [← Nat.pow_add]; exact Nat.pow_le_pow_right (by decide) (by lia)
  have hw : (v.toUInt64 <<< s.toUInt64).toNat = v.toNat * 2 ^ s := by
    rw [UInt64.toNat_shiftLeft, hs', Nat.mod_eq_of_lt (show s < 64 by lia),
      UInt32.toNat_toUInt64, Nat.shiftLeft_eq, Nat.mod_eq_of_lt (by lia)]
  -- The low limb of `v 2^s` is a multiple of `2^s`, so adding `c < 2^s` stays below `β`.
  have hlow : v.toNat * 2 ^ s % 2 ^ 32 + c.toNat < 2 ^ 32 := by
    rw [hQ, Nat.mul_comm v.toNat, Nat.mul_mod_mul_left]
    have hm := Nat.mod_lt v.toNat (Nat.two_pow_pos (32 - s))
    have := Nat.mul_le_mul_left (2 ^ s) (show v.toNat % 2 ^ (32 - s) + 1 ≤ 2 ^ (32 - s) by lia)
    rw [Nat.mul_succ] at this
    lia
  have hq : v.toNat * 2 ^ s / 2 ^ 32 < 2 ^ s := by
    rw [Nat.div_lt_iff_lt_mul (by decide)]; exact Nat.lt_of_lt_of_eq hlt (Nat.mul_comm _ _)
  simp only [shlStep, UInt32.toNat_add, UInt64.toNat_toUInt32, UInt64.toNat_shiftRight, hw,
    UInt64.reduceToNat, Nat.shiftRight_eq_div_pow, Nat.reduceMod]
  rw [Nat.mod_eq_of_lt (show v.toNat * 2 ^ s / 2 ^ 32 < 2 ^ 32 by lia), Nat.mod_eq_of_lt hlow]
  refine ⟨?_, hq⟩
  have := Nat.mod_add_div (v.toNat * 2 ^ s) (2 ^ 32)
  lia

/-! ## Shifts of slices

`main`'s `WordArray.shlBits` and `shrBits` on the limbs of a slice, which read the slice where it
is instead of copying it first.
-/

/-- `a 2ⁿ`, trimmed, by `main`'s `WordArray.shlBits`. -/
public def shiftLeft (a : UInt32Array.Slice) (n : Nat) : UInt32Array :=
  trim (WordArray.shlBits a.array a.start a.size n)

@[simp] public theorem toNat_shiftLeft (a : UInt32Array.Slice) (n : Nat) :
    toNat (shiftLeft a n) = toNat a * 2 ^ n := by
  rw [shiftLeft, toNat_trim, toNat_array_eq_valAt,
    show (WordArray.shlBits a.array a.start a.size n).size = _ from
      WordArray.size_shlBits a.array a.start a.size n]
  exact WordArray.valAt_shlBits a.array a.start a.size n

public theorem isTrimmed_shiftLeft (a : UInt32Array.Slice) (n : Nat) :
    isTrimmed (shiftLeft a n) = true := isTrimmed_trim _

/-- `⌊a / 2ⁿ⌋`, trimmed, by `main`'s `WordArray.shrBits`. -/
public def shiftRight (a : UInt32Array.Slice) (n : Nat) : UInt32Array :=
  trim (WordArray.shrBits a.array a.start a.size n)

@[simp] public theorem toNat_shiftRight (a : UInt32Array.Slice) (n : Nat) :
    toNat (shiftRight a n) = toNat a / 2 ^ n := by
  rw [shiftRight, toNat_trim, toNat_array_eq_valAt,
    show (WordArray.shrBits a.array a.start a.size n).size = _ from
      WordArray.size_shrBits a.array a.start a.size n]
  exact WordArray.valAt_shrBits a.array a.start a.size n

public theorem isTrimmed_shiftRight (a : UInt32Array.Slice) (n : Nat) :
    isTrimmed (shiftRight a n) = true := isTrimmed_trim _

/-! ## Bitwise operations and comparison

`main`'s `WordArray.landA`, `lorA`, `xorA` (by `bitW` into new limbs) and `ltA`.
-/

/-- Whether `a < b`, by `main`'s `WordArray.ltAFast`. -/
public def ltA (a b : UInt32Array) : Bool := WordArray.ltAFast a b

public theorem ltA_iff (a b : UInt32Array) : ltA a b = true ↔ toNat a < toNat b := by
  rw [ltA, ← WordArray.ltA_eq_ltAFast, WordArray.ltA_iff, toNat_array_eq_valAt,
    toNat_array_eq_valAt]; rfl

/-- `a &&& b`, trimmed. -/
public def land (a b : UInt32Array) : UInt32Array := WordArray.landA 0 a b

/-- `a ||| b`, trimmed. -/
public def lor (a b : UInt32Array) : UInt32Array := WordArray.lorA 0 a b

/-- `a ^^^ b`, trimmed. -/
public def xor (a b : UInt32Array) : UInt32Array := WordArray.xorA 0 a b

@[simp] public theorem toNat_land (a b : UInt32Array) : toNat (land a b) = toNat a &&& toNat b := by
  rw [toNat_array_eq_valAt, toNat_array_eq_valAt, toNat_array_eq_valAt]
  exact WordArray.valAt_landA 0 a b

@[simp] public theorem toNat_lor (a b : UInt32Array) : toNat (lor a b) = toNat a ||| toNat b := by
  rw [toNat_array_eq_valAt, toNat_array_eq_valAt, toNat_array_eq_valAt]
  exact WordArray.valAt_lorA 0 a b

@[simp] public theorem toNat_xor (a b : UInt32Array) : toNat (xor a b) = toNat a ^^^ toNat b := by
  rw [toNat_array_eq_valAt, toNat_array_eq_valAt, toNat_array_eq_valAt]
  exact WordArray.valAt_xorA 0 a b

public theorem isTrimmed_land (a b : UInt32Array) : isTrimmed (land a b) = true :=
  isTrimmed_of_isTrimmedTo (WordArray.isTrimmedTo_bitA ..)
public theorem isTrimmed_lor (a b : UInt32Array) : isTrimmed (lor a b) = true :=
  isTrimmed_of_isTrimmedTo (WordArray.isTrimmedTo_bitA ..)
public theorem isTrimmed_xor (a b : UInt32Array) : isTrimmed (xor a b) = true :=
  isTrimmed_of_isTrimmedTo (WordArray.isTrimmedTo_bitA ..)

end MPN.W32
