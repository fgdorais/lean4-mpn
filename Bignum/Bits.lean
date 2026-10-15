/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bignum.Mul.Limb

/-!
# Shifts and bits

* `shiftLeft a n` is `a * 2ⁿ`: `n / 32` zero limbs below `a` times `2^(n % 32)`.
* `shiftRight a n` is `a / 2ⁿ`: the limbs of `a` from `n / 32` on, divided by `2^s` for
  `s = n % 32` as `a 2^(32 - s)` without its low limb, which multiplies instead of dividing.

Both results are trimmed.
-/

open ScalarArray

namespace Bignum

/-! ## Moving limbs -/

/-- The limbs of `a` from `k` on hold `⌊a / βᵏ⌋`. -/
public theorem toNat_slice_from (a : UInt32Array.Slice) (k : Nat) (hk : k ≤ a.size) :
    toNat (a.slice k a.size) = toNat a / 2 ^ (32 * k) := by
  have h := toNat_slice_add_toNat_slice a k hk
  have hlt := toNat_lt (a.slice 0 k)
  simp only [UInt32Array.Slice.size_slice] at hlt
  rw [show min k a.size - 0 = k by omega] at hlt
  rw [← h, Nat.mul_comm (2 ^ _), Nat.add_mul_div_right _ _ (Nat.two_pow_pos _),
    Nat.div_eq_of_lt hlt, Nat.zero_add]

private theorem toNat_pow_limb (s : Nat) (hs : s < 32) :
    ((1 : UInt32) <<< s.toUInt32).toNat = 2 ^ s := by
  rw [UInt32.toNat_shiftLeft]
  simp only [UInt32.toNat_one, Nat.toUInt32, UInt32.toNat_ofNat', Nat.one_shiftLeft]
  rw [Nat.mod_eq_of_lt (show s < 2 ^ 32 by omega), Nat.mod_eq_of_lt hs,
    Nat.mod_eq_of_lt (Nat.pow_lt_pow_right (by decide) hs)]

/-! ## Shifts -/

/-- `a * 2ⁿ`, trimmed. -/
public def shiftLeft (a : UInt32Array.Slice) (n : Nat) : UInt32Array :=
  trim (shiftLimbs (mulRow a ((1 : UInt32) <<< (n % 32).toUInt32)) (n / 32))

@[simp] public theorem toNat_shiftLeft (a : UInt32Array.Slice) (n : Nat) :
    toNat (shiftLeft a n) = toNat a * 2 ^ n := by
  rw [shiftLeft, toNat_trim, toNat_shiftLimbs, toNat_mulRow,
    toNat_pow_limb _ (Nat.mod_lt _ (by decide)), Nat.mul_assoc, ← Nat.pow_add]
  congr 2
  omega

public theorem isTrimmed_shiftLeft (a : UInt32Array.Slice) (n : Nat) :
    isTrimmed (shiftLeft a n) = true :=
  isTrimmed_trim _

/-- `a / 2ⁿ`, trimmed. -/
public def shiftRight (a : UInt32Array.Slice) (n : Nat) : UInt32Array :=
  if n / 32 ≤ a.size then
    let a' := a.slice (n / 32) a.size
    if n % 32 = 0 then
      trim a'.copy
    else
      let w := mulRow a' ((1 : UInt32) <<< (32 - n % 32).toUInt32)
      trim (w.toSlice 1 w.size).copy
  else
    .empty

@[simp] public theorem toNat_shiftRight (a : UInt32Array.Slice) (n : Nat) :
    toNat (shiftRight a n) = toNat a / 2 ^ n := by
  have hA := toNat_lt a
  have hn : 2 ^ n = 2 ^ (32 * (n / 32)) * 2 ^ (n % 32) := by
    rw [← Nat.pow_add]; congr 1; omega
  by_cases hq : n / 32 ≤ a.size
  · have hsl := toNat_slice_from a (n / 32) hq
    by_cases hs : n % 32 = 0
    · have e : shiftRight a n = trim (a.slice (n / 32) a.size).copy := by
        rw [shiftRight, ite_eq_left hq]
        exact ite_eq_left hs
      rw [e, toNat_trim, toNat_copy, hsl, hn, hs, Nat.pow_zero, Nat.mul_one]
    · have e : shiftRight a n = trim ((mulRow (a.slice (n / 32) a.size)
          ((1 : UInt32) <<< (32 - n % 32).toUInt32)).toSlice 1 (mulRow (a.slice (n / 32) a.size)
          ((1 : UInt32) <<< (32 - n % 32).toUInt32)).size).copy := by
        rw [shiftRight, ite_eq_left hq]
        exact ite_eq_right hs
      rw [e, toNat_trim, toNat_copy]
      have hws : 1 ≤ (mulRow (a.slice (n / 32) a.size)
          ((1 : UInt32) <<< (32 - n % 32).toUInt32)).size := by
        rw [size_mulRow]; omega
      generalize hw : mulRow (a.slice (n / 32) a.size)
        ((1 : UInt32) <<< (32 - n % 32).toUInt32) = w at hws ⊢
      have hwv : toNat w = toNat a / 2 ^ (32 * (n / 32)) * 2 ^ (32 - n % 32) := by
        rw [← hw, toNat_mulRow, toNat_pow_limb _ (by omega), hsl]
      have hwin := toNat_window w 1 w.size hws (by
        have := toNat_lt w
        simpa using this)
      rw [hwin, hwv, Nat.mul_one, hn, ← Nat.div_div_eq_div_mul]
      have h32 : 2 ^ (32 : Nat) = 2 ^ (n % 32) * 2 ^ (32 - n % 32) := by
        rw [← Nat.pow_add]; congr 1; omega
      rw [h32, Nat.mul_div_mul_right _ _ (Nat.two_pow_pos _)]
  · have e : shiftRight a n = .empty := by rw [shiftRight, ite_eq_right hq]
    rw [e, toNat_toSlice]
    simp only [UInt32Array.toList_empty, ofLimbs_nil]
    -- `a < β^a.size ≤ 2ⁿ`.
    have : 2 ^ (32 * a.size) ≤ 2 ^ n := Nat.pow_le_pow_right (by decide) (by omega)
    exact (Nat.div_eq_of_lt (by omega)).symm

public theorem isTrimmed_shiftRight (a : UInt32Array.Slice) (n : Nat) :
    isTrimmed (shiftRight a n) = true := by
  unfold shiftRight
  split
  · split
    · exact isTrimmed_trim _
    · exact isTrimmed_trim _
  · rw [isTrimmed_iff]; simp

/-! ## Bitwise operations -/

/-- Bit `j` of a number is bit `j % 32` of its limb `j / 32`. -/
public theorem testBit_ofLimbs (l : List UInt32) (j : Nat) :
    (ofLimbs l).testBit j = (l.getD (j / 32) 0).toNat.testBit (j % 32) := by
  induction l generalizing j with
  | nil => simp
  | cons x l ih =>
    rw [ofLimbs_cons, Nat.add_comm, Nat.testBit_two_pow_mul_add _ x.toNat_lt]
    by_cases hj : j < 32
    · rw [if_pos hj, Nat.div_eq_of_lt hj, Nat.mod_eq_of_lt hj]
      rfl
    · rw [if_neg hj, ih]
      have h₁ : j / 32 = (j - 32) / 32 + 1 := by omega
      have h₂ : j % 32 = (j - 32) % 32 := by omega
      rw [h₁, h₂, List.getD_cons_succ]

/-- The limbs `f (a i) (b i)`, trimmed, for a limbwise operation `f` with `f 0 0 = 0`. -/
def bitwiseLimbs (f : UInt32 → UInt32 → UInt32) (a b : UInt32Array.Slice) : UInt32Array :=
  trim (UInt32Array.ofFn (n := max a.size b.size) fun i => f (a.getD i 0) (b.getD i 0))

private theorem getD_bitwiseLimbs (f : UInt32 → UInt32 → UInt32) (hf : f 0 0 = 0)
    (a b : UInt32Array.Slice) (k : Nat) :
    (UInt32Array.ofFn (n := max a.size b.size) fun i => f (a.getD i 0) (b.getD i 0)).toList.getD
      k 0 = f (a.getD k 0) (b.getD k 0) := by
  rw [UInt32Array.toList_ofFn, List.getD_eq_getElem?_getD]
  by_cases hk : k < max a.size b.size
  · rw [List.getElem?_ofFn]
    simp [hk]
  · rw [List.getElem?_ofFn]
    simp only [hk, ↓reduceDIte, Option.getD_none]
    rw [UInt32Array.Slice.getD_eq, UInt32Array.Slice.getD_eq]
    simp only [show ¬ k < a.size by omega, show ¬ k < b.size by omega, ↓reduceDIte]
    exact hf.symm

private theorem testBit_bitwiseLimbs (f : UInt32 → UInt32 → UInt32) (hf : f 0 0 = 0)
    (a b : UInt32Array.Slice) (j : Nat) :
    (toNat (bitwiseLimbs f a b)).testBit j =
      (f (a.getD (j / 32) 0) (b.getD (j / 32) 0)).toNat.testBit (j % 32) := by
  rw [bitwiseLimbs, toNat_trim, toNat_toSlice, testBit_ofLimbs, getD_bitwiseLimbs f hf]

private theorem testBit_toNat (a : UInt32Array.Slice) (j : Nat) :
    (toNat a).testBit j = (a.getD (j / 32) 0).toNat.testBit (j % 32) := by
  rw [toNat, testBit_ofLimbs, ← getD_eq_getD_toList_copy]

/-- `a &&& b`, trimmed. -/
public def land (a b : UInt32Array.Slice) : UInt32Array := bitwiseLimbs (· &&& ·) a b

/-- `a ||| b`, trimmed. -/
public def lor (a b : UInt32Array.Slice) : UInt32Array := bitwiseLimbs (· ||| ·) a b

/-- `a ^^^ b`, trimmed. -/
public def xor (a b : UInt32Array.Slice) : UInt32Array := bitwiseLimbs (· ^^^ ·) a b

@[simp] public theorem toNat_land (a b : UInt32Array.Slice) :
    toNat (land a b) = toNat a &&& toNat b := by
  apply Nat.eq_of_testBit_eq
  intro j
  rw [land, testBit_bitwiseLimbs _ (by decide), UInt32.toNat_and, Nat.testBit_and, Nat.testBit_and,
    testBit_toNat, testBit_toNat]

@[simp] public theorem toNat_lor (a b : UInt32Array.Slice) :
    toNat (lor a b) = toNat a ||| toNat b := by
  apply Nat.eq_of_testBit_eq
  intro j
  rw [lor, testBit_bitwiseLimbs _ (by decide), UInt32.toNat_or, Nat.testBit_or, Nat.testBit_or,
    testBit_toNat, testBit_toNat]

@[simp] public theorem toNat_xor (a b : UInt32Array.Slice) :
    toNat (xor a b) = toNat a ^^^ toNat b := by
  apply Nat.eq_of_testBit_eq
  intro j
  rw [xor, testBit_bitwiseLimbs _ (by decide), UInt32.toNat_xor, Nat.testBit_xor, Nat.testBit_xor,
    testBit_toNat, testBit_toNat]

public theorem isTrimmed_land (a b : UInt32Array.Slice) : isTrimmed (land a b) = true :=
  isTrimmed_trim _
public theorem isTrimmed_lor (a b : UInt32Array.Slice) : isTrimmed (lor a b) = true :=
  isTrimmed_trim _
public theorem isTrimmed_xor (a b : UInt32Array.Slice) : isTrimmed (xor a b) = true :=
  isTrimmed_trim _

end Bignum
