/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import MPN.Generic.Ops
public import MPN.Dispatch
public import MPN.Join
public import MPN.Trim

/-!
# `NatOps` on arrays of limbs, for limbs of any width

`opsA k O cfg div hdiv` is the instance of `NatOps` on arrays of `w`-bit limbs at base `2ʷ` that
runs the base-generic algorithms on a width's own operations: `O` gives the products, the sum and
the difference (`ArrayOps`, specified below the sizes of `fitsU`), and `div` the division; the rest
is shared: `lo` and `hi` copy their limbs out (`extract`), `shl` is `shlBits`, `join` is `joinW`,
`le` is `ltA`, and `mulMod` is the wrapped product `Dispatch.mulModW` with the thresholds `cfg`.
The results of the products, the sum, the difference, `shl` and `mulMod` are trimmed to `k` limbs,
so that the next products see no zero limbs on top, and past the sizes of `fitsU` every operation
computes from the values, which never happens.
-/

namespace MPN.WordArray

open LimbArray

variable {A L : Type} [LA : LimbArray A L] [R : WordArray A L] [F : WordFolds A L]

/-- The value of an array. -/
public abbrev vA (x : A) : Nat := valAt x 0 (LA.size x)

/-- A width's operations on arrays, specified below the sizes that `fitsU` decides. -/
public structure ArrayOps (A : Type) {L : Type} [LA : LimbArray A L] where
  mul : A → A → A
  val_mul : ∀ x y, fitsU (LA.size x + LA.size y + 1) = true → vA (mul x y) = vA x * vA y
  sqr : A → A
  val_sqr : ∀ x, fitsU (2 * LA.size x + 1) = true → vA (sqr x) = vA x * vA x
  add : A → A → A
  val_add : ∀ x y, fitsU (LA.size x + LA.size y + 1) = true → vA (add x y) = vA x + vA y
  sub : A → A → A
  val_sub : ∀ x y, fitsU (LA.size x + LA.size y + 1) = true → vA y ≤ vA x →
    vA (sub x y) = vA x - vA y

omit R F in
/-- The low `k` limbs of a value. -/
private theorem valAt_min (x : A) (k : Nat) :
    valAt x 0 (min k (LA.size x)) = vA x % 2 ^ (LA.w * k) := by
  rcases Nat.le_total k (LA.size x) with h | h
  · rw [Nat.min_eq_left h, valAt_mod _ _ h]
  · rw [Nat.min_eq_right h, Nat.mod_eq_of_lt]
    exact Nat.lt_of_lt_of_le (valAt_lt ..) (Nat.pow_le_pow_right (by decide)
      (Nat.mul_le_mul_left _ h))

omit R F in
/-- The limbs from `k` on of a value. -/
private theorem valAt_from (x : A) (k : Nat) :
    valAt x k (LA.size x - k) = vA x / 2 ^ (LA.w * k) := by
  rcases Nat.le_total k (LA.size x) with h | h
  · have e := valAt_add x 0 k (LA.size x - k)
    rw [show k + (LA.size x - k) = LA.size x by lia, Nat.zero_add] at e
    rw [vA, e, Nat.add_mul_div_left _ _ (Nat.two_pow_pos _), Nat.div_eq_of_lt (valAt_lt ..),
      Nat.zero_add]
  · rw [show LA.size x - k = 0 by lia, valAt_zero, Nat.div_eq_of_lt]
    exact Nat.lt_of_lt_of_le (valAt_lt ..) (Nat.pow_le_pow_right (by decide)
      (Nat.mul_le_mul_left _ h))

omit F in
/-- The low `k` limbs of `x`, copied. -/
@[inline, expose] public def loA (k : Nat) (x : A) : A := R.extract x 0 (min k (LA.size x))

omit F in
public theorem vA_loA (k : Nat) (x : A) : vA (loA k x) = vA x % 2 ^ (LA.w * k) := by
  have e := extract_spec x 0 (min k (LA.size x)) (by lia)
  rw [Nat.zero_add] at e
  rw [vA, loA, e.1, e.2, valAt_min]

omit F in
/-- The limbs of `x` from `k` on, copied. -/
@[inline, expose] public def hiA (k : Nat) (x : A) : A := R.extract x k (LA.size x)

omit F in
public theorem size_hiA (k : Nat) (x : A) : LA.size (hiA k x) = LA.size x - k := by
  rw [hiA, R.size_extract, Nat.min_self]

omit F in
public theorem vA_hiA (k : Nat) (x : A) : vA (hiA k x) = vA x / 2 ^ (LA.w * k) := by
  rw [← valAt_from, vA, size_hiA]
  rcases Nat.le_total k (LA.size x) with h | h
  · have e := (extract_spec x k (LA.size x - k) (by lia)).2
    rwa [show k + (LA.size x - k) = LA.size x by lia] at e
  · rw [show LA.size x - k = 0 by lia, valAt_zero, valAt_zero]

/-- `x βᵏ + y mod βᵏ`, by `joinW` into new limbs. -/
@[inline, expose] public def joinA (k : Nat) (x y : A) : A :=
  if h : fitsU (k + LA.size x + LA.size y + 1) then
    joinW A k.toUSize x 0 (LA.size x).toUSize y 0 (LA.size y).toUSize (R.zeros (k + LA.size x))
      (by
        have hU := lt_of_fitsU h
        refine ⟨full_bound x (by lia), full_bound y (by lia), ?_, ?_, fun i => R.val_get_zeros ..⟩
        · rw [toNat_toUSize_of_lt (by lia), toNat_toUSize_of_lt (by lia)]; lia
        · rw [R.size_zeros, toNat_toUSize_of_lt (by lia), toNat_toUSize_of_lt (by lia)])
  else ofNatW (R := R) (vA x * 2 ^ (LA.w * k) + vA y % 2 ^ (LA.w * k))

public theorem vA_joinA (k : Nat) (x y : A) :
    vA (joinA k x y) = vA x * 2 ^ (LA.w * k) + vA y % 2 ^ (LA.w * k) := by
  unfold joinA
  split
  · rename_i h
    have hU := lt_of_fitsU h
    obtain ⟨j₁, j₂⟩ := joinW_spec (A := A) k.toUSize x 0 (LA.size x).toUSize y 0
      (LA.size y).toUSize (R.zeros (k + LA.size x)) _
    simp only [toNat_toUSize_of_lt (show k < USize.size by lia),
      toNat_toUSize_of_lt (show LA.size x < USize.size by lia),
      toNat_toUSize_of_lt (show LA.size y < USize.size by lia), USize.toNat_zero] at j₁ j₂
    rw [vA, j₁]
    exact j₂
  · exact valAt_ofNatW ..

variable [B : Toom.ToomBase A L]

/--
`NatOps` at base `2ʷ` on arrays: the width's operations `O`, trimmed to `k` limbs, and the
division `div`, with the rest shared.
-/
@[expose] public def opsA (k : Nat) (O : ArrayOps A) (cfg : Dispatch.MulConfig)
    (div : A → A → A × A)
    (hdiv : ∀ x y, vA y ≠ 0 → vA (div x y).1 = vA x / vA y ∧ vA (div x y).2 = vA x % vA y) :
    NatOps A where
  B := 2 ^ LA.w
  one_lt_B := Nat.one_lt_two_pow (Nat.pos_iff_ne_zero.1 LA.w_pos)
  val := vA
  size := LA.size
  val_lt x := by rw [← Nat.pow_mul]; exact valAt_lt ..
  mul x y := if fitsU (LA.size x + LA.size y + 1) then trimTo k (O.mul x y)
    else ofNatW (R := R) (vA x * vA y)
  val_mul x y := by
    split
    · rename_i h; rw [vA, valAt_trimTo]; exact O.val_mul x y h
    · exact valAt_ofNatW ..
  sqr x := if fitsU (2 * LA.size x + 1) then trimTo k (O.sqr x) else ofNatW (R := R) (vA x * vA x)
  val_sqr x := by
    split
    · rename_i h; rw [vA, valAt_trimTo]; exact O.val_sqr x h
    · exact valAt_ofNatW ..
  add x y := if fitsU (LA.size x + LA.size y + 1) then trimTo k (O.add x y)
    else ofNatW (R := R) (vA x + vA y)
  val_add x y := by
    split
    · rename_i h; rw [vA, valAt_trimTo]; exact O.val_add x y h
    · exact valAt_ofNatW ..
  sub x y := if fitsU (LA.size x + LA.size y + 1) then trimTo k (O.sub x y)
    else ofNatW (R := R) (vA x - vA y)
  val_sub x y hle := by
    split
    · rename_i h; rw [vA, valAt_trimTo]; exact O.val_sub x y h hle
    · exact valAt_ofNatW ..
  le x y := !ltA y x
  le_iff x y := by
    rw [Bool.not_eq_true', ← Bool.not_eq_true, ltA_iff]
    lia
  lo := loA
  val_lo k x := by rw [vA_loA, ← Nat.pow_mul]
  hi := hiA
  val_hi k x := by rw [vA_hiA, ← Nat.pow_mul]
  size_hi := size_hiA
  shl k' x := trimTo k (shlBits x 0 (LA.size x) (LA.w * k'))
  val_shl k' x := by
    rw [vA, valAt_trimTo, size_shlBits, valAt_shlBits, ← Nat.pow_mul]
  join := joinA
  val_join k x y := by rw [vA_joinA, ← Nat.pow_mul]
  pow k' := trimTo k (shlBits (ofNatW (R := R) 1) 0 (LA.size (ofNatW (R := R) 1)) (LA.w * k'))
  val_pow k' := by
    rw [vA, valAt_trimTo, size_shlBits, valAt_shlBits, valAt_ofNatW, Nat.one_mul, ← Nat.pow_mul]
  one := ofNatW (R := R) 1
  val_one := valAt_ofNatW ..
  mulModSize n := Dispatch.modSize cfg.fftKFactor n
  le_mulModSize n := Dispatch.le_modSize ..
  mulMod n x y := trimTo k (Dispatch.mulModW cfg n x 0 (LA.size x) y 0 (LA.size y))
  val_mulMod n x y := by
    rw [← Nat.pow_mul, vA, valAt_trimTo]
    exact Dispatch.mulModW_spec cfg n x 0 (LA.size x) y 0 (LA.size y)
  divRem := div
  val_divRem := hdiv

end MPN.WordArray
