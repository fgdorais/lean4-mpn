/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import MPN.Generic.Ops
public import MPN64.Num
public import MPN.Join
public import MPN.Generic.OpsArray

/-!
# The operations of the 64-bit instance of `NatOps`

`ops64With div` runs the base-generic algorithms on whole arrays of 64-bit limbs with the
operations of `MPN.Num` and the division `div`: the schoolbook division for the base-generic
divide-and-conquer division (`ops64B`, `MPN.Div.DC`), and `Num.divMod` for the others (`ops64`,
`MPN.Generic.Ops64`). Those are proved for arrays of fewer than `USize.size`
limbs, which every array that fits in memory has, but which the logical model of arrays does not
know; so each operation checks that its operands are small enough (`fits`, on constants that are
machine words), and otherwise computes with `Nat` (`ofNatN`). That branch cannot run: it would
need arrays of more than `2³¹` limbs on a 32-bit platform or `2⁶²` on a 64-bit one.
-/

open ScalarArray UInt64Array

namespace MPN.W64

/-! ## Sizes -/

/-- Whether `n` is below `USize.size`: `main`'s `WordArray.fitsU`. -/
@[inline] public def fits (n : Nat) : Bool := WordArray.fitsU n

public theorem lt_of_fits {n : Nat} (h : fits n = true) : n < USize.size := WordArray.lt_of_fitsU h

/-! ## The fallback -/

/-- The `len` low limbs of `n`: `main`'s `WordArray.ofNatLen`, by halves. -/
public def ofNatN (n len : Nat) : UInt64Array := WordArray.ofNatLen n len

public theorem size_ofNatN (n len : Nat) : (ofNatN n len).size = len := by
  rw [ofNatN]; exact WordArray.size_ofNatLen (A := UInt64Array) n len

public theorem toNat_ofNatN (n len : Nat) : (ofNatN n len).toNat = n % 2 ^ (64 * len) := by
  rw [toNat_eq_valAt, size_ofNatN, ofNatN]
  exact WordArray.valAt_ofNatLen (A := UInt64Array) n len

/-- The limbs of `n`. -/
public def ofNat (n : Nat) : UInt64Array := ofNatN n (n.log2 / 64 + 1)

public theorem toNat_ofNat (n : Nat) : (ofNat n).toNat = n := by
  rw [ofNat, toNat_ofNatN, Nat.mod_eq_of_lt]
  rcases Nat.eq_zero_or_pos n with h | h
  · subst h; exact Nat.two_pow_pos _
  · exact Nat.lt_of_lt_of_le Nat.lt_log2_self (Nat.pow_le_pow_right (by decide) (by lia))

public theorem toNat_lt_pow (x : UInt64Array) : x.toNat < (2 ^ 64) ^ x.size := by
  rw [toNat_eq_valAt, ← Nat.pow_mul]; exact valAt_lt ..

/-! ## Trimming -/

/--
`x` without its zero limbs on top, but at least one limb: the operations of `MPN.Num` leave such
limbs, and the generic algorithms decide by sizes. It is `main`'s `WordArray.trimTo 1`, which pops
them, in place when `x` is not shared, which the fresh results of `MPN.Num` never are; it is `x`
itself when its top limb is nonzero.
-/
public def trimA (x : UInt64Array) : UInt64Array := WordArray.trimTo 1 x

@[simp] public theorem toNat_trimA (x : UInt64Array) : (trimA x).toNat = x.toNat := by
  rw [toNat_eq_valAt, toNat_eq_valAt, trimA]
  exact WordArray.valAt_trimTo 1 x

public theorem size_trimA_le (x : UInt64Array) : (trimA x).size ≤ max x.size 1 := by
  rw [trimA]; exact Nat.le_trans (WordArray.size_trimTo_le 1 x) (Nat.le_max_left ..)

/-- `trimA x` has at most one limb or a nonzero top limb. -/
public theorem trimA_trimmed (x : UInt64Array) :
    (trimA x).size ≤ 1 ∨ (trimA x)[(trimA x).size - 1]! ≠ 0 := by
  rw [trimA]
  rcases (WordArray.trimTo_spec 1 x).2.2.2 with h | h
  · exact .inl h
  · exact .inr fun e => h (by
      show (WordArray.trimTo 1 x)[(WordArray.trimTo 1 x).size - 1]!.toNat = 0; rw [e]; rfl)

/-- `trimA x` is one limb or has a nonzero top limb, for `x` of one limb at least. -/
public theorem trimA_top (x : UInt64Array) (h : 1 ≤ x.size) :
    (trimA x).size = 1 ∨ (1 < (trimA x).size ∧ (trimA x)[(trimA x).size - 1]! ≠ 0) := by
  have hge : 1 ≤ (trimA x).size := by
    have := WordArray.le_size_trimTo 1 x
    rw [trimA]
    exact Nat.le_trans (by show 1 ≤ min 1 x.size; lia) this
  rcases trimA_trimmed x with e | e
  · exact .inl (by lia)
  · rcases Nat.lt_or_ge 1 (trimA x).size with h' | h'
    · exact .inr ⟨h', e⟩
    · exact .inl (by lia)

/-! ## The instance -/

/-- The value of `main`'s shared instances is `toNat`. -/
public theorem vA_eq_toNat (x : UInt64Array) : WordArray.vA x = x.toNat := (toNat_eq_valAt x).symm

/-- The operations of `MPN.Num` for `main`'s `WordArray.opsA`, with their bounds. -/
@[expose] public def numOps64 : WordArray.ArrayOps UInt64Array where
  mul := Num.mul
  val_mul x y h := by
    have hU : x.size + y.size + 1 < USize.size := WordArray.lt_of_fitsU h
    rw [vA_eq_toNat, vA_eq_toNat, vA_eq_toNat]; exact Num.toNat_mul x y (by lia)
  sqr := Num.sqr
  val_sqr x h := by
    have hU : 2 * x.size + 1 < USize.size := WordArray.lt_of_fitsU h
    rw [vA_eq_toNat, vA_eq_toNat]; exact Num.toNat_sqr x (by lia)
  add := Num.add
  val_add x y h := by
    have hU : x.size + y.size + 1 < USize.size := WordArray.lt_of_fitsU h
    rw [vA_eq_toNat, vA_eq_toNat, vA_eq_toNat]; exact Num.toNat_add x y hU
  sub := Num.sub
  val_sub x y h hle := by
    have hU : x.size + y.size + 1 < USize.size := WordArray.lt_of_fitsU h
    rw [vA_eq_toNat, vA_eq_toNat] at hle
    rw [vA_eq_toNat, vA_eq_toNat, vA_eq_toNat]; exact Num.toNat_sub x y hle (by lia) (by lia)

/-- `(x / y, x mod y)` by the schoolbook division `Num.divModBase`. -/
public def divBase64 (x y : UInt64Array) : UInt64Array × UInt64Array :=
  if fits (x.size + y.size + 1) then
    let p := Num.divModBase x y
    (trimA p.1, trimA p.2)
  else (ofNat (x.toNat / y.toNat), ofNat (x.toNat % y.toNat))

public theorem val_divBase64 (x y : UInt64Array) (hy : y.toNat ≠ 0) :
    (divBase64 x y).1.toNat = x.toNat / y.toNat ∧ (divBase64 x y).2.toNat = x.toNat % y.toNat := by
  rw [divBase64]; split
  · rename_i h
    dsimp only
    rw [toNat_trimA, toNat_trimA]
    exact Num.toNat_divModBase _ _ (by lia) (lt_of_fits h)
  · exact ⟨toNat_ofNat _, toNat_ofNat _⟩

/--
The operations of `MPN.Num` as `NatOps` at base `2⁶⁴`, with the division `div`: `main`'s
`WordArray.opsA` on `numOps64`, trimmed to one limb, with the thresholds of `config.mul`.
-/
@[expose] public def ops64With (div : UInt64Array → UInt64Array → UInt64Array × UInt64Array)
    (hdiv : ∀ x y, y.toNat ≠ 0 →
      (div x y).1.toNat = x.toNat / y.toNat ∧ (div x y).2.toNat = x.toNat % y.toNat) :
    NatOps UInt64Array :=
  WordArray.opsA 1 numOps64 config.mul div fun x y h => by
    rw [vA_eq_toNat] at h
    rw [vA_eq_toNat, vA_eq_toNat, vA_eq_toNat, vA_eq_toNat]; exact hdiv x y h

/-- The instance with the schoolbook division, for the divide-and-conquer division over it. -/
@[expose] public def ops64B : NatOps UInt64Array := ops64With divBase64 val_divBase64

@[simp] public theorem ops64B_val (x : UInt64Array) : ops64B.val x = x.toNat := vA_eq_toNat x

@[simp] public theorem ops64B_B : ops64B.B = 2 ^ 64 := rfl

end MPN.W64
