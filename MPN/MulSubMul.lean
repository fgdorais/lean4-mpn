/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import MPN.Basic
public import MPN.UInt
public import MPN.ValAt
public import MPN.LinComb

/-!
# Linear combinations of two numbers by words

The steps of `main`'s `LinComb.mulSubMul` and `LinComb.mulAddMul` on 32-bit limbs, `a x - b y` and
`a x + b y` for words `a, b < 2³¹` in one pass over the limbs of `x` and `y`, and the instance
`linComb32`: `main`'s `LehmerStep` applies the cofactors of Lehmer's step to two numbers this way,
and multiplies the matrices of half-gcd's base case.

The value of a limb of `a x - b y`, `x a - y b` plus the carry, lies in `(-2⁶³, 2⁶³)`. The step adds
`2⁶³ - 2³¹` to make it a word, whose low half is the limb and whose high half is the next carry plus
`2³¹`, and carries that word, as `subMulBiased` does: each step is a sum and a difference of natural
numbers, and the chain from one carry to the next is an addition and a shift. Fusing the two
differences of a Lehmer step into one pass, which this file did, was 5–11% slower for `gcd` from 64
to 1024 limbs than two passes.
-/

open ScalarArray

namespace MPN

/-! ## The step -/

/--
`v + x a - y b + (h - 2³¹)`, with `h` the carry in plus `2³¹`, as its low word and the carry out
plus `2³¹`, for `a, b < 2³¹`.
-/
@[inline, expose] public def mulSubMulStep (v x y a b h : UInt32) : UInt32 × UInt32 :=
  let p := v.toUInt64 + x.toUInt64 * a.toUInt64 + 0x7FFFFFFF80000000 - y.toUInt64 * b.toUInt64
  (p.toUInt32 + h, ((p + h.toUInt64) >>> 32).toUInt32)

/-- `mulSubMulStep` with the carry in the sum, as its specification reads it. -/
private theorem mulSubMulStep_eq (v x y a b h : UInt32) :
    mulSubMulStep v x y a b h =
      ((v.toUInt64 + x.toUInt64 * a.toUInt64 + h.toUInt64 + 0x7FFFFFFF80000000 -
          y.toUInt64 * b.toUInt64).toUInt32,
        ((v.toUInt64 + x.toUInt64 * a.toUInt64 + h.toUInt64 + 0x7FFFFFFF80000000 -
          y.toUInt64 * b.toUInt64) >>> 32).toUInt32) := by
  have e : v.toUInt64 + x.toUInt64 * a.toUInt64 + h.toUInt64 + 0x7FFFFFFF80000000 -
      y.toUInt64 * b.toUInt64 = v.toUInt64 + x.toUInt64 * a.toUInt64 + 0x7FFFFFFF80000000 -
      y.toUInt64 * b.toUInt64 + h.toUInt64 := by grind
  rw [e]
  simp only [mulSubMulStep, UInt32.toUInt32_add]

public theorem mulSubMulStep_spec (v x y a b h : UInt32) (ha : a.toNat < 2 ^ 31)
    (hb : b.toNat < 2 ^ 31) :
    (mulSubMulStep v x y a b h).1.toNat + 2 ^ 32 * (mulSubMulStep v x y a b h).2.toNat +
        y.toNat * b.toNat = v.toNat + x.toNat * a.toNat + h.toNat + (2 ^ 63 - 2 ^ 31) := by
  have := v.toNat_lt
  have := x.toNat_lt
  have := y.toNat_lt
  have := h.toNat_lt
  have hxa : x.toNat * a.toNat ≤ (2 ^ 32 - 1) * (2 ^ 31 - 1) := Nat.mul_le_mul (by lia) (by lia)
  have hyb : y.toNat * b.toNat ≤ (2 ^ 32 - 1) * (2 ^ 31 - 1) := Nat.mul_le_mul (by lia) (by lia)
  rw [mulSubMulStep_eq]
  simp only [UInt64.toNat_sub, UInt64.toNat_add, UInt64.toNat_mul,
    UInt64.toNat_toUInt32, UInt32.toNat_toUInt64, UInt64.toNat_shiftRight,
    Nat.shiftRight_eq_div_pow, UInt64.toNat_ofNat, Nat.reduceMod, Nat.reducePow] at *
  generalize x.toNat * a.toNat = p at *
  generalize y.toNat * b.toNat = q at *
  rw [Nat.mod_eq_of_lt (show p < 18446744073709551616 by lia),
    Nat.mod_eq_of_lt (show q < 18446744073709551616 by lia)]
  lia

/-! ## A sum of two multiples

Each limb `x a + y b` of `a x + b y` plus the carry fits in a word of 64 bits, whose high half is
the next carry.
-/

/-- `v + x a + y b + c` as its low word and its high word, for `a, b < 2³¹`. -/
@[inline, expose] public def mulAddMulStep (v x y a b c : UInt32) : UInt32 × UInt32 :=
  let p := v.toUInt64 + x.toUInt64 * a.toUInt64 + y.toUInt64 * b.toUInt64 + c.toUInt64
  (p.toUInt32, (p >>> 32).toUInt32)

public theorem mulAddMulStep_spec (v x y a b c : UInt32) (ha : a.toNat < 2 ^ 31)
    (hb : b.toNat < 2 ^ 31) :
    (mulAddMulStep v x y a b c).1.toNat + 2 ^ 32 * (mulAddMulStep v x y a b c).2.toNat =
      v.toNat + x.toNat * a.toNat + y.toNat * b.toNat + c.toNat := by
  have := v.toNat_lt
  have := x.toNat_lt
  have := y.toNat_lt
  have := c.toNat_lt
  have hxa : x.toNat * a.toNat ≤ (2 ^ 32 - 1) * (2 ^ 31 - 1) := Nat.mul_le_mul (by lia) (by lia)
  have hyb : y.toNat * b.toNat ≤ (2 ^ 32 - 1) * (2 ^ 31 - 1) := Nat.mul_le_mul (by lia) (by lia)
  simp only [mulAddMulStep, UInt64.toNat_add, UInt64.toNat_mul, UInt64.toNat_toUInt32,
    UInt32.toNat_toUInt64, UInt64.toNat_shiftRight, Nat.shiftRight_eq_div_pow,
    UInt64.toNat_ofNat, Nat.reduceMod, Nat.reducePow] at *
  generalize x.toNat * a.toNat = p at *
  generalize y.toNat * b.toNat = q at *
  rw [Nat.mod_eq_of_lt (show p < 18446744073709551616 by lia),
    Nat.mod_eq_of_lt (show q < 18446744073709551616 by lia)]
  lia

/--
The steps of `main`'s linear combinations on `UInt32Array`: `mulSubMulStep` with its carry plus
`2³¹`, and `mulAddMulStep`, on a limb of zero.
-/
public instance linComb32 : LinCombOps UInt32Array UInt32 where
  cb := 31
  cb_lt := by decide
  zeros n := UInt32Array.replicate n 0
  size_zeros n := UInt32Array.size_replicate ..
  val_get_ge a i h := by
    show a[i]!.toNat = 0
    rw [getElem!_neg a i (Nat.not_lt.2 h)]; rfl
  limb := LinComb.limbU
  val_limb := LinComb.val_limbU (fun a i h => by show a[i]!.toNat = 0; rw [getElem!_neg a i (Nat.not_lt.2 h)]; rfl)
  maC xi yi a b c := mulAddMulStep 0 xi yi a b c
  cOK _ := True
  cOK_zero := trivial
  val_maC xi yi a b c ha hb _ := by
    refine ⟨?_, trivial⟩
    have := mulAddMulStep_spec 0 xi yi a b c ha hb
    show (mulAddMulStep 0 xi yi a b c).1.toNat + 2 ^ 32 * (mulAddMulStep 0 xi yi a b c).2.toNat =
      a.toNat * xi.toNat + b.toNat * yi.toNat + c.toNat
    rw [Nat.mul_comm a.toNat, Nat.mul_comm b.toNat]
    simpa using this
  msC xi yi a b h := mulSubMulStep 0 xi yi a b h
  sv h := (h.toNat : Int) - 2 ^ 31
  sOK _ := True
  s0 := 0x80000000
  sOK_s0 := trivial
  sv_s0 := by decide
  val_msC xi yi a b h ha hb _ := by
    refine ⟨?_, trivial⟩
    have := mulSubMulStep_spec 0 xi yi a b h ha hb
    show ((mulSubMulStep 0 xi yi a b h).1.toNat : Int) +
        2 ^ 32 * (((mulSubMulStep 0 xi yi a b h).2.toNat : Int) - 2 ^ 31) =
      a.toNat * xi.toNat - b.toNat * yi.toNat + ((h.toNat : Int) - 2 ^ 31)
    rw [Nat.mul_comm yi.toNat, Nat.mul_comm xi.toNat] at this
    simp only [UInt32.toNat_zero, Nat.zero_add] at this
    lia
  sNeg h := decide (h < 0x80000000)
  sNeg_iff h _ := by
    show decide (h < 0x80000000) = true ↔ (h.toNat : Int) - 2 ^ 31 < 0
    rw [decide_eq_true_eq, UInt32.lt_iff_toNat_lt,
      show (0x80000000 : UInt32).toNat = 2 ^ 31 from rfl]
    lia
  sTop h := h - 0x80000000
  val_sTop h _ hs := by
    show ((h - 0x80000000).toNat : Int) = (h.toNat : Int) - 2 ^ 31
    change 0 ≤ (h.toNat : Int) - 2 ^ 31 at hs
    have e : (0x80000000 : UInt32).toNat = 2 ^ 31 := rfl
    rw [UInt32.toNat_sub_of_le _ _ (by rw [UInt32.le_iff_toNat_le, e]; lia), e]
    lia

end MPN
