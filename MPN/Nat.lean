/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import MPN.Natural
public import MPN.NatGcd
public import MPN.Gcd
public import MPN.Decimal
public import MPN.Sqrt
public import MPN.Div.DC
import Std.Data.String.ToNat

/-!
# Natural numbers

`MPN.Nat` is `main`'s `GNat` on arrays of 64-bit limbs: a natural number as a machine word below
`2⁶⁴` and as trimmed limbs above, with every operation proved correct against `Nat`. The instance
`natLimbs64` of `NatLimbs` gives it the operations of `MPN.Num`, whose results it trims (`norm`),
and limb-wise bitwise operations (`bitA`). Since `MPN.Num` leaves at least one limb, the trimmed
form here is one limb or a nonzero top limb (`isTrim`). The operations guard the bounds that the
specifications of `MPN.Num` need, and otherwise compute on `Nat`, which never happens.

The square root above `2⁶⁴` is Zimmermann's recursion of `sqrtRem`. The greatest common divisor
is `main`'s `GNat.gcd` on the instance `gcdLimbs64` of `GcdLimbs`, with Lehmer's step and half-gcd
from `MPN.Gcd`; `MPN.gcdWith` and `Num.gcd` are it on arrays.
-/

open ScalarArray UInt64Array

namespace MPN

namespace Limbs64

/-! ## Trimmed limbs -/

/-- The limb `0`, as one limb. -/
public def zero : UInt64Array := UInt64Array.replicate 1 0

/-- `x` trimmed, with one limb at least: `trimA`, or `[0]` for the empty array. -/
@[inline] public def norm (x : UInt64Array) : UInt64Array :=
  if x.size = 0 then zero else trimA x

/-- Whether `x` is trimmed: one limb, or a nonzero top limb. -/
public def isTrim (x : UInt64Array) : Bool :=
  x.size == 1 || (decide (1 < x.size) && x[x.size - 1]! != 0)

public theorem toNat_norm (x : UInt64Array) : (norm x).toNat = x.toNat := by
  unfold norm
  split
  · rename_i h
    rw [toNat_eq_valAt, toNat_eq_valAt, h]
    simp [zero, valAt_succ]
  · exact toNat_trimA x

private theorem isTrim_trimA (x : UInt64Array) (h : 1 ≤ x.size) : isTrim (trimA x) = true := by
  simp only [isTrim, Bool.or_eq_true, beq_iff_eq, Bool.and_eq_true, decide_eq_true_eq,
    bne_iff_ne, ne_eq]
  exact trimA_top x h

public theorem isTrim_norm (x : UInt64Array) : isTrim (norm x) = true := by
  unfold norm
  split
  · simp [isTrim, zero]
  · exact isTrim_trimA x (by lia)

/-- A trimmed array of more than one limb is at least `2^(64 (n - 1))`. -/
public theorem pow_le_of_isTrim {x : UInt64Array} (h : isTrim x = true) (hs : 2 ≤ x.size) :
    2 ^ (64 * (x.size - 1)) ≤ x.toNat := by
  simp only [isTrim, Bool.or_eq_true, beq_iff_eq, Bool.and_eq_true, decide_eq_true_eq,
    bne_iff_ne, ne_eq] at h
  have ht : x[x.size - 1]! ≠ 0 := by
    rcases h with h | h
    · lia
    · exact h.2
  have ht' : 1 ≤ x[x.size - 1]!.toNat :=
    Nat.pos_of_ne_zero fun e => ht (UInt64.toNat_inj.1 (by rw [e]; rfl))
  rw [toNat_eq_valAt, show x.size = (x.size - 1) + 1 by lia, UInt64Array.valAt_add, valAt_one,
    Nat.zero_add, show x.size - 1 + 1 - 1 = x.size - 1 by lia]
  have := Nat.mul_le_mul_left (2 ^ (64 * (x.size - 1))) ht'
  lia

/-- A trimmed array is below `2⁶⁴` exactly when it has one limb. -/
public theorem size_one_iff {x : UInt64Array} (h : isTrim x = true) :
    x.size = 1 ↔ x.toNat < 2 ^ 64 := by
  have hs : 1 ≤ x.size := by
    simp only [isTrim, Bool.or_eq_true, beq_iff_eq, Bool.and_eq_true, decide_eq_true_eq] at h
    lia
  constructor
  · intro e
    have := valAt_lt x 0 x.size
    rw [e] at this
    rw [toNat_eq_valAt, e]
    simpa using this
  · intro hv
    refine Nat.le_antisymm (Nat.le_of_not_lt fun h₂ => ?_) hs
    have := pow_le_of_isTrim h (by lia)
    have : 2 ^ 64 ≤ 2 ^ (64 * (x.size - 1)) := Nat.pow_le_pow_right (by decide) (by lia)
    lia

/-- Two trimmed arrays of the same value are the same. -/
public theorem eq_of_toNat {a b : UInt64Array} (ha : isTrim a = true) (hb : isTrim b = true)
    (h : a.toNat = b.toNat) : a = b := by
  have hsa : 1 ≤ a.size := by
    simp only [isTrim, Bool.or_eq_true, beq_iff_eq, Bool.and_eq_true, decide_eq_true_eq] at ha
    lia
  have hsb : 1 ≤ b.size := by
    simp only [isTrim, Bool.or_eq_true, beq_iff_eq, Bool.and_eq_true, decide_eq_true_eq] at hb
    lia
  -- The sizes: one limb, or the number of limbs of the value.
  have hs : a.size = b.size := by
    by_cases h1 : a.toNat < 2 ^ 64
    · rw [(size_one_iff ha).2 h1, (size_one_iff hb).2 (by rw [← h]; exact h1)]
    · have ha2 : 2 ≤ a.size := by
        have : a.size ≠ 1 := fun e => h1 ((size_one_iff ha).1 e)
        lia
      have hb2 : 2 ≤ b.size := by
        have : b.size ≠ 1 := fun e => h1 (h ▸ (size_one_iff hb).1 e)
        lia
      have la := pow_le_of_isTrim ha ha2
      have lb := pow_le_of_isTrim hb hb2
      have ua : a.toNat < 2 ^ (64 * a.size) := by rw [toNat_eq_valAt]; exact valAt_lt ..
      have ub : b.toNat < 2 ^ (64 * b.size) := by rw [toNat_eq_valAt]; exact valAt_lt ..
      have e₁ : 64 * (a.size - 1) < 64 * b.size :=
        (Nat.pow_lt_pow_iff_right (a := 2) (by decide)).1 (by lia)
      have e₂ : 64 * (b.size - 1) < 64 * a.size :=
        (Nat.pow_lt_pow_iff_right (a := 2) (by decide)).1 (by lia)
      lia
  -- The limbs, as the digits of the value.
  have hl : ∀ i, i < a.size → a[i]! = b[i]! := by
    intro i hi
    have e₁ := LimbArray.val_get_eq a hi
    have e₂ := LimbArray.val_get_eq b (show i < b.size by lia)
    change (a[i]!).toNat = UInt64Array.valAt a 0 a.size / _ % _ at e₁
    change (b[i]!).toNat = UInt64Array.valAt b 0 b.size / _ % _ at e₂
    rw [← toNat_eq_valAt] at e₁ e₂
    exact UInt64.toNat_inj.1 (by rw [e₁, e₂, h])
  apply UInt64Array.ext
  apply Array.ext (by simpa using hs)
  intro i h₁ h₂
  have := hl i (by simpa using h₁)
  rw [getElem!_eq_getElem!_toArray, getElem!_eq_getElem!_toArray, getElem!_pos a.toArray i h₁,
    getElem!_pos b.toArray i h₂] at this
  exact this

/-! ## Bitwise operations -/

/-- Limb-wise `f` of `a` and `b`, zero past their ends, trimmed. -/
@[inline] public def bitA (f : UInt64 → UInt64 → UInt64) (a b : UInt64Array) : UInt64Array :=
  norm (UInt64Array.ofFn (n := max a.size b.size) fun i => f (Num.limbAt a i) (Num.limbAt b i))

private theorem testBit_bitA (f : UInt64 → UInt64 → UInt64) (g : Bool → Bool → Bool)
    (hf : ∀ x y : UInt64, ∀ k, (f x y).toNat.testBit k = g (x.toNat.testBit k) (y.toNat.testBit k))
    (hg : g false false = false) (a b : UInt64Array) (j : Nat) :
    (bitA f a b).toNat.testBit j = g (a.toNat.testBit j) (b.toNat.testBit j) := by
  rw [bitA, toNat_norm]
  generalize hc : UInt64Array.ofFn (n := max a.size b.size)
    (fun i => f (Num.limbAt a i) (Num.limbAt b i)) = c
  have hcs : c.size = max a.size b.size := by rw [← hc, size_ofFn]
  have hca : c.toNat = c.valAt 0 (max a.size b.size) := by rw [toNat_eq_valAt, hcs]
  have haa : a.toNat = a.valAt 0 (max a.size b.size) := (Num.valAt_ge a _ (by lia)).symm
  have hbb : b.toNat = b.valAt 0 (max a.size b.size) := (Num.valAt_ge b _ (by lia)).symm
  rw [hca, haa, hbb]
  by_cases hj : j < 64 * max a.size b.size
  · have t₁ := LimbArray.testBit_valAt c hj
    have t₂ := LimbArray.testBit_valAt a hj
    have t₃ := LimbArray.testBit_valAt b hj
    change (UInt64Array.valAt c 0 _).testBit j = (c[j / 64]!).toNat.testBit (j % 64) at t₁
    change (UInt64Array.valAt a 0 _).testBit j = (a[j / 64]!).toNat.testBit (j % 64) at t₂
    change (UInt64Array.valAt b 0 _).testBit j = (b[j / 64]!).toNat.testBit (j % 64) at t₃
    have hq : j / 64 < max a.size b.size := by lia
    have hcq : c[j / 64]! = f (Num.limbAt a (j / 64)) (Num.limbAt b (j / 64)) := by
      rw [getElem!_eq_getElem _ _ (by rw [hcs]; exact hq)]
      subst hc
      simp
    rw [t₁, t₂, t₃, hcq, hf, Num.limbAt_eq, Num.limbAt_eq]
  · have h₁ : 2 ^ (64 * max a.size b.size) ≤ 2 ^ j := Nat.pow_le_pow_right (by decide) (by lia)
    rw [Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le (valAt_lt ..) h₁),
      Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le (valAt_lt ..) h₁),
      Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le (valAt_lt ..) h₁), hg]

public theorem isTrim_bitA (f : UInt64 → UInt64 → UInt64) (a b : UInt64Array) :
    isTrim (bitA f a b) = true := isTrim_norm _

public theorem toNat_land (a b : UInt64Array) :
    (bitA (· &&& ·) a b).toNat = a.toNat &&& b.toNat :=
  Nat.eq_of_testBit_eq fun j => by
    rw [testBit_bitA _ (· && ·) (fun x y k => by rw [UInt64.toNat_and, Nat.testBit_and]) rfl,
      Nat.testBit_and]

public theorem toNat_lor (a b : UInt64Array) :
    (bitA (· ||| ·) a b).toNat = a.toNat ||| b.toNat :=
  Nat.eq_of_testBit_eq fun j => by
    rw [testBit_bitA _ (· || ·) (fun x y k => by rw [UInt64.toNat_or, Nat.testBit_or]) rfl,
      Nat.testBit_or]

public theorem toNat_xor (a b : UInt64Array) :
    (bitA (· ^^^ ·) a b).toNat = a.toNat ^^^ b.toNat :=
  Nat.eq_of_testBit_eq fun j => by
    rw [testBit_bitA _ (fun x y => x ^^ y) (fun x y k => by rw [UInt64.toNat_xor, Nat.testBit_xor])
      rfl, Nat.testBit_xor]

/-! ## Words and guarded operations

The operations of `MPN.Num` with their results trimmed, where the bounds of their specifications
hold, and on `Nat` otherwise, which never happens.
-/

/-- The limb `0` of an array. -/
@[inline] public def toWord (x : UInt64Array) : UInt64 := x[0]!

public theorem toNat_toWord (x : UInt64Array) (h : isTrim x = true) (hv : x.toNat < 2 ^ 64) :
    (toWord x).toNat = x.toNat := by
  rw [toNat_eq_valAt, (size_one_iff h).2 hv, valAt_one]
  rfl

/-- `a + b`. -/
public def add (a b : UInt64Array) : UInt64Array :=
  if fits (a.size + b.size + 1) then norm (Num.add a b) else norm (ofNat (a.toNat + b.toNat))

public theorem toNat_add (a b : UInt64Array) : (add a b).toNat = a.toNat + b.toNat := by
  unfold add
  split
  · rename_i h; rw [toNat_norm, Num.toNat_add _ _ (lt_of_fits h)]
  · rw [toNat_norm, toNat_ofNat]

/-- `a - b`, for `b ≤ a`. -/
public def sub (a b : UInt64Array) : UInt64Array :=
  if fits (a.size + b.size + 1) then norm (Num.sub a b) else norm (ofNat (a.toNat - b.toNat))

public theorem toNat_sub (a b : UInt64Array) (hle : b.toNat ≤ a.toNat) :
    (sub a b).toNat = a.toNat - b.toNat := by
  unfold sub
  split
  · rename_i h
    have := lt_of_fits h
    rw [toNat_norm, Num.toNat_sub _ _ hle (by lia) (by lia)]
  · rw [toNat_norm, toNat_ofNat]

/-- Whether `a < b`. -/
public def lt (a b : UInt64Array) : Bool :=
  if fits (a.size + b.size + 1) then Num.lt a b else decide (a.toNat < b.toNat)

public theorem lt_iff (a b : UInt64Array) : lt a b = true ↔ a.toNat < b.toNat := by
  unfold lt
  split
  · rename_i h; exact Num.lt_iff a b (by have := lt_of_fits h; lia)
  · exact decide_eq_true_iff

/-- `a b`. -/
public def mul (a b : UInt64Array) : UInt64Array :=
  if fits (a.size + b.size + 1) then norm (Num.mul a b) else norm (ofNat (a.toNat * b.toNat))

public theorem toNat_mul (a b : UInt64Array) : (mul a b).toNat = a.toNat * b.toNat := by
  unfold mul
  split
  · rename_i h; rw [toNat_norm, Num.toNat_mul _ _ (by have := lt_of_fits h; lia)]
  · rw [toNat_norm, toNat_ofNat]

/-- `a²`. -/
public def sqr (a : UInt64Array) : UInt64Array :=
  if fits (2 * a.size + 1) then norm (Num.sqr a) else norm (ofNat (a.toNat * a.toNat))

public theorem toNat_sqr (a : UInt64Array) : (sqr a).toNat = a.toNat * a.toNat := by
  unfold sqr
  split
  · rename_i h; rw [toNat_norm, Num.toNat_sqr _ (by have := lt_of_fits h; lia)]
  · rw [toNat_norm, toNat_ofNat]

/-- `1`, as one limb. -/
private def one : UInt64Array := UInt64Array.replicate 1 1

private theorem toNat_one : one.toNat = 1 := by simp [one, toNat_eq_valAt]

/-- `a / b`, and `0` for `b = 0`. -/
public def div (a b : UInt64Array) : UInt64Array :=
  if fits (a.size + b.size + 2) then
    if Num.lt b one then zero else norm (Num.div a b)
  else norm (ofNat (a.toNat / b.toNat))

public theorem toNat_div (a b : UInt64Array) : (div a b).toNat = a.toNat / b.toNat := by
  unfold div
  split
  · rename_i h
    have hU := lt_of_fits h
    split
    · rename_i h0
      rw [Num.lt_iff _ _ (by simp only [one, UInt64Array.size_replicate]; lia), toNat_one] at h0
      rw [show b.toNat = 0 by lia, Nat.div_zero]
      simp [zero, toNat_eq_valAt]
    · rename_i h0
      rw [Num.lt_iff _ _ (by simp only [one, UInt64Array.size_replicate]; lia), toNat_one] at h0
      rw [toNat_norm, Num.toNat_div _ _ (by lia) (by lia)]
  · rw [toNat_norm, toNat_ofNat]

/-- `a % b`, and `a` for `b = 0`. -/
public def mod (a b : UInt64Array) : UInt64Array :=
  if fits (a.size + b.size + 2) then
    if Num.lt b one then norm a else norm (Num.divMod a b).2
  else norm (ofNat (a.toNat % b.toNat))

public theorem toNat_mod (a b : UInt64Array) : (mod a b).toNat = a.toNat % b.toNat := by
  unfold mod
  split
  · rename_i h
    have hU := lt_of_fits h
    split
    · rename_i h0
      rw [Num.lt_iff _ _ (by simp only [one, UInt64Array.size_replicate]; lia), toNat_one] at h0
      rw [show b.toNat = 0 by lia, Nat.mod_zero, toNat_norm]
    · rename_i h0
      rw [Num.lt_iff _ _ (by simp only [one, UInt64Array.size_replicate]; lia), toNat_one] at h0
      rw [toNat_norm, (Num.toNat_divMod _ _ (by lia) (by lia)).2]
  · rw [toNat_norm, toNat_ofNat]

/-- `a 2ⁿ`. -/
public def shl (a : UInt64Array) (n : Nat) : UInt64Array :=
  if fits (n / 64 + a.size + 1) then norm (Num.shl a n) else norm (ofNat (a.toNat * 2 ^ n))

public theorem toNat_shl (a : UInt64Array) (n : Nat) : (shl a n).toNat = a.toNat * 2 ^ n := by
  unfold shl
  split
  · rename_i h; rw [toNat_norm, Num.toNat_shl _ _ (lt_of_fits h)]
  · rw [toNat_norm, toNat_ofNat]

/-- `⌊a / 2ⁿ⌋`. -/
public def shr (a : UInt64Array) (n : Nat) : UInt64Array :=
  if fits a.size then norm (Num.shr a n) else norm (ofNat (a.toNat / 2 ^ n))

public theorem toNat_shr (a : UInt64Array) (n : Nat) : (shr a n).toNat = a.toNat / 2 ^ n := by
  unfold shr
  split
  · rename_i h; rw [toNat_norm, Num.toNat_shr _ _ (lt_of_fits h)]
  · rw [toNat_norm, toNat_ofNat]

/-- `⌊log₂ a⌋`. -/
public def log2 (a : UInt64Array) : Nat :=
  if fits a.size then MPN.log2 a.toUSlice else a.toNat.log2

public theorem log2_eq' (a : UInt64Array) : log2 a = a.toNat.log2 := by
  unfold log2
  split
  · rename_i h; rw [log2_eq, toUSlice_toNat a (lt_of_fits h)]
  · rfl

/-- The limbs of a string of decimal digits, `[0]` for one that `String.isNat` rejects. -/
public def ofDecimal (s : String) : UInt64Array := norm ((Num.ofDecimal? s).getD zero)

public theorem ofDecimal_spec (s : String) (h : s.isNat = true) :
    isTrim (ofDecimal s) = true ∧ s.toNat? = some (ofDecimal s).toNat := by
  refine ⟨isTrim_norm _, ?_⟩
  have e := Num.ofDecimal?_eq s
  rw [ofDecimal, toNat_norm]
  cases hr : Num.ofDecimal? s with
  | none =>
    rw [hr, Option.map_none] at e
    rw [String.toNat?_eq_some_ofDigitChars h] at e
    exact absurd e (by simp)
  | some r =>
    rw [hr, Option.map_some] at e
    rw [← e]
    rfl

end Limbs64

/-- `main`'s whole-number operations on trimmed arrays of 64-bit limbs: `MPN.Num`'s, trimmed. -/
public instance natLimbs64 : NatLimbs UInt64Array where
  val a := a.toNat
  trimmed := Limbs64.isTrim
  eq_of_val _ _ ha hb h := Limbs64.eq_of_toNat ha hb h
  decEq := inferInstance
  hash a := hash a.toSlice
  ofNat n := Limbs64.norm (ofNat n)
  trimmed_ofNat _ := Limbs64.isTrim_norm _
  val_ofNat n := by show (Limbs64.norm (ofNat n)).toNat = n; rw [Limbs64.toNat_norm, toNat_ofNat]
  ofWord w := UInt64Array.replicate 1 w
  trimmed_ofWord w := by simp [Limbs64.isTrim]
  val_ofWord w := by show (UInt64Array.replicate 1 w).toNat = w.toNat; simp [toNat_eq_valAt]
  wide lo hi := (UInt64Array.replicate 1 lo).push hi
  wide_spec lo hi h := by
    refine ⟨?_, ?_⟩
    · show Limbs64.isTrim ((UInt64Array.replicate 1 lo).push hi) = true
      simp [Limbs64.isTrim, h]
    · show ((UInt64Array.replicate 1 lo).push hi).toNat = _
      rw [toNat_eq_valAt]
      simp [valAt_succ]
  fits a := decide (a.size ≤ 1)
  fits_iff a h := by
    rw [decide_eq_true_iff]
    have := (Limbs64.size_one_iff h)
    have : 1 ≤ a.size := by
      simp only [Limbs64.isTrim, Bool.or_eq_true, beq_iff_eq, Bool.and_eq_true, decide_eq_true_eq] at h
      lia
    change a.size ≤ 1 ↔ a.toNat < 2 ^ 64
    constructor
    · intro hs; exact (Limbs64.size_one_iff h).1 (by lia)
    · intro hv; have := (Limbs64.size_one_iff h).2 hv; lia
  toWord := Limbs64.toWord
  val_toWord a h hv := Limbs64.toNat_toWord a h hv
  add := Limbs64.add
  trimmed_add a b := by unfold Limbs64.add; split <;> exact Limbs64.isTrim_norm _
  val_add := Limbs64.toNat_add
  sub := Limbs64.sub
  trimmed_sub a b := by unfold Limbs64.sub; split <;> exact Limbs64.isTrim_norm _
  val_sub a b h := Limbs64.toNat_sub a b h
  lt := Limbs64.lt
  lt_iff := Limbs64.lt_iff
  mul := Limbs64.mul
  trimmed_mul a b := by unfold Limbs64.mul; split <;> exact Limbs64.isTrim_norm _
  val_mul := Limbs64.toNat_mul
  sqr := Limbs64.sqr
  trimmed_sqr a := by unfold Limbs64.sqr; split <;> exact Limbs64.isTrim_norm _
  val_sqr := Limbs64.toNat_sqr
  div := Limbs64.div
  trimmed_div a b := by
    unfold Limbs64.div
    split
    · split
      · simp [Limbs64.isTrim, Limbs64.zero]
      · exact Limbs64.isTrim_norm _
    · exact Limbs64.isTrim_norm _
  val_div := Limbs64.toNat_div
  mod := Limbs64.mod
  trimmed_mod a b := by
    unfold Limbs64.mod
    split
    · split <;> exact Limbs64.isTrim_norm _
    · exact Limbs64.isTrim_norm _
  val_mod := Limbs64.toNat_mod
  divW a b := Limbs64.div a (UInt64Array.replicate 1 b)
  trimmed_divW a b := by
    show Limbs64.isTrim (Limbs64.div a _) = true
    unfold Limbs64.div
    split
    · split
      · simp [Limbs64.isTrim, Limbs64.zero]
      · exact Limbs64.isTrim_norm _
    · exact Limbs64.isTrim_norm _
  val_divW a b _ := by
    show (Limbs64.div a _).toNat = _
    rw [Limbs64.toNat_div]
    simp [toNat_eq_valAt]
  modW a b := Limbs64.toWord (Limbs64.mod a (UInt64Array.replicate 1 b))
  val_modW a b hb := by
    have hb' : 0 < b.toNat := Nat.pos_of_ne_zero fun e => hb (UInt64.toNat_inj.1 (by simpa using e))
    have hv : (UInt64Array.replicate 1 b).toNat = b.toNat := by simp [toNat_eq_valAt]
    have hm := Limbs64.toNat_mod a (UInt64Array.replicate 1 b)
    rw [hv] at hm
    have ht : Limbs64.isTrim (Limbs64.mod a (UInt64Array.replicate 1 b)) = true := by
      unfold Limbs64.mod
      split
      · split <;> exact Limbs64.isTrim_norm _
      · exact Limbs64.isTrim_norm _
    rw [Limbs64.toNat_toWord _ ht (by rw [hm]; exact Nat.lt_trans (Nat.mod_lt _ hb') b.toNat_lt), hm]
  shl := Limbs64.shl
  trimmed_shl a n := by unfold Limbs64.shl; split <;> exact Limbs64.isTrim_norm _
  val_shl := Limbs64.toNat_shl
  shr := Limbs64.shr
  trimmed_shr a n := by unfold Limbs64.shr; split <;> exact Limbs64.isTrim_norm _
  val_shr := Limbs64.toNat_shr
  land := Limbs64.bitA (· &&& ·)
  trimmed_land _ _ := Limbs64.isTrim_bitA _ _ _
  val_land := Limbs64.toNat_land
  lor := Limbs64.bitA (· ||| ·)
  trimmed_lor _ _ := Limbs64.isTrim_bitA _ _ _
  val_lor := Limbs64.toNat_lor
  xor := Limbs64.bitA (· ^^^ ·)
  trimmed_xor _ _ := Limbs64.isTrim_bitA _ _ _
  val_xor := Limbs64.toNat_xor
  log2 := Limbs64.log2
  log2_eq a _ _ := Limbs64.log2_eq' a
  toDecimal := Num.toDecimal
  toDecimal_eq a _ := Num.toDecimal_eq a
  ofDecimal := Limbs64.ofDecimal
  ofDecimal_spec := Limbs64.ofDecimal_spec

namespace Limbs64

/-- The `GNat` of an array, trimmed. -/
@[inline] public def toGNat (x : UInt64Array) : GNat UInt64Array := GNat.ofLimbs (norm x) (isTrim_norm x)

@[simp] public theorem toNat_toGNat (x : UInt64Array) : (toGNat x).toNat = x.toNat := by
  rw [toGNat, GNat.toNat_ofLimbs]; exact toNat_norm x

/-- Lehmer's step (`lehmerStep`) on the limbs of `x` and `y`. -/
public def lehmer (x y : GNat UInt64Array) : Option (GNat UInt64Array × GNat UInt64Array) :=
  match lehmerStep x.limbs y.limbs with
  | some p => some (toGNat p.1, toGNat p.2)
  | none => none

public theorem gcd_lehmer (x y : GNat UInt64Array) (p : GNat UInt64Array × GNat UInt64Array)
    (h : lehmer x y = some p) : Nat.gcd p.1.toNat p.2.toNat = Nat.gcd x.toNat y.toNat := by
  unfold lehmer at h
  split at h
  · rename_i q hq
    rw [Option.some.injEq] at h
    subst h
    simp only [toNat_toGNat]
    rw [gcd_lehmerStep _ _ q hq, ← GNat.val_limbs x, ← GNat.val_limbs y]
    rfl
  · exact absurd h (by simp)

/-- Half-gcd (`hgcd64`) on the limbs of `x` and `y`. -/
public def hgcd (x y : GNat UInt64Array) : GNat UInt64Array × GNat UInt64Array :=
  let p := hgcd64 x.limbs y.limbs
  (toGNat p.1, toGNat p.2)

public theorem gcd_hgcd (x y : GNat UInt64Array) :
    Nat.gcd (hgcd x y).1.toNat (hgcd x y).2.toNat = Nat.gcd x.toNat y.toNat := by
  simp only [hgcd, toNat_toGNat]
  rw [gcd_hgcd64, ← GNat.val_limbs x, ← GNat.val_limbs y]
  rfl

/-- The high word of a number of at most two limbs. -/
public def hi : GNat UInt64Array → UInt64
  | .small _ => 0
  | .large a _ => Num.limbAt a 1

/-- The low word of a number. -/
public def lo : GNat UInt64Array → UInt64
  | .small w => w
  | .large a _ => Num.limbAt a 0

/-- Whether a number has at most two limbs. -/
public def fits2 : GNat UInt64Array → Bool
  | .small _ => true
  | .large a _ => decide (a.size ≤ 2)

public theorem val_two (x : GNat UInt64Array) (h : fits2 x = true) :
    (hi x).toNat * 2 ^ 64 + (lo x).toNat = x.toNat := by
  cases x with
  | small w => simp [hi, lo, GNat.toNat_small]
  | large a ha =>
    simp only [fits2, decide_eq_true_eq] at h
    show (Num.limbAt a 1).toNat * 2 ^ 64 + (Num.limbAt a 0).toNat = a.toNat
    rw [Num.limbAt_eq, Num.limbAt_eq]
    rcases Nat.lt_or_ge a.size 2 with h1 | h1
    · rw [getElem!_neg a 1 (by lia), toNat_eq_valAt]
      change 0 * 2 ^ 64 + _ = _
      rcases Nat.lt_or_ge a.size 1 with h0 | h0
      · rw [show a.size = 0 by lia, getElem!_neg a 0 (by lia), valAt_zero]; rfl
      · rw [show a.size = 1 by lia, valAt_one]; lia
    · rw [toNat_eq_valAt, show a.size = 2 by lia, valAt_succ, valAt_one]
      lia

/-- The size of a number, in limbs. -/
public def size : GNat UInt64Array → Nat
  | .small _ => 1
  | .large a _ => a.size

end Limbs64

/-- The parts of `main`'s greatest common divisor that depend on 64-bit limbs. -/
public instance gcdLimbs64 : GcdLimbs UInt64Array where
  mulh := UInt64.mulh
  toNat_mulh := UInt64.toNat_mulh
  rem2 ah al bl := al - UInt64.div2 (ah % bl) al bl * bl
  toNat_rem2 ah al bl hb := by
    rw [(UInt64.toNat_div2_rem (ah % bl) al bl
      (by rw [UInt64.toNat_mod]; exact Nat.mod_lt _ hb)).1, UInt64.toNat_mod]
    simp [Nat.add_mod, Nat.mul_mod]
  fits2 := Limbs64.fits2
  hi := Limbs64.hi
  lo := Limbs64.lo
  val_two := Limbs64.val_two
  lehmer := Limbs64.lehmer
  gcd_lehmer := Limbs64.gcd_lehmer
  hgcd := Limbs64.hgcd
  gcd_hgcd := Limbs64.gcd_hgcd
  size := Limbs64.size
  half := config.gcdHalf

/-- A natural number: `main`'s `GNat` on arrays of 64-bit limbs. -/
public protected abbrev Nat := GNat UInt64Array

namespace Nat

export GNat (small large ofLimbs wideOf toNat_wideOf add sub mul div mod blt decEq shiftLeft
  shiftRight land lor xor sqr pow sqrtNewton toNat_ofNat toNat_small toNat_inj ofNat_toNat
  trimmed_limbs toNat_add toNat_sub toNat_mul toNat_div toNat_mod blt_iff toNat_shiftLeft
  toNat_shiftRight toNat_land toNat_lor toNat_xor log2_eq toNat_sqr toNat_pow toNat_sqrtNewton
  repr_eq ofString?_eq toNat_hAdd toNat_hSub toNat_hMul toNat_hDiv toNat_hMod toNat_ofNat'
  lt_iff_toNat_lt le_iff_toNat_le gcd lcm toNat_gcd toNat_lcm)

/-- The `MPN.Nat` of a natural number. -/
public abbrev ofNat (n : _root_.Nat) : MPN.Nat := GNat.ofNat n

/-- The number that a string of decimal digits denotes, like `String.toNat?`. -/
public abbrev ofString? (s : String) : Option MPN.Nat := GNat.ofString? s

@[simp] public theorem toNat_ofLimbs (a : UInt64Array) (h : Limbs64.isTrim a = true) :
    (ofLimbs a h : MPN.Nat).toNat = a.toNat := GNat.toNat_ofLimbs a h

/-- `⌊√n⌋`: on words by `Nat.sqrt`, and above by Zimmermann's recursion (`sqrtRem`). -/
public def sqrt (n : MPN.Nat) : MPN.Nat :=
  match n with
  | small _ => sqrtNewton n
  | large a _ =>
    if fits (2 * a.size + 41) then ofLimbs (Limbs64.norm (sqrtRem a).1) (Limbs64.isTrim_norm _)
    else sqrtNewton n

@[simp] public theorem toNat_sqrt (n : MPN.Nat) : (sqrt n).toNat = _root_.Nat.sqrt n.toNat := by
  unfold sqrt
  split
  · exact toNat_sqrtNewton _
  · split
    · rename_i a ha h
      rw [toNat_ofLimbs, Limbs64.toNat_norm, (toNat_sqrtRem a (by have := lt_of_fits h; lia)).1]
      rfl
    · exact toNat_sqrtNewton _

end Nat

/-- `Nat.gcd x.toNat y.toNat`, by `GNat.gcdWith`: half-gcd from `half` limbs of the smaller. -/
public def gcdWith (half : _root_.Nat) (x y : UInt64Array) : UInt64Array :=
  (GNat.gcdWith half (Limbs64.toGNat x) (Limbs64.toGNat y)).limbs

public theorem toNat_gcdWith (half : _root_.Nat) (x y : UInt64Array) :
    (gcdWith half x y).toNat = _root_.Nat.gcd x.toNat y.toNat := by
  rw [gcdWith]
  show natLimbs64.val _ = _
  rw [GNat.val_limbs, GNat.toNat_gcdWith, Limbs64.toNat_toGNat, Limbs64.toNat_toGNat]

/-- `Nat.gcd a.toNat b.toNat`. -/
public def Num.gcd (a b : UInt64Array) : UInt64Array := gcdWith config.gcdHalf a b

@[simp] public theorem Num.toNat_gcd (a b : UInt64Array) :
    (Num.gcd a b).toNat = _root_.Nat.gcd a.toNat b.toNat :=
  toNat_gcdWith ..

end MPN
