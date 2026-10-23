/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import MPN.Linear
public import MPN.Mul.Karatsuba
public import MPN.Sqr.Karatsuba

/-!
# Toom multiplication

Splitting the operands into pieces of `k` limbs makes them the values at `x = 2^(64 k)` of
polynomials with the pieces as coefficients, and `a * b` the value at `x` of the product
polynomial. Its coefficients come from its values at a few points, each a product of about `k`
limbs, which `mulToom` computes recursively.

The points are `0, 1, 2, …, ∞`, natural numbers, as on `main`: since the coefficients of the
product are natural numbers, so is every intermediate value of the interpolation: each
subtraction takes away a part of the value it subtracts from, and each division by `2` or `3` is
exact. GMP uses `-1` and `-2`,
which makes the evaluations smaller but some intermediate values negative.

* Toom-3 (`3 × 3` pieces, degree 4): the points `0, 1, 2, 3, ∞`, five products;
* Toom-3 by 2 (`3 × 2` pieces, degree 3): the points `0, 1, 2, ∞`, four products;
* Toom-4 by 2 (`4 × 2` pieces, degree 4): the points `0, 1, 2, 3, ∞`, five products, with the
  interpolation of Toom-3.

`mulToom r a b` chooses by the sizes, and is `mulKaratsuba` below `toom3Threshold` limbs.
-/

open ScalarArray UInt64Array

namespace MPN

/-- The size of the smaller operand from which `mulToom` uses the Toom methods. -/
public def toom3Threshold : USize := 384

/-- The size of the smaller operand from which `mulToom` uses Toom-4 and Toom-4 by 3. -/
public def toom4Threshold : Nat := 600

/-! ## Building blocks -/

/-- The step of `zeroInto`. -/
@[inline, expose] public def zeroStep (n : USize) (j : USize) (_h : j < n) (_x c : UInt64) :
    UInt64 × UInt64 :=
  (0, c)

/-- Clears the limbs of `r`. -/
public def zeroInto (r : USlice) : UInt64Array :=
  foldUInPlaceThen r.size (zeroStep r.size) r.array r.start
    (r.loopBound (USize.le_iff_toNat_le.2 (Nat.le_refl _))) 0 0 fun arr _ _ => arr

/-- `x₀ + j x₁ + j² x₂`, in a new array of `len` limbs. -/
public def eval3 (x₀ x₁ x₂ : USlice) (len : USize) (j : UInt64) : UInt64Array :=
  let e := (addInto (UInt64Array.replicate len.toNat 0).toUSlice x₀).1
  let e := (addMulInto e.toUSlice x₁ j).1
  (addMulInto e.toUSlice x₂ (j * j)).1

/-- `x₀ + j x₁ + j² x₂ + j³ x₃`, in a new array of `len` limbs. -/
public def eval4 (x₀ x₁ x₂ x₃ : USlice) (len : USize) (j : UInt64) : UInt64Array :=
  let e := eval3 x₀ x₁ x₂ len j
  (addMulInto e.toUSlice x₃ (j * j * j)).1

/-- `x₀ + j x₁`, in a new array of `len` limbs. -/
public def eval2 (x₀ x₁ : USlice) (len : USize) (j : UInt64) : UInt64Array :=
  let e := (addInto (UInt64Array.replicate len.toNat 0).toUSlice x₀).1
  (addMulInto e.toUSlice x₁ j).1

/-! ### Their specifications -/

private theorem zero_spec (n : USize) (arr : UInt64Array) (rs : USize) (hr : LoopBound arr rs n)
    (j : USize) (c : UInt64) :
    (foldUInPlace n (zeroStep n) arr rs hr j c).1.size = arr.size ∧
      (∀ i, (i < rs.toNat + j.toNat ∨ rs.toNat + n.toNat ≤ i) →
        (foldUInPlace n (zeroStep n) arr rs hr j c).1[i]! = arr[i]!) ∧
      (foldUInPlace n (zeroStep n) arr rs hr j c).1.valAt (rs.toNat + j.toNat)
        (n.toNat - j.toNat) = 0 := by
  induction arr, hr, j, c using foldUInPlace.induct n (zeroStep n) rs with
  | case1 arr hr j c h p ih =>
    rw [foldUInPlace_lt _ _ _ _ _ _ _ h]
    have hj := USize.lt_iff_toNat_lt.1 h
    have hj₁ := USize.toNat_add_one_of_lt h
    have hidx := hr.toNat_add h
    obtain ⟨ih₁, ih₂, ih₃⟩ := ih
    simp only [p] at ih₁ ih₂ ih₃
    rw [hj₁] at ih₂ ih₃
    simp only [UInt64Array.size_uset] at ih₁
    have hv := ih₂ (rs.toNat + j.toNat) (.inl (by lia))
    rw [getElem!_uset, hidx] at hv
    simp only [↓reduceIte] at hv
    refine ⟨ih₁, fun i hi => ?_, ?_⟩
    · rw [ih₂ i (by lia), getElem!_uset]
      simp only [hidx]
      split <;> lia
    · obtain ⟨k, hk⟩ : ∃ k, n.toNat - j.toNat = k + 1 := ⟨n.toNat - j.toNat - 1, by lia⟩
      rw [show n.toNat - (j.toNat + 1) = k by lia, ← Nat.add_assoc] at ih₃
      rw [hk, UInt64Array.valAt_succ, hv, ih₃]
      rfl
  | case2 arr hr j c h =>
    rw [foldUInPlace_ge _ _ _ _ _ _ _ h]
    have : n.toNat - j.toNat = 0 := by have := USize.lt_iff_toNat_lt (a := j) (b := n); lia
    simp [this]

public theorem zeroInto_spec (r : USlice) :
    (zeroInto r).size = r.array.size ∧
      (∀ i, (i < r.start.toNat ∨ r.start.toNat + r.size.toNat ≤ i) →
        (zeroInto r)[i]! = r.array[i]!) ∧
      (zeroInto r).valAt r.start.toNat r.size.toNat = 0 := by
  rw [zeroInto, foldUInPlaceThen_eq]
  have := zero_spec r.size r.array r.start
    (r.loopBound (USize.le_iff_toNat_le.2 (Nat.le_refl _))) 0 0
  simp only [USize.toNat_zero, Nat.add_zero, Nat.sub_zero] at this
  exact this

public theorem valAt_replicate_zero (n lo m : Nat) :
    (UInt64Array.replicate n 0).valAt lo m = 0 := by
  induction m generalizing lo with
  | zero => simp
  | succ m ih =>
    rw [valAt_succ, ih]
    rw [getElem!_eq_getElem!_data, data_replicate]
    by_cases h : lo < n
    · simp [h]
    · simp [h]; rfl

/-- The zero array of `len` limbs, as a slice. -/
private theorem zeros (len : USize) :
    (UInt64Array.replicate len.toNat 0).toUSlice.start.toNat = 0 ∧
      (UInt64Array.replicate len.toNat 0).toUSlice.size = len ∧
      (UInt64Array.replicate len.toNat 0).toUSlice.array.valAt 0 len.toNat = 0 ∧
      (UInt64Array.replicate len.toNat 0).size = len.toNat := by
  have hs : (UInt64Array.replicate len.toNat 0).size = len.toNat := by simp
  refine ⟨by simp, ?_, valAt_replicate_zero .., hs⟩
  apply USize.toNat_inj.1
  rw [size_toUSlice _ (by rw [hs]; exact len.toNat_lt_size), hs]

private theorem eval_bound {x : USlice} {len : USize} (h : x.size ≤ len) {e : UInt64Array}
    (he : e.size = len.toNat) : x.size ≤ e.toUSlice.size := by
  rw [USize.le_iff_toNat_le, size_toUSlice _ (by rw [he]; exact len.toNat_lt_size), he]
  exact USize.le_iff_toNat_le.1 h

private theorem eval3_spec (x₀ x₁ x₂ : USlice) (len : USize) (j : UInt64)
    (h₀ : x₀.size ≤ len) (h₁ : x₁.size ≤ len) (h₂ : x₂.size ≤ len) (hj : j.toNat < 2 ^ 32)
    (hlt : x₀.toNat + x₁.toNat * j.toNat + x₂.toNat * (j.toNat * j.toNat) < 2 ^ (64 * len.toNat)) :
    (eval3 x₀ x₁ x₂ len j).size = len.toNat ∧
      (eval3 x₀ x₁ x₂ len j).valAt 0 len.toNat =
        x₀.toNat + x₁.toNat * j.toNat + x₂.toNat * (j.toNat * j.toNat) := by
  dsimp only [eval3]
  obtain ⟨z₁, z₂, z₃, z₄⟩ := zeros len
  have hjj : (j * j).toNat = j.toNat * j.toNat := by
    rw [UInt64.toNat_mul, Nat.mod_eq_of_lt (by
      have := Nat.mul_lt_mul_of_lt_of_lt hj hj; lia)]
  have e₁ := addInto_exact (UInt64Array.replicate len.toNat 0).toUSlice x₀ (by rw [z₂]; exact h₀)
    (by rw [z₁, z₂, z₃]; lia)
  rw [z₁, z₂, z₃, Nat.zero_add] at e₁
  have s₁ : (addInto (UInt64Array.replicate len.toNat 0).toUSlice x₀).1.size = len.toNat := by
    rw [size_addInto]; exact z₄
  generalize addInto (UInt64Array.replicate len.toNat 0).toUSlice x₀ 0 = p₁ at *
  have hs₁ := size_toUSlice p₁.1 (by rw [s₁]; exact len.toNat_lt_size)
  rw [s₁] at hs₁
  have e₂ := addMulInto_exact p₁.1.toUSlice x₁ j (eval_bound h₁ s₁)
    (by simp only [start_toUSlice, USize.toNat_zero, array_toUSlice, hs₁, e₁]; lia)
  simp only [start_toUSlice, USize.toNat_zero, array_toUSlice, hs₁, e₁] at e₂
  have s₂ : (addMulInto p₁.1.toUSlice x₁ j).1.size = len.toNat := by
    rw [size_addMulInto, array_toUSlice, s₁]
  generalize addMulInto p₁.1.toUSlice x₁ j = p₂ at *
  have hs₂ := size_toUSlice p₂.1 (by rw [s₂]; exact len.toNat_lt_size)
  rw [s₂] at hs₂
  have e₃ := addMulInto_exact p₂.1.toUSlice x₂ (j * j) (eval_bound h₂ s₂)
    (by simp only [start_toUSlice, USize.toNat_zero, array_toUSlice, hs₂, e₂, hjj]; lia)
  simp only [start_toUSlice, USize.toNat_zero, array_toUSlice, hs₂, e₂, hjj] at e₃
  exact ⟨by rw [size_addMulInto, array_toUSlice, s₂], e₃⟩

private theorem eval2_spec (x₀ x₁ : USlice) (len : USize) (j : UInt64)
    (h₀ : x₀.size ≤ len) (h₁ : x₁.size ≤ len)
    (hlt : x₀.toNat + x₁.toNat * j.toNat < 2 ^ (64 * len.toNat)) :
    (eval2 x₀ x₁ len j).size = len.toNat ∧
      (eval2 x₀ x₁ len j).valAt 0 len.toNat = x₀.toNat + x₁.toNat * j.toNat := by
  dsimp only [eval2]
  obtain ⟨z₁, z₂, z₃, z₄⟩ := zeros len
  have e₁ := addInto_exact (UInt64Array.replicate len.toNat 0).toUSlice x₀ (by rw [z₂]; exact h₀)
    (by rw [z₁, z₂, z₃]; lia)
  rw [z₁, z₂, z₃, Nat.zero_add] at e₁
  have s₁ : (addInto (UInt64Array.replicate len.toNat 0).toUSlice x₀).1.size = len.toNat := by
    rw [size_addInto]; exact z₄
  generalize addInto (UInt64Array.replicate len.toNat 0).toUSlice x₀ 0 = p₁ at *
  have hs₁ := size_toUSlice p₁.1 (by rw [s₁]; exact len.toNat_lt_size)
  rw [s₁] at hs₁
  have e₂ := addMulInto_exact p₁.1.toUSlice x₁ j (eval_bound h₁ s₁)
    (by simp only [start_toUSlice, USize.toNat_zero, array_toUSlice, hs₁, e₁]; lia)
  simp only [start_toUSlice, USize.toNat_zero, array_toUSlice, hs₁, e₁] at e₂
  exact ⟨by rw [size_addMulInto, array_toUSlice, s₁], e₂⟩

private theorem eval4_spec (x₀ x₁ x₂ x₃ : USlice) (len : USize) (j : UInt64)
    (h₀ : x₀.size ≤ len) (h₁ : x₁.size ≤ len) (h₂ : x₂.size ≤ len) (h₃ : x₃.size ≤ len)
    (hj : j.toNat < 2 ^ 16)
    (hlt : x₀.toNat + x₁.toNat * j.toNat + x₂.toNat * (j.toNat * j.toNat) +
      x₃.toNat * (j.toNat * j.toNat * j.toNat) < 2 ^ (64 * len.toNat)) :
    (eval4 x₀ x₁ x₂ x₃ len j).size = len.toNat ∧
      (eval4 x₀ x₁ x₂ x₃ len j).valAt 0 len.toNat =
        x₀.toNat + x₁.toNat * j.toNat + x₂.toNat * (j.toNat * j.toNat) +
          x₃.toNat * (j.toNat * j.toNat * j.toNat) := by
  dsimp only [eval4]
  obtain ⟨s₃, e₃⟩ := eval3_spec x₀ x₁ x₂ len j h₀ h₁ h₂ (by lia) (by lia)
  have hjjj : (j * j * j).toNat = j.toNat * j.toNat * j.toNat := by
    have h2 := Nat.mul_lt_mul_of_lt_of_lt hj hj
    have h3 := Nat.mul_lt_mul_of_lt_of_lt h2 hj
    rw [UInt64.toNat_mul, UInt64.toNat_mul, Nat.mod_eq_of_lt (a := j.toNat * j.toNat) (by lia),
      Nat.mod_eq_of_lt (by lia)]
  generalize eval3 x₀ x₁ x₂ len j = e at *
  have hs := size_toUSlice e (by rw [s₃]; exact len.toNat_lt_size)
  rw [s₃] at hs
  have e₄ := addMulInto_exact e.toUSlice x₃ (j * j * j) (eval_bound h₃ s₃)
    (by simp only [start_toUSlice, USize.toNat_zero, array_toUSlice, hs, e₃, hjjj]; lia)
  simp only [start_toUSlice, USize.toNat_zero, array_toUSlice, hs, e₃, hjjj] at e₄
  exact ⟨by rw [size_addMulInto, array_toUSlice, s₃], e₄⟩

/-! ### Steps on arrays of `L` limbs -/

section Steps

variable {L : Nat} (hL : L < USize.size)
include hL

private theorem whole (w : UInt64Array) (hw : w.size = L) :
    w.toUSlice.start.toNat = 0 ∧ w.toUSlice.size.toNat = L ∧ w.toUSlice.array = w := by
  refine ⟨by simp, by rw [size_toUSlice _ (by rw [hw]; exact hL), hw], rfl⟩

private theorem tail (w : UInt64Array) (hw : w.size = L) (h₁ : 1 ≤ L) :
    (w.toUSlice.slice 1 w.usize).array = w ∧ (w.toUSlice.slice 1 w.usize).start.toNat = 1 ∧
      (w.toUSlice.slice 1 w.usize).size.toNat = L - 1 ∧
      (w.toUSlice.slice 1 w.usize).toNat = w.valAt 1 (L - 1) := by
  have hu := toNat_usize w (by rw [hw]; exact hL)
  have := toUSlice_slice w (i := 1) (j := w.usize) (by rw [USize.toNat_one, hu, hw]; exact h₁)
    (by rw [hu]; exact Nat.le_refl _) (by rw [hw]; exact hL)
  rw [USize.toNat_one, hu, hw] at this
  exact this

private theorem low (w : UInt64Array) (hw : w.size = L) (h₁ : 1 ≤ L) (v : UInt64Array)
    (hv : v.size = L) :
    (w.toUSlice.slice 0 (v.usize - 1)).size.toNat = L - 1 ∧
      (w.toUSlice.slice 0 (v.usize - 1)).toNat = w.valAt 0 (L - 1) := by
  have hu := toNat_usize v (by rw [hv]; exact hL)
  have h1 : (v.usize - 1).toNat = L - 1 := by
    rw [USize.toNat_sub_of_le _ _ (USize.le_iff_toNat_le.2 (by rw [hu, USize.toNat_one]; lia)), hu,
      hv, USize.toNat_one]
  have := toUSlice_slice w (i := 0) (j := v.usize - 1) (by rw [USize.toNat_zero]; lia)
    (by rw [h1, hw]; lia) (by rw [hw]; exact hL)
  rw [USize.toNat_zero, h1, Nat.sub_zero] at this
  exact ⟨this.2.2.1, this.2.2.2⟩

/-- Subtracting from all of `w`. -/
private theorem sub_whole (w : UInt64Array) (hw : w.size = L) (b : USlice) (hb : b.size.toNat ≤ L)
    (hle : b.toNat ≤ w.valAt 0 L) :
    (subInto w.toUSlice b).1.size = L ∧
      (subInto w.toUSlice b).1.valAt 0 L = w.valAt 0 L - b.toNat := by
  obtain ⟨h₁, h₂, h₃⟩ := whole hL w hw
  have := subInto_exact w.toUSlice b (USize.le_iff_toNat_le.2 (by rw [h₂]; exact hb))
    (by rw [h₁, h₂, h₃]; exact hle)
  rw [h₁, h₂, h₃] at this
  exact ⟨by rw [size_subInto, h₃, hw], this⟩

/-- Subtracting a multiple from all of `w`. -/
private theorem subMul_whole (w : UInt64Array) (hw : w.size = L) (b : USlice) (x : UInt64)
    (hb : b.size.toNat ≤ L) (hle : b.toNat * x.toNat ≤ w.valAt 0 L) :
    (subMulInto w.toUSlice b x).1.size = L ∧
      (subMulInto w.toUSlice b x).1.valAt 0 L = w.valAt 0 L - b.toNat * x.toNat := by
  obtain ⟨h₁, h₂, h₃⟩ := whole hL w hw
  have := subMulInto_exact w.toUSlice b x (USize.le_iff_toNat_le.2 (by rw [h₂]; exact hb))
    (by rw [h₁, h₂, h₃]; exact hle)
  rw [h₁, h₂, h₃] at this
  exact ⟨by rw [size_subMulInto, h₃, hw], this⟩

/-- Subtracting from the limbs of `w` from the second on. -/
private theorem sub_tail (w : UInt64Array) (hw : w.size = L) (h₁ : 1 ≤ L) (b : USlice)
    (hb : b.size.toNat ≤ L - 1) (hle : b.toNat ≤ w.valAt 1 (L - 1)) :
    (subInto (w.toUSlice.slice 1 w.usize) b).1.size = L ∧
      (subInto (w.toUSlice.slice 1 w.usize) b).1.valAt 1 (L - 1) = w.valAt 1 (L - 1) - b.toNat := by
  obtain ⟨t₁, t₂, t₃, t₄⟩ := tail hL w hw h₁
  have := subInto_exact (w.toUSlice.slice 1 w.usize) b
    (USize.le_iff_toNat_le.2 (by rw [t₃]; exact hb))
    (by rw [t₁, t₂, t₃]; exact hle)
  rw [t₁, t₂, t₃] at this
  exact ⟨by rw [size_subInto, t₁, hw], this⟩

/-- Subtracting a multiple from the limbs of `w` from the second on. -/
private theorem subMul_tail (w : UInt64Array) (hw : w.size = L) (h₁ : 1 ≤ L) (b : USlice)
    (x : UInt64) (hb : b.size.toNat ≤ L - 1) (hle : b.toNat * x.toNat ≤ w.valAt 1 (L - 1)) :
    (subMulInto (w.toUSlice.slice 1 w.usize) b x).1.size = L ∧
      (subMulInto (w.toUSlice.slice 1 w.usize) b x).1.valAt 1 (L - 1) =
        w.valAt 1 (L - 1) - b.toNat * x.toNat := by
  obtain ⟨t₁, t₂, t₃, t₄⟩ := tail hL w hw h₁
  have := subMulInto_exact (w.toUSlice.slice 1 w.usize) b x
    (USize.le_iff_toNat_le.2 (by rw [t₃]; exact hb)) (by rw [t₁, t₂, t₃]; exact hle)
  rw [t₁, t₂, t₃] at this
  exact ⟨by rw [size_subMulInto, t₁, hw], this⟩

/-- Halving all of `w` into its limbs from the second on. -/
private theorem half_whole (w : UInt64Array) (hw : w.size = L) (h₁ : 1 ≤ L)
    (heven : w.valAt 0 L % 2 = 0) (hlt : w.valAt 0 L < 2 ^ (64 * (L - 1))) :
    (shl63Into w.toUSlice).1.size = L ∧
      (shl63Into w.toUSlice).1.valAt 1 (L - 1) = w.valAt 0 L / 2 := by
  obtain ⟨h₁', h₂, h₃⟩ := whole hL w hw
  have := valAt_shl63Into_half w.toUSlice (by rw [h₂]; lia) (by rw [h₁', h₂, h₃]; exact heven)
    (by rw [h₁', h₂, h₃]; exact hlt)
  rw [h₁', h₂, h₃] at this
  exact ⟨by rw [size_shl63Into, h₃, hw], this⟩

/-- Dividing all of `w` by `3`. -/
private theorem div3_whole (w : UInt64Array) (hw : w.size = L) (h3 : w.valAt 0 L % 3 = 0) :
    (divExact3Into w.toUSlice).1.size = L ∧
      (divExact3Into w.toUSlice).1.valAt 0 L = w.valAt 0 L / 3 := by
  obtain ⟨h₁, h₂, h₃⟩ := whole hL w hw
  have := valAt_divExact3Into w.toUSlice (by rw [h₁, h₂, h₃]; exact h3)
  rw [h₁, h₂, h₃] at this
  exact ⟨by rw [size_divExact3Into, h₃, hw], this⟩

/-- Dividing all of `w` by `5`. -/
private theorem div5_whole (w : UInt64Array) (hw : w.size = L) (h5 : w.valAt 0 L % 5 = 0) :
    (divExact5Into w.toUSlice).1.size = L ∧
      (divExact5Into w.toUSlice).1.valAt 0 L = w.valAt 0 L / 5 := by
  obtain ⟨h₁, h₂, h₃⟩ := whole hL w hw
  have := valAt_divExact5Into w.toUSlice (by rw [h₁, h₂, h₃]; exact h5)
  rw [h₁, h₂, h₃] at this
  exact ⟨by rw [size_divExact5Into, h₃, hw], this⟩

/-- Shifting all of `w` right by `s` bits, `0 < s < 64`. -/
private theorem shr_whole (w : UInt64Array) (hw : w.size = L) (s : UInt64) (hs₀ : 0 < s.toNat)
    (hs : s.toNat < 64) :
    (rshiftInto w.toUSlice s).size = L ∧
      (rshiftInto w.toUSlice s).valAt 0 L = w.valAt 0 L / 2 ^ s.toNat := by
  obtain ⟨h₁, h₂, h₃⟩ := whole hL w hw
  have := valAt_rshiftInto w.toUSlice s hs₀ hs
  rw [h₁, h₂, h₃] at this
  exact ⟨by rw [size_rshiftInto, h₃, hw], this⟩

/-! #### By values

The interpolation steps of Toom-4 as equations on values: each takes the value `W` of `w` and gives
the value `R` of the result from an equation `W = … + R`, so that a chain of them needs no
subtraction or division on `Nat`.
-/

private theorem subSl (w : UInt64Array) (hw : w.size = L) (b : USlice) (hb : b.size.toNat ≤ L)
    {W B R : Nat} (hW : w.valAt 0 L = W) (hB : b.toNat = B) (h : W = B + R) :
    (subInto w.toUSlice b).1.size = L ∧ (subInto w.toUSlice b).1.valAt 0 L = R := by
  obtain ⟨s₁, s₂⟩ := sub_whole hL w hw b hb (by lia)
  exact ⟨s₁, by rw [s₂]; lia⟩

private theorem subMulSl (w : UInt64Array) (hw : w.size = L) (b : USlice) (hb : b.size.toNat ≤ L)
    (x : UInt64) {W B X R : Nat} (hW : w.valAt 0 L = W) (hB : b.toNat = B) (hx : x.toNat = X)
    (h : W = B * X + R) :
    (subMulInto w.toUSlice b x).1.size = L ∧ (subMulInto w.toUSlice b x).1.valAt 0 L = R := by
  obtain ⟨s₁, s₂⟩ := subMul_whole hL w hw b x hb (by rw [hB, hx]; lia)
  exact ⟨s₁, by rw [s₂, hB, hx]; lia⟩

private theorem subW (w b : UInt64Array) (hw : w.size = L) (hb : b.size = L) {W B R : Nat}
    (hW : w.valAt 0 L = W) (hB : b.valAt 0 L = B) (h : W = B + R) :
    (subInto w.toUSlice b.toUSlice).1.size = L ∧
      (subInto w.toUSlice b.toUSlice).1.valAt 0 L = R := by
  obtain ⟨b₁, b₂, b₃⟩ := whole hL b hb
  refine subSl hL w hw b.toUSlice (by rw [b₂]; exact Nat.le_refl _) hW ?_ h
  rw [USlice.toNat_eq_valAt, b₁, b₂, b₃, hB]

private theorem subMulW (w b : UInt64Array) (hw : w.size = L) (hb : b.size = L) (x : UInt64)
    {W B X R : Nat} (hW : w.valAt 0 L = W) (hB : b.valAt 0 L = B) (hx : x.toNat = X)
    (h : W = B * X + R) :
    (subMulInto w.toUSlice b.toUSlice x).1.size = L ∧
      (subMulInto w.toUSlice b.toUSlice x).1.valAt 0 L = R := by
  obtain ⟨b₁, b₂, b₃⟩ := whole hL b hb
  refine subMulSl hL w hw b.toUSlice (by rw [b₂]; exact Nat.le_refl _) x hW ?_ hx h
  rw [USlice.toNat_eq_valAt, b₁, b₂, b₃, hB]

private theorem shrW (w : UInt64Array) (hw : w.size = L) (s : UInt64) (hs₀ : 0 < s.toNat)
    (hs : s.toNat < 64) {S W R : Nat} (hS : s.toNat = S) (hW : w.valAt 0 L = W)
    (h : W = 2 ^ S * R) :
    (rshiftInto w.toUSlice s).size = L ∧ (rshiftInto w.toUSlice s).valAt 0 L = R := by
  obtain ⟨s₁, s₂⟩ := shr_whole hL w hw s hs₀ hs
  exact ⟨s₁, by rw [s₂, hW, h, hS, Nat.mul_div_cancel_left _ (Nat.two_pow_pos _)]⟩

private theorem div3W (w : UInt64Array) (hw : w.size = L) {W R : Nat} (hW : w.valAt 0 L = W)
    (h : W = 3 * R) :
    (divExact3Into w.toUSlice).1.size = L ∧ (divExact3Into w.toUSlice).1.valAt 0 L = R := by
  obtain ⟨s₁, s₂⟩ := div3_whole hL w hw (by rw [hW, h]; simp)
  exact ⟨s₁, by rw [s₂, hW, h]; lia⟩

private theorem div5W (w : UInt64Array) (hw : w.size = L) {W R : Nat} (hW : w.valAt 0 L = W)
    (h : W = 5 * R) :
    (divExact5Into w.toUSlice).1.size = L ∧ (divExact5Into w.toUSlice).1.valAt 0 L = R := by
  obtain ⟨s₁, s₂⟩ := div5_whole hL w hw (by rw [hW, h]; simp)
  exact ⟨s₁, by rw [s₂, hW, h]; lia⟩

end Steps

/-! ### The recombination -/

/-- A window of the limbs of `r` in `arr`, an array of the same size. -/
private theorem window (arr : UInt64Array) (r : USlice) (h : arr.size = r.array.size) {i j : USize}
    (hij : i.toNat ≤ j.toNat) (hj : j.toNat ≤ r.size.toNat) :
    ((arr.uslice r.start r.stop).slice i j).array = arr ∧
      ((arr.uslice r.start r.stop).slice i j).start.toNat = r.start.toNat + i.toNat ∧
      ((arr.uslice r.start r.stop).slice i j).size.toNat = j.toNat - i.toNat ∧
      ((arr.uslice r.start r.stop).slice i j).toNat =
        arr.valAt (r.start.toNat + i.toNat) (j.toNat - i.toNat) := by
  obtain ⟨u₁, u₂, u₃⟩ := uslice_same r arr h
  have hsz : (arr.uslice r.start r.stop).size.toNat = r.size.toNat := by rw [u₂]
  refine ⟨by rw [USlice.array_slice, u₃], ?_, ?_, ?_⟩
  · rw [USlice.start_slice _ hij (by rw [hsz]; exact hj), u₁]
  · exact USlice.size_slice _ hij (by rw [hsz]; exact hj)
  · rw [USlice.toNat_slice _ hij (by rw [hsz]; exact hj), u₁, u₃]

/-- Adding `C` to the limbs of `r` from `off` to `n`: `C 2^(64 off)` to their value. -/
private theorem add_at (arr : UInt64Array) (r : USlice) (h : arr.size = r.array.size)
    (n off : USize)
    (hn : n.toNat ≤ r.size.toNat) (hoff : off.toNat ≤ n.toNat) (C : USlice)
    (hC : C.size.toNat ≤ n.toNat - off.toNat)
    (hlt : arr.valAt r.start.toNat n.toNat + 2 ^ (64 * off.toNat) * C.toNat <
      2 ^ (64 * n.toNat)) :
    (addInto ((arr.uslice r.start r.stop).slice off n) C).1.size = r.array.size ∧
      (∀ i, (i < r.start.toNat + off.toNat ∨ r.start.toNat + n.toNat ≤ i) →
        (addInto ((arr.uslice r.start r.stop).slice off n) C).1[i]! = arr[i]!) ∧
      (addInto ((arr.uslice r.start r.stop).slice off n) C).1.valAt r.start.toNat n.toNat =
        arr.valAt r.start.toNat n.toNat + 2 ^ (64 * off.toNat) * C.toNat := by
  obtain ⟨w₁, w₂, w₃, w₄⟩ := window arr r h hoff hn
  have hsplit : ∀ a : UInt64Array, a.valAt r.start.toNat n.toNat =
      a.valAt r.start.toNat off.toNat +
        2 ^ (64 * off.toNat) * a.valAt (r.start.toNat + off.toNat) (n.toNat - off.toNat) := by
    intro a
    rw [← UInt64Array.valAt_add, show off.toNat + (n.toNat - off.toNat) = n.toNat by lia]
  have hP : 2 ^ (64 * n.toNat) = 2 ^ (64 * off.toNat) * 2 ^ (64 * (n.toNat - off.toNat)) := by
    rw [← Nat.pow_add]; congr 1; lia
  have he := addInto_exact ((arr.uslice r.start r.stop).slice off n) C
    (USize.le_iff_toNat_le.2 (by rw [w₃]; exact hC)) (by
      rw [w₁, w₂, w₃]
      rw [hsplit, hP] at hlt
      have : 0 < 2 ^ (64 * off.toNat) := Nat.two_pow_pos _
      refine Nat.lt_of_mul_lt_mul_left (a := 2 ^ (64 * off.toNat)) ?_
      generalize arr.valAt _ off.toNat = L₀ at *
      generalize 2 ^ (64 * off.toNat) = P at *
      rw [Nat.mul_add]
      lia)
  rw [w₁, w₂, w₃] at he
  have hu := getElem!_addInto ((arr.uslice r.start r.stop).slice off n) C 0
  rw [w₁, w₂, w₃] at hu
  refine ⟨by rw [size_addInto, w₁, h], fun i hi => hu i (by lia), ?_⟩
  rw [hsplit, hsplit arr, he, UInt64Array.valAt_congr (b := arr) _ fun i _ hi => hu i (by lia),
    Nat.mul_add, Nat.add_assoc]

/-- Clearing the limbs of `r` from `i` to `j`. -/
private theorem zero_at (arr : UInt64Array) (r : USlice) (h : arr.size = r.array.size)
    (n i j : USize) (hn : n.toNat ≤ r.size.toNat) (hij : i.toNat ≤ j.toNat)
    (hj : j.toNat ≤ n.toNat) :
    (zeroInto ((arr.uslice r.start r.stop).slice i j)).size = r.array.size ∧
      (∀ t, (t < r.start.toNat + i.toNat ∨ r.start.toNat + j.toNat ≤ t) →
        (zeroInto ((arr.uslice r.start r.stop).slice i j))[t]! = arr[t]!) ∧
      (zeroInto ((arr.uslice r.start r.stop).slice i j)).valAt r.start.toNat n.toNat =
        arr.valAt r.start.toNat i.toNat +
          2 ^ (64 * j.toNat) * arr.valAt (r.start.toNat + j.toNat) (n.toNat - j.toNat) := by
  obtain ⟨w₁, w₂, w₃, w₄⟩ := window arr r h hij (by lia)
  obtain ⟨z₁, z₂, z₃⟩ := zeroInto_spec ((arr.uslice r.start r.stop).slice i j)
  rw [w₁, w₂, w₃] at z₂
  rw [w₂, w₃] at z₃
  rw [w₁] at z₁
  refine ⟨by rw [z₁, h], fun t ht => z₂ t (by lia), ?_⟩
  have hsplit := UInt64Array.valAt_add (zeroInto ((arr.uslice r.start r.stop).slice i j))
    r.start.toNat i.toNat (j.toNat - i.toNat)
  have hsplit' := UInt64Array.valAt_add (zeroInto ((arr.uslice r.start r.stop).slice i j))
    r.start.toNat j.toNat (n.toNat - j.toNat)
  rw [show i.toNat + (j.toNat - i.toNat) = j.toNat by lia, z₃, Nat.mul_zero, Nat.add_zero]
    at hsplit
  rw [show j.toNat + (n.toNat - j.toNat) = n.toNat by lia, hsplit] at hsplit'
  rw [hsplit', UInt64Array.valAt_congr (b := arr) (lo := r.start.toNat) i.toNat
      fun t _ ht => z₂ t (by lia),
    UInt64Array.valAt_congr (b := arr) (lo := r.start.toNat + j.toNat) (n.toNat - j.toNat)
      fun t ht _ => z₂ t (by lia)]

/-! ## Interpolation -/

/--
The interpolation and recombination of degree 4, from the points `0, 1, 2, 3, ∞`: `arr` holds
`c₀` in limbs `[r.start, r.start + 2 k)` and `c₄` from limb `r.start + 4 k` to `r.start + n`,
and `w₁`, `w₂`, `w₃` are the values at `1, 2, 3`, of `len` limbs each. Writes
`c₀ + c₁ x + c₂ x² + c₃ x³ + c₄ x⁴` into the `n` limbs from `r.start`.
-/
public def interp4 (arr : UInt64Array) (r : USlice) (n k : USize) (w₁ w₂ w₃ : UInt64Array) :
    UInt64Array :=
  let R := arr.uslice r.start r.stop
  let X₀ := R.slice 0 (k + k)
  let X₄ := R.slice (4 * k) n
  let w₁ := (subInto w₁.toUSlice X₀).1
  let w₁ := (subInto w₁.toUSlice X₄).1
  let w₂ := (subInto w₂.toUSlice X₀).1
  let w₂ := (subMulInto w₂.toUSlice X₄ 16).1
  let w₂ := (shl63Into w₂.toUSlice).1
  let w₃ := (subInto w₃.toUSlice X₀).1
  let w₃ := (subMulInto w₃.toUSlice X₄ 81).1
  let w₃ := (divExact3Into w₃.toUSlice).1
  -- `t₂ = s₂ - r₁`, `t₃ = (s₃ - r₁) / 2`.
  let w₂ := (subInto (w₂.toUSlice.slice 1 w₂.usize) (w₁.toUSlice.slice 0 (w₂.usize - 1))).1
  let w₃ := (subInto w₃.toUSlice w₁.toUSlice).1
  let w₃ := (shl63Into w₃.toUSlice).1
  -- `c₃ = t₃ - t₂`, `c₂ = t₂ - 3 c₃`, `c₁ = r₁ - c₂ - c₃`.
  let w₃ := (subInto (w₃.toUSlice.slice 1 w₃.usize) (w₂.toUSlice.slice 1 w₂.usize)).1
  let w₂ := (subMulInto (w₂.toUSlice.slice 1 w₂.usize) (w₃.toUSlice.slice 1 w₃.usize) 3).1
  let w₁ := (subInto w₁.toUSlice (w₂.toUSlice.slice 1 w₂.usize)).1
  let w₁ := (subInto w₁.toUSlice (w₃.toUSlice.slice 1 w₃.usize)).1
  -- The recombination.
  let arr := zeroInto ((arr.uslice r.start r.stop).slice (k + k) (4 * k))
  let arr := (addInto ((arr.uslice r.start r.stop).slice k n)
    (w₁.toUSlice.slice 0 (min (n - k) w₁.usize))).1
  let arr := (addInto ((arr.uslice r.start r.stop).slice (k + k) n)
    (w₂.toUSlice.slice 1 (min (n - (k + k) + 1) w₂.usize))).1
  (addInto ((arr.uslice r.start r.stop).slice (3 * k) n)
    (w₃.toUSlice.slice 1 (min (n - 3 * k + 1) w₃.usize))).1

/--
The interpolation and recombination of degree 3, from the points `0, 1, 2, ∞`: `arr` holds `c₀`
in limbs `[r.start, r.start + 2 k)` and `c₃` from limb `r.start + 3 k` to `r.start + n`, and `w₁`,
`w₂` are the values at `1, 2`. Writes `c₀ + c₁ x + c₂ x² + c₃ x³` into the `n` limbs from
`r.start`.
-/
public def interp3 (arr : UInt64Array) (r : USlice) (n k : USize) (w₁ w₂ : UInt64Array) :
    UInt64Array :=
  let R := arr.uslice r.start r.stop
  let X₀ := R.slice 0 (k + k)
  let X₃ := R.slice (3 * k) n
  let w₁ := (subInto w₁.toUSlice X₀).1
  let w₁ := (subInto w₁.toUSlice X₃).1
  let w₂ := (subInto w₂.toUSlice X₀).1
  let w₂ := (subMulInto w₂.toUSlice X₃ 8).1
  let w₂ := (shl63Into w₂.toUSlice).1
  -- `c₂ = s₂ - r₁`, `c₁ = r₁ - c₂`.
  let w₂ := (subInto (w₂.toUSlice.slice 1 w₂.usize) (w₁.toUSlice.slice 0 (w₂.usize - 1))).1
  let w₁ := (subInto w₁.toUSlice (w₂.toUSlice.slice 1 w₂.usize)).1
  -- The recombination.
  let arr := zeroInto ((arr.uslice r.start r.stop).slice (k + k) (3 * k))
  let arr := (addInto ((arr.uslice r.start r.stop).slice k n)
    (w₁.toUSlice.slice 0 (min (n - k) w₁.usize))).1
  (addInto ((arr.uslice r.start r.stop).slice (k + k) n)
    (w₂.toUSlice.slice 1 (min (n - (k + k) + 1) w₂.usize))).1

/-! ### Correctness of the interpolation -/

private theorem toNat_mul_k (k : USize) (c : Nat) (hc : c < 2 ^ 32) (n : USize)
    (hk : c * k.toNat ≤ n.toNat) : ((c.toUSize) * k).toNat = c * k.toNat := by
  have : 4294967296 ≤ USize.size := by cases USize.size_eq <;> lia
  have hn := n.toNat_lt_size
  rw [USize.toNat_mul, USize.toNat_ofNat', Nat.mod_eq_of_lt (a := c) (by
    simp only [USize.size] at this; lia)]
  exact Nat.mod_eq_of_lt (by simp only [USize.size] at hn; lia)

/-- A coefficient that fits: `c < Q` when `P c ≤ x < P Q`. -/
private theorem coeff_lt {P Q c x : Nat} (_hP : 0 < P) (h : P * c ≤ x) (hx : x < P * Q) : c < Q :=
  Nat.lt_of_mul_lt_mul_left (a := P) (by lia)

/-- The low limbs of a coefficient `c` in limbs `lo` to `lo + L - 1` of `w`, when it fits. -/
private theorem coeff_slice {L : Nat} (hL : L < USize.size) (w : UInt64Array) (hw : w.size = L)
    (lo : USize) (hlo : lo.toNat ≤ 1) {j : USize} (c : Nat) (hj : lo.toNat ≤ min j.toNat L)
    (hc : w.valAt lo.toNat (L - lo.toNat) = c)
    (hlt : c < 2 ^ (64 * (min j.toNat L - lo.toNat))) :
    (w.toUSlice.slice lo (min j w.usize)).size.toNat = min j.toNat L - lo.toNat ∧
      (w.toUSlice.slice lo (min j w.usize)).toNat = c := by
  have hu := toNat_usize w (by rw [hw]; exact hL)
  have hm : (min j w.usize).toNat = min j.toNat L := by rw [USize.toNat_min, hu, hw]
  obtain ⟨-, -, h₃, h₄⟩ := toUSlice_slice w (i := lo) (j := min j w.usize)
    (by rw [hm]; exact hj) (by rw [hm, hw]; lia) (by rw [hw]; exact hL)
  rw [hm] at h₃ h₄
  refine ⟨h₃, ?_⟩
  rw [h₄, UInt64Array.valAt_mod _ _ (show min j.toNat L - lo.toNat ≤ L - lo.toNat by lia), hc]
  exact Nat.mod_eq_of_lt hlt

/--
Adding a coefficient `c`, all of `w`, to limbs `off` to `n - 1` of `r` in `arr`: only the limbs of
`w` that fit, which hold all of `c` when the sum fits.
-/
private theorem rec_step (A : UInt64Array) (r : USlice) (hA : A.size = r.array.size) (n off : USize)
    (hn : n.toNat ≤ r.size.toNat) (hoff : off.toNat ≤ n.toNat) {L : Nat} (hL : L < USize.size)
    (w : UInt64Array) (hw : w.size = L) (c : Nat) (hc : w.valAt 0 L = c)
    (hlt : A.valAt r.start.toNat n.toNat + 2 ^ (64 * off.toNat) * c < 2 ^ (64 * n.toNat)) :
    (addInto ((A.uslice r.start r.stop).slice off n)
        (w.toUSlice.slice 0 (min (n - off) w.usize))).1.size = r.array.size ∧
      (∀ i, (i < r.start.toNat + off.toNat ∨ r.start.toNat + n.toNat ≤ i) →
        (addInto ((A.uslice r.start r.stop).slice off n)
          (w.toUSlice.slice 0 (min (n - off) w.usize))).1[i]! = A[i]!) ∧
      (addInto ((A.uslice r.start r.stop).slice off n)
          (w.toUSlice.slice 0 (min (n - off) w.usize))).1.valAt r.start.toNat n.toNat =
        A.valAt r.start.toNat n.toNat + 2 ^ (64 * off.toNat) * c := by
  have hno : (n - off).toNat = n.toNat - off.toNat :=
    USize.toNat_sub_of_le _ _ (USize.le_iff_toNat_le.2 hoff)
  have hP : 2 ^ (64 * n.toNat) = 2 ^ (64 * off.toNat) * 2 ^ (64 * (n.toNat - off.toNat)) := by
    rw [← Nat.pow_add]; congr 1; lia
  have hcl : c < 2 ^ (64 * (n.toNat - off.toNat)) :=
    coeff_lt (x := A.valAt r.start.toNat n.toNat + 2 ^ (64 * off.toNat) * c) (Nat.two_pow_pos _)
      (Nat.le_add_left _ _) (by rw [← hP]; exact hlt)
  obtain ⟨C₁, C₂⟩ := coeff_slice hL w hw 0 (by simp) (j := n - off) c (by simp)
    (by rw [USize.toNat_zero, Nat.sub_zero]; exact hc) (by
      rw [hno, USize.toNat_zero, Nat.sub_zero]
      rcases Nat.le_total (n.toNat - off.toNat) L with hle | hle
      · rw [Nat.min_eq_left hle]; exact hcl
      · rw [Nat.min_eq_right hle, ← hc]; exact valAt_lt ..)
  rw [hno, USize.toNat_zero, Nat.sub_zero] at C₁
  obtain ⟨a₁, a₂, a₃⟩ := add_at A r hA n off hn hoff (w.toUSlice.slice 0 (min (n - off) w.usize))
    (by rw [C₁]; lia) (by rw [C₂]; exact hlt)
  rw [C₂] at a₃
  exact ⟨a₁, a₂, a₃⟩

private theorem interp4_spec (arr : UInt64Array) (r : USlice) (n k : USize)
    (w₁ w₂ w₃ : UInt64Array) (L c₀ c₁ c₂ c₃ c₄ : Nat)
    (h : arr.size = r.array.size) (hn : n.toNat ≤ r.size.toNat) (hk : 4 * k.toNat ≤ n.toNat)
    (hk₁ : 1 ≤ k.toNat) (hL : L < USize.size) (hL₂ : 2 ≤ L) (hw₁ : w₁.size = L) (hw₂ : w₂.size = L)
    (hw₃ : w₃.size = L) (hX₀ : 2 * k.toNat ≤ L) (hX₄ : n.toNat - 4 * k.toNat ≤ L)
    (hc₀ : arr.valAt r.start.toNat (2 * k.toNat) = c₀)
    (hc₄ : arr.valAt (r.start.toNat + 4 * k.toNat) (n.toNat - 4 * k.toNat) = c₄)
    (hv₁ : w₁.valAt 0 L = c₀ + c₁ + c₂ + c₃ + c₄)
    (hv₂ : w₂.valAt 0 L = c₀ + 2 * c₁ + 4 * c₂ + 8 * c₃ + 16 * c₄)
    (hv₃ : w₃.valAt 0 L = c₀ + 3 * c₁ + 9 * c₂ + 27 * c₃ + 81 * c₄)
    (hb : c₀ + 3 * c₁ + 9 * c₂ + 27 * c₃ + 81 * c₄ < 2 ^ (64 * (L - 1)))
    (htot : c₀ + 2 ^ (64 * k.toNat) * c₁ + 2 ^ (64 * (2 * k.toNat)) * c₂ +
      2 ^ (64 * (3 * k.toNat)) * c₃ + 2 ^ (64 * (4 * k.toNat)) * c₄ < 2 ^ (64 * n.toNat)) :
    (interp4 arr r n k w₁ w₂ w₃).size = r.array.size ∧
      (∀ i, (i < r.start.toNat ∨ r.start.toNat + n.toNat ≤ i) →
        (interp4 arr r n k w₁ w₂ w₃)[i]! = arr[i]!) ∧
      (interp4 arr r n k w₁ w₂ w₃).valAt r.start.toNat n.toNat =
        c₀ + 2 ^ (64 * k.toNat) * c₁ + 2 ^ (64 * (2 * k.toNat)) * c₂ +
          2 ^ (64 * (3 * k.toNat)) * c₃ + 2 ^ (64 * (4 * k.toNat)) * c₄ := by
  dsimp only [interp4]
  have hnS := n.toNat_lt_size
  have hkk : (k + k).toNat = 2 * k.toNat := by rw [USize.toNat_add_of_lt (by lia)]; lia
  have h4k : (4 * k).toNat = 4 * k.toNat := toNat_mul_k k 4 (by decide) n hk
  have h3k : (3 * k).toNat = 3 * k.toNat := toNat_mul_k k 3 (by decide) n (by lia)
  -- `c₀` and `c₄` in `arr`.
  obtain ⟨x₀₁, x₀₂, x₀₃, x₀₄⟩ := window arr r h (i := 0) (j := k + k) (by simp) (by rw [hkk]; lia)
  obtain ⟨x₄₁, x₄₂, x₄₃, x₄₄⟩ := window arr r h (i := 4 * k) (j := n) (by rw [h4k]; lia) hn
  simp only [USize.toNat_zero, Nat.add_zero, Nat.sub_zero, hkk, hc₀] at x₀₃ x₀₄
  rw [h4k, hc₄] at x₄₄
  rw [h4k] at x₄₃
  generalize (arr.uslice r.start r.stop).slice 0 (k + k) = X₀ at *
  generalize (arr.uslice r.start r.stop).slice (4 * k) n = X₄ at *
  -- `r₁ = w₁ - c₀ - c₄ = c₁ + c₂ + c₃`.
  obtain ⟨s₁, e₁⟩ := sub_whole hL w₁ hw₁ X₀ (by rw [x₀₃]; exact hX₀) (by rw [x₀₄, hv₁]; lia)
  replace e₁ := e₁.trans (show _ = c₁ + c₂ + c₃ + c₄ by rw [x₀₄, hv₁]; lia)
  generalize subInto w₁.toUSlice X₀ 0 = q₁ at *
  obtain ⟨s₂, e₂⟩ := sub_whole hL q₁.1 s₁ X₄ (by rw [x₄₃]; exact hX₄) (by rw [x₄₄, e₁]; lia)
  replace e₂ := e₂.trans (show _ = c₁ + c₂ + c₃ by rw [x₄₄, e₁]; lia)
  generalize subInto q₁.1.toUSlice X₄ 0 = q₂ at *
  -- `s₂ = (w₂ - c₀ - 16 c₄) / 2 = c₁ + 2 c₂ + 4 c₃`.
  have h16 : (16 : UInt64).toNat = 16 := rfl
  have h81 : (81 : UInt64).toNat = 81 := rfl
  have h3 : (3 : UInt64).toNat = 3 := rfl
  obtain ⟨s₃, e₃⟩ := sub_whole hL w₂ hw₂ X₀ (by rw [x₀₃]; exact hX₀) (by rw [x₀₄, hv₂]; lia)
  replace e₃ := e₃.trans (show _ = 2 * c₁ + 4 * c₂ + 8 * c₃ + 16 * c₄ by rw [x₀₄, hv₂]; lia)
  generalize subInto w₂.toUSlice X₀ 0 = q₃ at *
  obtain ⟨s₄, e₄⟩ := subMul_whole hL q₃.1 s₃ X₄ 16 (by rw [x₄₃]; exact hX₄)
    (by rw [x₄₄, e₃, h16]; lia)
  replace e₄ := e₄.trans (show _ = 2 * c₁ + 4 * c₂ + 8 * c₃ by rw [x₄₄, e₃, h16]; lia)
  generalize subMulInto q₃.1.toUSlice X₄ 16 = q₄ at *
  obtain ⟨s₅, e₅⟩ := half_whole hL q₄.1 s₄ (by lia) (by rw [e₄]; lia) (by rw [e₄]; lia)
  replace e₅ := e₅.trans (show _ = c₁ + 2 * c₂ + 4 * c₃ by rw [e₄]; lia)
  generalize shl63Into q₄.1.toUSlice = q₅ at *
  -- `s₃ = (w₃ - c₀ - 81 c₄) / 3 = c₁ + 3 c₂ + 9 c₃`.
  obtain ⟨s₆, e₆⟩ := sub_whole hL w₃ hw₃ X₀ (by rw [x₀₃]; exact hX₀) (by rw [x₀₄, hv₃]; lia)
  replace e₆ := e₆.trans (show _ = 3 * c₁ + 9 * c₂ + 27 * c₃ + 81 * c₄ by rw [x₀₄, hv₃]; lia)
  generalize subInto w₃.toUSlice X₀ 0 = q₆ at *
  obtain ⟨s₇, e₇⟩ := subMul_whole hL q₆.1 s₆ X₄ 81 (by rw [x₄₃]; exact hX₄)
    (by rw [x₄₄, e₆, h81]; lia)
  replace e₇ := e₇.trans (show _ = 3 * c₁ + 9 * c₂ + 27 * c₃ by rw [x₄₄, e₆, h81]; lia)
  generalize subMulInto q₆.1.toUSlice X₄ 81 = q₇ at *
  obtain ⟨s₈, e₈⟩ := div3_whole hL q₇.1 s₇ (by rw [e₇]; lia)
  replace e₈ := e₈.trans (show _ = c₁ + 3 * c₂ + 9 * c₃ by rw [e₇]; lia)
  generalize divExact3Into q₇.1.toUSlice = q₈ at *
  -- `t₂ = s₂ - r₁ = c₂ + 3 c₃`.
  obtain ⟨l₁, l₂⟩ := low hL q₂.1 s₂ (by lia) q₅.1 s₅
  have hr₁ : q₂.1.valAt 0 (L - 1) = c₁ + c₂ + c₃ := by
    rw [UInt64Array.valAt_mod _ _ (Nat.sub_le L 1), e₂]
    exact Nat.mod_eq_of_lt (by lia)
  rw [hr₁] at l₂
  obtain ⟨s₉, e₉⟩ := sub_tail hL q₅.1 s₅ (by lia) (q₂.1.toUSlice.slice 0 (q₅.1.usize - 1))
    (Nat.le_of_eq l₁) (by rw [l₂, e₅]; lia)
  replace e₉ := e₉.trans (show _ = c₂ + 3 * c₃ by rw [l₂, e₅]; lia)
  generalize subInto (q₅.1.toUSlice.slice 1 q₅.1.usize) (q₂.1.toUSlice.slice 0 (q₅.1.usize - 1))
    0 = q₉ at *
  -- `t₃ = (s₃ - r₁) / 2 = c₂ + 4 c₃`.
  obtain ⟨w₁₁, w₁₂, w₁₃⟩ := whole hL q₂.1 s₂
  have hq₂ : q₂.1.toUSlice.toNat = c₁ + c₂ + c₃ := by
    rw [USlice.toNat_eq_valAt, w₁₁, w₁₂, w₁₃, e₂]
  obtain ⟨s₁₀, e₁₀⟩ := sub_whole hL q₈.1 s₈ q₂.1.toUSlice (Nat.le_of_eq w₁₂)
    (by rw [hq₂, e₈]; lia)
  replace e₁₀ := e₁₀.trans (show _ = 2 * c₂ + 8 * c₃ by rw [hq₂, e₈]; lia)
  generalize subInto q₈.1.toUSlice q₂.1.toUSlice 0 = q₁₀ at *
  obtain ⟨s₁₁, e₁₁⟩ := half_whole hL q₁₀.1 s₁₀ (by lia) (by rw [e₁₀]; lia) (by rw [e₁₀]; lia)
  replace e₁₁ := e₁₁.trans (show _ = c₂ + 4 * c₃ by rw [e₁₀]; lia)
  generalize shl63Into q₁₀.1.toUSlice = q₁₁ at *
  -- `c₃ = t₃ - t₂`.
  obtain ⟨t₉₁, t₉₂, t₉₃, t₉₄⟩ := tail hL q₉.1 s₉ (by lia)
  obtain ⟨s₁₂, e₁₂⟩ := sub_tail hL q₁₁.1 s₁₁ (by lia) (q₉.1.toUSlice.slice 1 q₉.1.usize)
    (Nat.le_of_eq t₉₃) (by rw [t₉₄, e₉, e₁₁]; lia)
  replace e₁₂ := e₁₂.trans (show _ = c₃ by rw [t₉₄, e₉, e₁₁]; lia)
  generalize subInto (q₁₁.1.toUSlice.slice 1 q₁₁.1.usize) (q₉.1.toUSlice.slice 1 q₉.1.usize)
    0 = q₁₂ at *
  -- `c₂ = t₂ - 3 c₃`.
  obtain ⟨t₁₂₁, t₁₂₂, t₁₂₃, t₁₂₄⟩ := tail hL q₁₂.1 s₁₂ (by lia)
  obtain ⟨s₁₃, e₁₃⟩ := subMul_tail hL q₉.1 s₉ (by lia) (q₁₂.1.toUSlice.slice 1 q₁₂.1.usize) 3
    (Nat.le_of_eq t₁₂₃) (by rw [t₁₂₄, e₁₂, e₉, h3]; lia)
  replace e₁₃ := e₁₃.trans (show _ = c₂ by rw [t₁₂₄, e₁₂, e₉, h3]; lia)
  generalize subMulInto (q₉.1.toUSlice.slice 1 q₉.1.usize) (q₁₂.1.toUSlice.slice 1 q₁₂.1.usize)
    3 = q₁₃ at *
  -- `c₁ = r₁ - c₂ - c₃`.
  obtain ⟨t₁₃₁, t₁₃₂, t₁₃₃, t₁₃₄⟩ := tail hL q₁₃.1 s₁₃ (by lia)
  obtain ⟨s₁₄, e₁₄⟩ := sub_whole hL q₂.1 s₂ (q₁₃.1.toUSlice.slice 1 q₁₃.1.usize) (by rw [t₁₃₃]; lia)
    (by rw [t₁₃₄, e₁₃, e₂]; lia)
  replace e₁₄ := e₁₄.trans (show _ = c₁ + c₃ by rw [t₁₃₄, e₁₃, e₂]; lia)
  generalize subInto q₂.1.toUSlice (q₁₃.1.toUSlice.slice 1 q₁₃.1.usize) 0 = q₁₄ at *
  obtain ⟨s₁₅, e₁₅⟩ := sub_whole hL q₁₄.1 s₁₄ (q₁₂.1.toUSlice.slice 1 q₁₂.1.usize)
    (by rw [t₁₂₃]; lia) (by rw [t₁₂₄, e₁₂, e₁₄]; lia)
  replace e₁₅ := e₁₅.trans (show _ = c₁ by rw [t₁₂₄, e₁₂, e₁₄]; lia)
  generalize subInto q₁₄.1.toUSlice (q₁₂.1.toUSlice.slice 1 q₁₂.1.usize) 0 = q₁₅ at *
  -- The recombination: clear the middle, then add `c₁`, `c₂` and `c₃`.
  obtain ⟨z₁, z₂, z₃⟩ := zero_at arr r h n (k + k) (4 * k) hn (by rw [hkk, h4k]; lia)
    (by rw [h4k]; lia)
  rw [hkk, h4k, hc₀, hc₄] at z₃
  rw [hkk, h4k] at z₂
  generalize zeroInto ((arr.uslice r.start r.stop).slice (k + k) (4 * k)) = A₁ at *
  have hP : ∀ i, i * k.toNat ≤ n.toNat →
      2 ^ (64 * n.toNat) = 2 ^ (64 * (i * k.toNat)) * 2 ^ (64 * (n.toNat - i * k.toNat)) := by
    intro i hi; rw [← Nat.pow_add]; congr 1; lia
  have hpos : ∀ i, 0 < 2 ^ (64 * (i * k.toNat)) := fun _ => Nat.two_pow_pos _
  have hk1 : 2 ^ (64 * k.toNat) = 2 ^ (64 * (1 * k.toNat)) := by rw [Nat.one_mul]
  have hnk : (n - k).toNat = n.toNat - k.toNat :=
    USize.toNat_sub_of_le _ _ (USize.le_iff_toNat_le.2 (by lia))
  have hn2k : (n - (k + k) + 1).toNat = n.toNat - 2 * k.toNat + 1 := by
    rw [USize.toNat_add_of_lt (by
        rw [USize.toNat_sub_of_le _ _ (USize.le_iff_toNat_le.2 (by rw [hkk]; lia)), hkk,
          USize.toNat_one]; lia),
      USize.toNat_sub_of_le _ _ (USize.le_iff_toNat_le.2 (by rw [hkk]; lia)), hkk, USize.toNat_one]
  have hn3k : (n - 3 * k + 1).toNat = n.toNat - 3 * k.toNat + 1 := by
    rw [USize.toNat_add_of_lt (by
        rw [USize.toNat_sub_of_le _ _ (USize.le_iff_toNat_le.2 (by rw [h3k]; lia)), h3k,
          USize.toNat_one]; lia),
      USize.toNat_sub_of_le _ _ (USize.le_iff_toNat_le.2 (by rw [h3k]; lia)), h3k, USize.toNat_one]
  -- `c₁` from limb `k` on.
  -- The terms of the total, each below it.
  have hle₁ : 2 ^ (64 * (1 * k.toNat)) * c₁ ≤
      c₀ + 2 ^ (64 * k.toNat) * c₁ + 2 ^ (64 * (2 * k.toNat)) * c₂ +
        2 ^ (64 * (3 * k.toNat)) * c₃ + 2 ^ (64 * (4 * k.toNat)) * c₄ := by
    rw [Nat.one_mul]
    generalize 2 ^ (64 * k.toNat) * c₁ = T₁
    generalize 2 ^ (64 * (2 * k.toNat)) * c₂ = T₂
    generalize 2 ^ (64 * (3 * k.toNat)) * c₃ = T₃
    generalize 2 ^ (64 * (4 * k.toNat)) * c₄ = T₄
    lia
  have hle₂ : 2 ^ (64 * (2 * k.toNat)) * c₂ ≤
      c₀ + 2 ^ (64 * k.toNat) * c₁ + 2 ^ (64 * (2 * k.toNat)) * c₂ +
        2 ^ (64 * (3 * k.toNat)) * c₃ + 2 ^ (64 * (4 * k.toNat)) * c₄ := by
    generalize 2 ^ (64 * k.toNat) * c₁ = T₁
    generalize 2 ^ (64 * (2 * k.toNat)) * c₂ = T₂
    generalize 2 ^ (64 * (3 * k.toNat)) * c₃ = T₃
    generalize 2 ^ (64 * (4 * k.toNat)) * c₄ = T₄
    lia
  have hle₃ : 2 ^ (64 * (3 * k.toNat)) * c₃ ≤
      c₀ + 2 ^ (64 * k.toNat) * c₁ + 2 ^ (64 * (2 * k.toNat)) * c₂ +
        2 ^ (64 * (3 * k.toNat)) * c₃ + 2 ^ (64 * (4 * k.toNat)) * c₄ := by
    generalize 2 ^ (64 * k.toNat) * c₁ = T₁
    generalize 2 ^ (64 * (2 * k.toNat)) * c₂ = T₂
    generalize 2 ^ (64 * (3 * k.toNat)) * c₃ = T₃
    generalize 2 ^ (64 * (4 * k.toNat)) * c₄ = T₄
    lia
  have hc₁ : c₁ < 2 ^ (64 * (n.toNat - 1 * k.toNat)) :=
    coeff_lt (hpos 1) hle₁ (by rw [← hP 1 (by lia)]; exact htot)
  obtain ⟨C₁z, C₁v⟩ := coeff_slice hL q₁₅.1 s₁₅ 0 (by simp) (j := n - k) c₁ (by simp)
    (by rw [USize.toNat_zero, Nat.sub_zero]; exact e₁₅) (by
      rw [hnk, USize.toNat_zero, Nat.sub_zero]
      rcases Nat.le_total (n.toNat - k.toNat) L with hle | hle
      · rw [Nat.min_eq_left hle]; rw [Nat.one_mul] at hc₁; exact hc₁
      · rw [Nat.min_eq_right hle, ← e₁₅]; exact valAt_lt ..)
  rw [hnk, USize.toNat_zero, Nat.sub_zero] at C₁z
  obtain ⟨a₁, a₂, a₃⟩ := add_at A₁ r z₁ n k hn (by lia) (q₁₅.1.toUSlice.slice 0
    (min (n - k) q₁₅.1.usize)) (by rw [C₁z]; lia) (by
      rw [z₃, C₁v]
      generalize 2 ^ (64 * k.toNat) * c₁ = T₁ at *
      generalize 2 ^ (64 * (2 * k.toNat)) * c₂ = T₂ at *
      generalize 2 ^ (64 * (3 * k.toNat)) * c₃ = T₃ at *
      generalize 2 ^ (64 * (4 * k.toNat)) * c₄ = T₄ at *
      lia)
  rw [z₃, C₁v] at a₃
  generalize (addInto ((A₁.uslice r.start r.stop).slice k n)
    (q₁₅.1.toUSlice.slice 0 (min (n - k) q₁₅.1.usize)) 0).1 = A₂ at *
  -- `c₂` from limb `2 k` on.
  have hc₂ : c₂ < 2 ^ (64 * (n.toNat - 2 * k.toNat)) :=
    coeff_lt (hpos 2) hle₂ (by rw [← hP 2 (by lia)]; exact htot)
  obtain ⟨C₂z, C₂v⟩ := coeff_slice hL q₁₃.1 s₁₃ 1 (by simp) (j := n - (k + k) + 1) c₂
    (by rw [hn2k, USize.toNat_one]; lia) (by rw [USize.toNat_one]; exact e₁₃) (by
      rw [hn2k, USize.toNat_one]
      rcases Nat.le_total (n.toNat - 2 * k.toNat + 1) L with hle | hle
      · rw [Nat.min_eq_left hle, Nat.add_sub_cancel]; exact hc₂
      · rw [Nat.min_eq_right hle, ← e₁₃]; exact valAt_lt ..)
  rw [hn2k, USize.toNat_one] at C₂z
  obtain ⟨b₁, b₂, b₃⟩ := add_at A₂ r a₁ n (k + k) hn (by rw [hkk]; lia) (q₁₃.1.toUSlice.slice 1
    (min (n - (k + k) + 1) q₁₃.1.usize)) (by rw [C₂z, hkk]; lia) (by
      rw [a₃, C₂v, hkk]
      generalize 2 ^ (64 * k.toNat) * c₁ = T₁ at *
      generalize 2 ^ (64 * (2 * k.toNat)) * c₂ = T₂ at *
      generalize 2 ^ (64 * (3 * k.toNat)) * c₃ = T₃ at *
      generalize 2 ^ (64 * (4 * k.toNat)) * c₄ = T₄ at *
      lia)
  rw [a₃, C₂v, hkk] at b₃
  rw [hkk] at b₂
  generalize (addInto ((A₂.uslice r.start r.stop).slice (k + k) n)
    (q₁₃.1.toUSlice.slice 1 (min (n - (k + k) + 1) q₁₃.1.usize)) 0).1 = A₃ at *
  -- `c₃` from limb `3 k` on.
  have hc₃ : c₃ < 2 ^ (64 * (n.toNat - 3 * k.toNat)) :=
    coeff_lt (hpos 3) hle₃ (by rw [← hP 3 (by lia)]; exact htot)
  obtain ⟨C₃z, C₃v⟩ := coeff_slice hL q₁₂.1 s₁₂ 1 (by simp) (j := n - 3 * k + 1) c₃
    (by rw [hn3k, USize.toNat_one]; lia) (by rw [USize.toNat_one]; exact e₁₂) (by
      rw [hn3k, USize.toNat_one]
      rcases Nat.le_total (n.toNat - 3 * k.toNat + 1) L with hle | hle
      · rw [Nat.min_eq_left hle, Nat.add_sub_cancel]; exact hc₃
      · rw [Nat.min_eq_right hle, ← e₁₂]; exact valAt_lt ..)
  rw [hn3k, USize.toNat_one] at C₃z
  obtain ⟨d₁, d₂, d₃⟩ := add_at A₃ r b₁ n (3 * k) hn (by rw [h3k]; lia) (q₁₂.1.toUSlice.slice 1
    (min (n - 3 * k + 1) q₁₂.1.usize)) (by rw [C₃z, h3k]; lia) (by
      rw [b₃, C₃v, h3k]
      generalize 2 ^ (64 * k.toNat) * c₁ = T₁ at *
      generalize 2 ^ (64 * (2 * k.toNat)) * c₂ = T₂ at *
      generalize 2 ^ (64 * (3 * k.toNat)) * c₃ = T₃ at *
      generalize 2 ^ (64 * (4 * k.toNat)) * c₄ = T₄ at *
      lia)
  rw [b₃, C₃v, h3k] at d₃
  rw [h3k] at d₂
  refine ⟨d₁, fun i hi => ?_, ?_⟩
  · rw [d₂ i (by lia), b₂ i (by lia), a₂ i (by lia), z₂ i (by lia)]
  · rw [d₃]
    lia

private theorem interp3_spec (arr : UInt64Array) (r : USlice) (n k : USize)
    (w₁ w₂ : UInt64Array) (L c₀ c₁ c₂ c₃ : Nat)
    (h : arr.size = r.array.size) (hn : n.toNat ≤ r.size.toNat) (hk : 3 * k.toNat ≤ n.toNat)
    (hk₁ : 1 ≤ k.toNat) (hL : L < USize.size) (hL₂ : 2 ≤ L) (hw₁ : w₁.size = L)
    (hw₂ : w₂.size = L) (hX₀ : 2 * k.toNat ≤ L) (hX₃ : n.toNat - 3 * k.toNat ≤ L)
    (hc₀ : arr.valAt r.start.toNat (2 * k.toNat) = c₀)
    (hc₃ : arr.valAt (r.start.toNat + 3 * k.toNat) (n.toNat - 3 * k.toNat) = c₃)
    (hv₁ : w₁.valAt 0 L = c₀ + c₁ + c₂ + c₃)
    (hv₂ : w₂.valAt 0 L = c₀ + 2 * c₁ + 4 * c₂ + 8 * c₃)
    (hb : c₀ + 2 * c₁ + 4 * c₂ + 8 * c₃ < 2 ^ (64 * (L - 1)))
    (htot : c₀ + 2 ^ (64 * k.toNat) * c₁ + 2 ^ (64 * (2 * k.toNat)) * c₂ +
        2 ^ (64 * (3 * k.toNat)) * c₃ < 2 ^ (64 * n.toNat)) :
    (interp3 arr r n k w₁ w₂).size = r.array.size ∧
      (∀ i, (i < r.start.toNat ∨ r.start.toNat + n.toNat ≤ i) →
        (interp3 arr r n k w₁ w₂)[i]! = arr[i]!) ∧
      (interp3 arr r n k w₁ w₂).valAt r.start.toNat n.toNat =
        c₀ + 2 ^ (64 * k.toNat) * c₁ + 2 ^ (64 * (2 * k.toNat)) * c₂ +
        2 ^ (64 * (3 * k.toNat)) * c₃ := by
  dsimp only [interp3]
  have hnS := n.toNat_lt_size
  have hkk : (k + k).toNat = 2 * k.toNat := by rw [USize.toNat_add_of_lt (by lia)]; lia
  have h3k : (3 * k).toNat = 3 * k.toNat := toNat_mul_k k 3 (by decide) n hk
  -- `c₀` and `c₃` in `arr`.
  obtain ⟨x₀₁, x₀₂, x₀₃, x₀₄⟩ := window arr r h (i := 0) (j := k + k) (by simp) (by rw [hkk]; lia)
  obtain ⟨x₃₁, x₃₂, x₃₃, x₃₄⟩ := window arr r h (i := 3 * k) (j := n) (by rw [h3k]; lia) hn
  simp only [USize.toNat_zero, Nat.add_zero, Nat.sub_zero, hkk, hc₀] at x₀₃ x₀₄
  rw [h3k, hc₃] at x₃₄
  rw [h3k] at x₃₃
  generalize (arr.uslice r.start r.stop).slice 0 (k + k) = X₀ at *
  generalize (arr.uslice r.start r.stop).slice (3 * k) n = X₃ at *
  have h8 : (8 : UInt64).toNat = 8 := rfl
  -- `r₁ = w₁ - c₀ - c₃ = c₁ + c₂`.
  obtain ⟨s₁, e₁⟩ := sub_whole hL w₁ hw₁ X₀ (by rw [x₀₃]; exact hX₀) (by rw [x₀₄, hv₁]; lia)
  replace e₁ := e₁.trans (show _ = c₁ + c₂ + c₃ by rw [x₀₄, hv₁]; lia)
  generalize subInto w₁.toUSlice X₀ 0 = q₁ at *
  obtain ⟨s₂, e₂⟩ := sub_whole hL q₁.1 s₁ X₃ (by rw [x₃₃]; exact hX₃) (by rw [x₃₄, e₁]; lia)
  replace e₂ := e₂.trans (show _ = c₁ + c₂ by rw [x₃₄, e₁]; lia)
  generalize subInto q₁.1.toUSlice X₃ 0 = q₂ at *
  -- `s₂ = (w₂ - c₀ - 8 c₃) / 2 = c₁ + 2 c₂`.
  obtain ⟨s₃, e₃⟩ := sub_whole hL w₂ hw₂ X₀ (by rw [x₀₃]; exact hX₀) (by rw [x₀₄, hv₂]; lia)
  replace e₃ := e₃.trans (show _ = 2 * c₁ + 4 * c₂ + 8 * c₃ by rw [x₀₄, hv₂]; lia)
  generalize subInto w₂.toUSlice X₀ 0 = q₃ at *
  obtain ⟨s₄, e₄⟩ := subMul_whole hL q₃.1 s₃ X₃ 8 (by rw [x₃₃]; exact hX₃)
    (by rw [x₃₄, e₃, h8]; lia)
  replace e₄ := e₄.trans (show _ = 2 * c₁ + 4 * c₂ by rw [x₃₄, e₃, h8]; lia)
  generalize subMulInto q₃.1.toUSlice X₃ 8 = q₄ at *
  obtain ⟨s₅, e₅⟩ := half_whole hL q₄.1 s₄ (by lia) (by rw [e₄]; lia) (by rw [e₄]; lia)
  replace e₅ := e₅.trans (show _ = c₁ + 2 * c₂ by rw [e₄]; lia)
  generalize shl63Into q₄.1.toUSlice = q₅ at *
  -- `c₂ = s₂ - r₁`, `c₁ = r₁ - c₂`.
  obtain ⟨l₁, l₂⟩ := low hL q₂.1 s₂ (by lia) q₅.1 s₅
  have hr₁ : q₂.1.valAt 0 (L - 1) = c₁ + c₂ := by
    rw [UInt64Array.valAt_mod _ _ (Nat.sub_le L 1), e₂]
    exact Nat.mod_eq_of_lt (by lia)
  rw [hr₁] at l₂
  obtain ⟨s₉, e₉⟩ := sub_tail hL q₅.1 s₅ (by lia) (q₂.1.toUSlice.slice 0 (q₅.1.usize - 1))
    (Nat.le_of_eq l₁) (by rw [l₂, e₅]; lia)
  replace e₉ := e₉.trans (show _ = c₂ by rw [l₂, e₅]; lia)
  generalize subInto (q₅.1.toUSlice.slice 1 q₅.1.usize) (q₂.1.toUSlice.slice 0 (q₅.1.usize - 1))
    0 = q₉ at *
  obtain ⟨t₉₁, t₉₂, t₉₃, t₉₄⟩ := tail hL q₉.1 s₉ (by lia)
  obtain ⟨s₁₄, e₁₄⟩ := sub_whole hL q₂.1 s₂ (q₉.1.toUSlice.slice 1 q₉.1.usize) (by rw [t₉₃]; lia)
    (by rw [t₉₄, e₉, e₂]; lia)
  replace e₁₄ := e₁₄.trans (show _ = c₁ by rw [t₉₄, e₉, e₂]; lia)
  generalize subInto q₂.1.toUSlice (q₉.1.toUSlice.slice 1 q₉.1.usize) 0 = q₁₄ at *
  -- The recombination: clear the middle, then add `c₁` and `c₂`.
  obtain ⟨z₁, z₂, z₃⟩ := zero_at arr r h n (k + k) (3 * k) hn (by rw [hkk, h3k]; lia)
    (by rw [h3k]; lia)
  rw [hkk, h3k, hc₀, hc₃] at z₃
  rw [hkk, h3k] at z₂
  generalize zeroInto ((arr.uslice r.start r.stop).slice (k + k) (3 * k)) = A₁ at *
  have hP : ∀ i, i * k.toNat ≤ n.toNat →
      2 ^ (64 * n.toNat) = 2 ^ (64 * (i * k.toNat)) * 2 ^ (64 * (n.toNat - i * k.toNat)) := by
    intro i hi; rw [← Nat.pow_add]; congr 1; lia
  have hpos : ∀ i, 0 < 2 ^ (64 * (i * k.toNat)) := fun _ => Nat.two_pow_pos _
  have hnk : (n - k).toNat = n.toNat - k.toNat :=
    USize.toNat_sub_of_le _ _ (USize.le_iff_toNat_le.2 (by lia))
  have hn2k : (n - (k + k) + 1).toNat = n.toNat - 2 * k.toNat + 1 := by
    rw [USize.toNat_add_of_lt (by
        rw [USize.toNat_sub_of_le _ _ (USize.le_iff_toNat_le.2 (by rw [hkk]; lia)), hkk,
          USize.toNat_one]; lia),
      USize.toNat_sub_of_le _ _ (USize.le_iff_toNat_le.2 (by rw [hkk]; lia)), hkk, USize.toNat_one]
  have hle₁ : 2 ^ (64 * (1 * k.toNat)) * c₁ ≤
      c₀ + 2 ^ (64 * k.toNat) * c₁ + 2 ^ (64 * (2 * k.toNat)) * c₂ +
        2 ^ (64 * (3 * k.toNat)) * c₃ := by
    rw [Nat.one_mul]
    generalize 2 ^ (64 * k.toNat) * c₁ = T₁
    generalize 2 ^ (64 * (2 * k.toNat)) * c₂ = T₂
    generalize 2 ^ (64 * (3 * k.toNat)) * c₃ = T₃
    lia
  have hle₂ : 2 ^ (64 * (2 * k.toNat)) * c₂ ≤
      c₀ + 2 ^ (64 * k.toNat) * c₁ + 2 ^ (64 * (2 * k.toNat)) * c₂ +
        2 ^ (64 * (3 * k.toNat)) * c₃ := by
    generalize 2 ^ (64 * k.toNat) * c₁ = T₁
    generalize 2 ^ (64 * (2 * k.toNat)) * c₂ = T₂
    generalize 2 ^ (64 * (3 * k.toNat)) * c₃ = T₃
    lia
  -- `c₁` from limb `k` on.
  have hc₁ : c₁ < 2 ^ (64 * (n.toNat - 1 * k.toNat)) :=
    coeff_lt (hpos 1) hle₁ (by rw [← hP 1 (by lia)]; exact htot)
  obtain ⟨C₁z, C₁v⟩ := coeff_slice hL q₁₄.1 s₁₄ 0 (by simp) (j := n - k) c₁ (by simp)
    (by rw [USize.toNat_zero, Nat.sub_zero]; exact e₁₄) (by
      rw [hnk, USize.toNat_zero, Nat.sub_zero]
      rcases Nat.le_total (n.toNat - k.toNat) L with hle | hle
      · rw [Nat.min_eq_left hle]; rw [Nat.one_mul] at hc₁; exact hc₁
      · rw [Nat.min_eq_right hle, ← e₁₄]; exact valAt_lt ..)
  rw [hnk, USize.toNat_zero, Nat.sub_zero] at C₁z
  obtain ⟨a₁, a₂, a₃⟩ := add_at A₁ r z₁ n k hn (by lia) (q₁₄.1.toUSlice.slice 0
    (min (n - k) q₁₄.1.usize)) (by rw [C₁z]; lia) (by
      rw [z₃, C₁v]
      generalize 2 ^ (64 * k.toNat) * c₁ = T₁ at *
      generalize 2 ^ (64 * (2 * k.toNat)) * c₂ = T₂ at *
      generalize 2 ^ (64 * (3 * k.toNat)) * c₃ = T₃ at *
      lia)
  rw [z₃, C₁v] at a₃
  generalize (addInto ((A₁.uslice r.start r.stop).slice k n)
    (q₁₄.1.toUSlice.slice 0 (min (n - k) q₁₄.1.usize)) 0).1 = A₂ at *
  -- `c₂` from limb `2 k` on.
  have hc₂ : c₂ < 2 ^ (64 * (n.toNat - 2 * k.toNat)) :=
    coeff_lt (hpos 2) hle₂ (by rw [← hP 2 (by lia)]; exact htot)
  obtain ⟨C₂z, C₂v⟩ := coeff_slice hL q₉.1 s₉ 1 (by simp) (j := n - (k + k) + 1) c₂
    (by rw [hn2k, USize.toNat_one]; lia) (by rw [USize.toNat_one]; exact e₉) (by
      rw [hn2k, USize.toNat_one]
      rcases Nat.le_total (n.toNat - 2 * k.toNat + 1) L with hle | hle
      · rw [Nat.min_eq_left hle, Nat.add_sub_cancel]; exact hc₂
      · rw [Nat.min_eq_right hle, ← e₉]; exact valAt_lt ..)
  rw [hn2k, USize.toNat_one] at C₂z
  obtain ⟨b₁, b₂, b₃⟩ := add_at A₂ r a₁ n (k + k) hn (by rw [hkk]; lia) (q₉.1.toUSlice.slice 1
    (min (n - (k + k) + 1) q₉.1.usize)) (by rw [C₂z, hkk]; lia) (by
      rw [a₃, C₂v, hkk]
      generalize 2 ^ (64 * k.toNat) * c₁ = T₁ at *
      generalize 2 ^ (64 * (2 * k.toNat)) * c₂ = T₂ at *
      generalize 2 ^ (64 * (3 * k.toNat)) * c₃ = T₃ at *
      lia)
  rw [a₃, C₂v, hkk] at b₃
  rw [hkk] at b₂
  refine ⟨b₁, fun i hi => ?_, ?_⟩
  · rw [b₂ i (by lia), a₂ i (by lia), z₂ i (by lia)]
  · rw [b₃]
    lia

/-! ### The interpolations of Toom-4 and Toom-4 by 3 -/

/--
The interpolation of degree 6 at `0, 1, …, 5, ∞`: from `c₀` in limbs `[r.start, r.start + 2 k)`
and `c_6` from limb `r.start + 6 k` to `r.start + n`, with `w₁, …, w_5` the values at `1, …, 5`,
writes `c₀ + c₁ x + ⋯ + c_6 x^6` into the `n` limbs from `r.start`, `x = 2^(64 k)`. The values
`(w_j - c₀ - j^6 c_6) / j`, their divided differences and Horner's rule are all in place on the `w`.
-/
public def interp6 (arr : UInt64Array) (r : USlice) (n k : USize) (w₁ w₂ w₃ w₄ w₅ : UInt64Array) :
    UInt64Array :=
  let R := arr.uslice r.start r.stop
  let X₀ := R.slice 0 (k + k)
  let Xd := R.slice (6 * k) n
  let w₁ := (subInto w₁.toUSlice X₀).1
  let w₁ := (subInto w₁.toUSlice Xd).1
  let w₂ := (subInto w₂.toUSlice X₀).1
  let w₂ := (subMulInto w₂.toUSlice Xd 64).1
  let w₂ := rshiftInto w₂.toUSlice 1
  let w₃ := (subInto w₃.toUSlice X₀).1
  let w₃ := (subMulInto w₃.toUSlice Xd 729).1
  let w₃ := (divExact3Into w₃.toUSlice).1
  let w₄ := (subInto w₄.toUSlice X₀).1
  let w₄ := (subMulInto w₄.toUSlice Xd 4096).1
  let w₄ := rshiftInto w₄.toUSlice 2
  let w₅ := (subInto w₅.toUSlice X₀).1
  let w₅ := (subMulInto w₅.toUSlice Xd 15625).1
  let w₅ := (divExact5Into w₅.toUSlice).1
  let w₅ := (subInto w₅.toUSlice w₄.toUSlice).1
  let w₄ := (subInto w₄.toUSlice w₃.toUSlice).1
  let w₃ := (subInto w₃.toUSlice w₂.toUSlice).1
  let w₂ := (subInto w₂.toUSlice w₁.toUSlice).1
  let w₅ := (subInto w₅.toUSlice w₄.toUSlice).1
  let w₅ := rshiftInto w₅.toUSlice 1
  let w₄ := (subInto w₄.toUSlice w₃.toUSlice).1
  let w₄ := rshiftInto w₄.toUSlice 1
  let w₃ := (subInto w₃.toUSlice w₂.toUSlice).1
  let w₃ := rshiftInto w₃.toUSlice 1
  let w₅ := (subInto w₅.toUSlice w₄.toUSlice).1
  let w₅ := (divExact3Into w₅.toUSlice).1
  let w₄ := (subInto w₄.toUSlice w₃.toUSlice).1
  let w₄ := (divExact3Into w₄.toUSlice).1
  let w₅ := (subInto w₅.toUSlice w₄.toUSlice).1
  let w₅ := rshiftInto w₅.toUSlice 2
  let w₄ := (subMulInto w₄.toUSlice w₅.toUSlice 4).1
  let w₃ := (subMulInto w₃.toUSlice w₄.toUSlice 3).1
  let w₄ := (subMulInto w₄.toUSlice w₅.toUSlice 3).1
  let w₂ := (subMulInto w₂.toUSlice w₃.toUSlice 2).1
  let w₃ := (subMulInto w₃.toUSlice w₄.toUSlice 2).1
  let w₄ := (subMulInto w₄.toUSlice w₅.toUSlice 2).1
  let w₁ := (subInto w₁.toUSlice w₂.toUSlice).1
  let w₂ := (subInto w₂.toUSlice w₃.toUSlice).1
  let w₃ := (subInto w₃.toUSlice w₄.toUSlice).1
  let w₄ := (subInto w₄.toUSlice w₅.toUSlice).1
  -- The recombination.
  let arr := zeroInto ((arr.uslice r.start r.stop).slice (k + k) (6 * k))
  let arr := (addInto ((arr.uslice r.start r.stop).slice k n)
    (w₁.toUSlice.slice 0 (min (n - k) w₁.usize))).1
  let arr := (addInto ((arr.uslice r.start r.stop).slice (k + k) n)
    (w₂.toUSlice.slice 0 (min (n - (k + k)) w₂.usize))).1
  let arr := (addInto ((arr.uslice r.start r.stop).slice (3 * k) n)
    (w₃.toUSlice.slice 0 (min (n - (3 * k)) w₃.usize))).1
  let arr := (addInto ((arr.uslice r.start r.stop).slice (4 * k) n)
    (w₄.toUSlice.slice 0 (min (n - (4 * k)) w₄.usize))).1
  (addInto ((arr.uslice r.start r.stop).slice (5 * k) n)
    (w₅.toUSlice.slice 0 (min (n - (5 * k)) w₅.usize))).1

set_option maxHeartbeats 1000000 in
private theorem interp6_spec (arr : UInt64Array) (r : USlice) (n k : USize)
    (w₁ w₂ w₃ w₄ w₅ : UInt64Array) (L c₀ c₁ c₂ c₃ c₄ c₅ c₆ : Nat)
    (h : arr.size = r.array.size) (hn : n.toNat ≤ r.size.toNat) (hk : 6 * k.toNat ≤ n.toNat)
    (hk₁ : 1 ≤ k.toNat) (hL : L < USize.size) (hw₁ : w₁.size = L) (hw₂ : w₂.size = L)
        (hw₃ : w₃.size = L) (hw₄ : w₄.size = L) (hw₅ : w₅.size = L)
    (hX₀ : 2 * k.toNat ≤ L) (hXd : n.toNat - 6 * k.toNat ≤ L)
    (hc₀ : arr.valAt r.start.toNat (2 * k.toNat) = c₀)
    (hc₆ : arr.valAt (r.start.toNat + 6 * k.toNat) (n.toNat - 6 * k.toNat) = c₆)
    (hv₁ : w₁.valAt 0 L = c₀ + c₁ + c₂ + c₃ + c₄ + c₅ + c₆)
    (hv₂ : w₂.valAt 0 L = c₀ + 2 * c₁ + 4 * c₂ + 8 * c₃ + 16 * c₄ + 32 * c₅ + 64 * c₆)
    (hv₃ : w₃.valAt 0 L = c₀ + 3 * c₁ + 9 * c₂ + 27 * c₃ + 81 * c₄ + 243 * c₅ + 729 * c₆)
    (hv₄ : w₄.valAt 0 L = c₀ + 4 * c₁ + 16 * c₂ + 64 * c₃ + 256 * c₄ + 1024 * c₅ + 4096 * c₆)
    (hv₅ : w₅.valAt 0 L = c₀ + 5 * c₁ + 25 * c₂ + 125 * c₃ + 625 * c₄ + 3125 * c₅ + 15625 * c₆)
    (htot : c₀ + 2 ^ (64 * k.toNat) * c₁ + 2 ^ (64 * (2 * k.toNat)) * c₂ + 2 ^
        (64 * (3 * k.toNat)) * c₃ + 2 ^ (64 * (4 * k.toNat)) * c₄ + 2 ^ (64 * (5 * k.toNat)) * c₅ +
        2 ^ (64 * (6 * k.toNat)) * c₆ < 2 ^ (64 * n.toNat)) :
    (interp6 arr r n k w₁ w₂ w₃ w₄ w₅).size = r.array.size ∧
      (∀ i, (i < r.start.toNat ∨ r.start.toNat + n.toNat ≤ i) →
        (interp6 arr r n k w₁ w₂ w₃ w₄ w₅)[i]! = arr[i]!) ∧
      (interp6 arr r n k w₁ w₂ w₃ w₄ w₅).valAt r.start.toNat n.toNat =
        c₀ + 2 ^ (64 * k.toNat) * c₁ + 2 ^ (64 * (2 * k.toNat)) * c₂ + 2 ^ (64 * (3 * k.toNat)) *
            c₃ + 2 ^ (64 * (4 * k.toNat)) * c₄ + 2 ^ (64 * (5 * k.toNat)) * c₅ + 2 ^
            (64 * (6 * k.toNat)) * c₆ := by
  dsimp only [interp6]
  have hnS := n.toNat_lt_size
  have hkk : (k + k).toNat = 2 * k.toNat := by rw [USize.toNat_add_of_lt (by lia)]; lia
  have h3k : (3 * k).toNat = 3 * k.toNat := toNat_mul_k k 3 (by decide) n (by lia)
  have h4k : (4 * k).toNat = 4 * k.toNat := toNat_mul_k k 4 (by decide) n (by lia)
  have h5k : (5 * k).toNat = 5 * k.toNat := toNat_mul_k k 5 (by decide) n (by lia)
  have h6k : (6 * k).toNat = 6 * k.toNat := toNat_mul_k k 6 (by decide) n (by lia)
  -- `c₀` and `c_6` in `arr`.
  obtain ⟨x₀₁, x₀₂, x₀₃, x₀₄⟩ := window arr r h (i := 0) (j := k + k) (by simp) (by rw [hkk]; lia)
  obtain ⟨xd₁, xd₂, xd₃, xd₄⟩ := window arr r h (i := 6 * k) (j := n) (by rw [h6k]; lia) hn
  simp only [USize.toNat_zero, Nat.add_zero, Nat.sub_zero, hkk, hc₀] at x₀₃ x₀₄
  rw [h6k, hc₆] at xd₄
  rw [h6k] at xd₃
  generalize (arr.uslice r.start r.stop).slice 0 (k + k) = X₀ at *
  generalize (arr.uslice r.start r.stop).slice (6 * k) n = Xd at *
  obtain ⟨s₁, e₁⟩ := subSl hL w₁ hw₁ X₀ (by rw [x₀₃]; exact hX₀) (R := c₁ + c₂ + c₃ + c₄ + c₅ + c₆)
      hv₁ x₀₄ (by lia)
  generalize (subInto w₁.toUSlice X₀ 0).1 = q₁ at *
  obtain ⟨s₂, e₂⟩ := subSl hL q₁ s₁ Xd (by rw [xd₃]; exact hXd) (R := c₁ + c₂ + c₃ + c₄ + c₅) e₁ xd₄
      (by lia)
  generalize (subInto q₁.toUSlice Xd 0).1 = q₂ at *
  obtain ⟨s₃, e₃⟩ := subSl hL w₂ hw₂ X₀ (by rw [x₀₃]; exact hX₀)
      (R := 2 * c₁ + 4 * c₂ + 8 * c₃ + 16 * c₄ + 32 * c₅ + 64 * c₆) hv₂ x₀₄ (by lia)
  generalize (subInto w₂.toUSlice X₀ 0).1 = q₃ at *
  obtain ⟨s₄, e₄⟩ := subMulSl hL q₃ s₃ Xd (by rw [xd₃]; exact hXd) 64
      (R := 2 * c₁ + 4 * c₂ + 8 * c₃ + 16 * c₄ + 32 * c₅) e₃ xd₄ rfl (by lia)
  generalize (subMulInto q₃.toUSlice Xd 64).1 = q₄ at *
  obtain ⟨s₅, e₅⟩ := shrW hL q₄ s₄ 1 (by decide) (by decide)
      (R := c₁ + 2 * c₂ + 4 * c₃ + 8 * c₄ + 16 * c₅) rfl e₄ (by lia)
  generalize rshiftInto q₄.toUSlice 1 = q₅ at *
  obtain ⟨s₆, e₆⟩ := subSl hL w₃ hw₃ X₀ (by rw [x₀₃]; exact hX₀)
      (R := 3 * c₁ + 9 * c₂ + 27 * c₃ + 81 * c₄ + 243 * c₅ + 729 * c₆) hv₃ x₀₄ (by lia)
  generalize (subInto w₃.toUSlice X₀ 0).1 = q₆ at *
  obtain ⟨s₇, e₇⟩ := subMulSl hL q₆ s₆ Xd (by rw [xd₃]; exact hXd) 729
      (R := 3 * c₁ + 9 * c₂ + 27 * c₃ + 81 * c₄ + 243 * c₅) e₆ xd₄ rfl (by lia)
  generalize (subMulInto q₆.toUSlice Xd 729).1 = q₇ at *
  obtain ⟨s₈, e₈⟩ := div3W hL q₇ s₇ (R := c₁ + 3 * c₂ + 9 * c₃ + 27 * c₄ + 81 * c₅) e₇ (by lia)
  generalize (divExact3Into q₇.toUSlice).1 = q₈ at *
  obtain ⟨s₉, e₉⟩ := subSl hL w₄ hw₄ X₀ (by rw [x₀₃]; exact hX₀)
      (R := 4 * c₁ + 16 * c₂ + 64 * c₃ + 256 * c₄ + 1024 * c₅ + 4096 * c₆) hv₄ x₀₄ (by lia)
  generalize (subInto w₄.toUSlice X₀ 0).1 = q₉ at *
  obtain ⟨s₁₀, e₁₀⟩ := subMulSl hL q₉ s₉ Xd (by rw [xd₃]; exact hXd) 4096
      (R := 4 * c₁ + 16 * c₂ + 64 * c₃ + 256 * c₄ + 1024 * c₅) e₉ xd₄ rfl (by lia)
  generalize (subMulInto q₉.toUSlice Xd 4096).1 = q₁₀ at *
  obtain ⟨s₁₁, e₁₁⟩ := shrW hL q₁₀ s₁₀ 2 (by decide) (by decide)
      (R := c₁ + 4 * c₂ + 16 * c₃ + 64 * c₄ + 256 * c₅) rfl e₁₀ (by lia)
  generalize rshiftInto q₁₀.toUSlice 2 = q₁₁ at *
  obtain ⟨s₁₂, e₁₂⟩ := subSl hL w₅ hw₅ X₀ (by rw [x₀₃]; exact hX₀)
      (R := 5 * c₁ + 25 * c₂ + 125 * c₃ + 625 * c₄ + 3125 * c₅ + 15625 * c₆) hv₅ x₀₄ (by lia)
  generalize (subInto w₅.toUSlice X₀ 0).1 = q₁₂ at *
  obtain ⟨s₁₃, e₁₃⟩ := subMulSl hL q₁₂ s₁₂ Xd (by rw [xd₃]; exact hXd) 15625
      (R := 5 * c₁ + 25 * c₂ + 125 * c₃ + 625 * c₄ + 3125 * c₅) e₁₂ xd₄ rfl (by lia)
  generalize (subMulInto q₁₂.toUSlice Xd 15625).1 = q₁₃ at *
  obtain ⟨s₁₄, e₁₄⟩ := div5W hL q₁₃ s₁₃ (R := c₁ + 5 * c₂ + 25 * c₃ + 125 * c₄ + 625 * c₅) e₁₃
      (by lia)
  generalize (divExact5Into q₁₃.toUSlice).1 = q₁₄ at *
  obtain ⟨s₁₅, e₁₅⟩ := subW hL q₁₄ q₁₁ s₁₄ s₁₁ (R := c₂ + 9 * c₃ + 61 * c₄ + 369 * c₅) e₁₄ e₁₁
      (by lia)
  generalize (subInto q₁₄.toUSlice q₁₁.toUSlice 0).1 = q₁₅ at *
  obtain ⟨s₁₆, e₁₆⟩ := subW hL q₁₁ q₈ s₁₁ s₈ (R := c₂ + 7 * c₃ + 37 * c₄ + 175 * c₅) e₁₁ e₈ (by lia)
  generalize (subInto q₁₁.toUSlice q₈.toUSlice 0).1 = q₁₆ at *
  obtain ⟨s₁₇, e₁₇⟩ := subW hL q₈ q₅ s₈ s₅ (R := c₂ + 5 * c₃ + 19 * c₄ + 65 * c₅) e₈ e₅ (by lia)
  generalize (subInto q₈.toUSlice q₅.toUSlice 0).1 = q₁₇ at *
  obtain ⟨s₁₈, e₁₈⟩ := subW hL q₅ q₂ s₅ s₂ (R := c₂ + 3 * c₃ + 7 * c₄ + 15 * c₅) e₅ e₂ (by lia)
  generalize (subInto q₅.toUSlice q₂.toUSlice 0).1 = q₁₈ at *
  obtain ⟨s₁₉, e₁₉⟩ := subW hL q₁₅ q₁₆ s₁₅ s₁₆ (R := 2 * c₃ + 24 * c₄ + 194 * c₅) e₁₅ e₁₆ (by lia)
  generalize (subInto q₁₅.toUSlice q₁₆.toUSlice 0).1 = q₁₉ at *
  obtain ⟨s₂₀, e₂₀⟩ := shrW hL q₁₉ s₁₉ 1 (by decide) (by decide) (R := c₃ + 12 * c₄ + 97 * c₅) rfl
      e₁₉ (by lia)
  generalize rshiftInto q₁₉.toUSlice 1 = q₂₀ at *
  obtain ⟨s₂₁, e₂₁⟩ := subW hL q₁₆ q₁₇ s₁₆ s₁₇ (R := 2 * c₃ + 18 * c₄ + 110 * c₅) e₁₆ e₁₇ (by lia)
  generalize (subInto q₁₆.toUSlice q₁₇.toUSlice 0).1 = q₂₁ at *
  obtain ⟨s₂₂, e₂₂⟩ := shrW hL q₂₁ s₂₁ 1 (by decide) (by decide) (R := c₃ + 9 * c₄ + 55 * c₅) rfl
      e₂₁ (by lia)
  generalize rshiftInto q₂₁.toUSlice 1 = q₂₂ at *
  obtain ⟨s₂₃, e₂₃⟩ := subW hL q₁₇ q₁₈ s₁₇ s₁₈ (R := 2 * c₃ + 12 * c₄ + 50 * c₅) e₁₇ e₁₈ (by lia)
  generalize (subInto q₁₇.toUSlice q₁₈.toUSlice 0).1 = q₂₃ at *
  obtain ⟨s₂₄, e₂₄⟩ := shrW hL q₂₃ s₂₃ 1 (by decide) (by decide) (R := c₃ + 6 * c₄ + 25 * c₅) rfl
      e₂₃ (by lia)
  generalize rshiftInto q₂₃.toUSlice 1 = q₂₄ at *
  obtain ⟨s₂₅, e₂₅⟩ := subW hL q₂₀ q₂₂ s₂₀ s₂₂ (R := 3 * c₄ + 42 * c₅) e₂₀ e₂₂ (by lia)
  generalize (subInto q₂₀.toUSlice q₂₂.toUSlice 0).1 = q₂₅ at *
  obtain ⟨s₂₆, e₂₆⟩ := div3W hL q₂₅ s₂₅ (R := c₄ + 14 * c₅) e₂₅ (by lia)
  generalize (divExact3Into q₂₅.toUSlice).1 = q₂₆ at *
  obtain ⟨s₂₇, e₂₇⟩ := subW hL q₂₂ q₂₄ s₂₂ s₂₄ (R := 3 * c₄ + 30 * c₅) e₂₂ e₂₄ (by lia)
  generalize (subInto q₂₂.toUSlice q₂₄.toUSlice 0).1 = q₂₇ at *
  obtain ⟨s₂₈, e₂₈⟩ := div3W hL q₂₇ s₂₇ (R := c₄ + 10 * c₅) e₂₇ (by lia)
  generalize (divExact3Into q₂₇.toUSlice).1 = q₂₈ at *
  obtain ⟨s₂₉, e₂₉⟩ := subW hL q₂₆ q₂₈ s₂₆ s₂₈ (R := 4 * c₅) e₂₆ e₂₈ (by lia)
  generalize (subInto q₂₆.toUSlice q₂₈.toUSlice 0).1 = q₂₉ at *
  obtain ⟨s₃₀, e₃₀⟩ := shrW hL q₂₉ s₂₉ 2 (by decide) (by decide) (R := c₅) rfl e₂₉ (by lia)
  generalize rshiftInto q₂₉.toUSlice 2 = q₃₀ at *
  obtain ⟨s₃₁, e₃₁⟩ := subMulW hL q₂₈ q₃₀ s₂₈ s₃₀ 4 (R := c₄ + 6 * c₅) e₂₈ e₃₀ rfl (by lia)
  generalize (subMulInto q₂₈.toUSlice q₃₀.toUSlice 4).1 = q₃₁ at *
  obtain ⟨s₃₂, e₃₂⟩ := subMulW hL q₂₄ q₃₁ s₂₄ s₃₁ 3 (R := c₃ + 3 * c₄ + 7 * c₅) e₂₄ e₃₁ rfl (by lia)
  generalize (subMulInto q₂₄.toUSlice q₃₁.toUSlice 3).1 = q₃₂ at *
  obtain ⟨s₃₃, e₃₃⟩ := subMulW hL q₃₁ q₃₀ s₃₁ s₃₀ 3 (R := c₄ + 3 * c₅) e₃₁ e₃₀ rfl (by lia)
  generalize (subMulInto q₃₁.toUSlice q₃₀.toUSlice 3).1 = q₃₃ at *
  obtain ⟨s₃₄, e₃₄⟩ := subMulW hL q₁₈ q₃₂ s₁₈ s₃₂ 2 (R := c₂ + c₃ + c₄ + c₅) e₁₈ e₃₂ rfl (by lia)
  generalize (subMulInto q₁₈.toUSlice q₃₂.toUSlice 2).1 = q₃₄ at *
  obtain ⟨s₃₅, e₃₅⟩ := subMulW hL q₃₂ q₃₃ s₃₂ s₃₃ 2 (R := c₃ + c₄ + c₅) e₃₂ e₃₃ rfl (by lia)
  generalize (subMulInto q₃₂.toUSlice q₃₃.toUSlice 2).1 = q₃₅ at *
  obtain ⟨s₃₆, e₃₆⟩ := subMulW hL q₃₃ q₃₀ s₃₃ s₃₀ 2 (R := c₄ + c₅) e₃₃ e₃₀ rfl (by lia)
  generalize (subMulInto q₃₃.toUSlice q₃₀.toUSlice 2).1 = q₃₆ at *
  obtain ⟨s₃₇, e₃₇⟩ := subW hL q₂ q₃₄ s₂ s₃₄ (R := c₁) e₂ e₃₄ (by lia)
  generalize (subInto q₂.toUSlice q₃₄.toUSlice 0).1 = q₃₇ at *
  obtain ⟨s₃₈, e₃₈⟩ := subW hL q₃₄ q₃₅ s₃₄ s₃₅ (R := c₂) e₃₄ e₃₅ (by lia)
  generalize (subInto q₃₄.toUSlice q₃₅.toUSlice 0).1 = q₃₈ at *
  obtain ⟨s₃₉, e₃₉⟩ := subW hL q₃₅ q₃₆ s₃₅ s₃₆ (R := c₃) e₃₅ e₃₆ (by lia)
  generalize (subInto q₃₅.toUSlice q₃₆.toUSlice 0).1 = q₃₉ at *
  obtain ⟨s₄₀, e₄₀⟩ := subW hL q₃₆ q₃₀ s₃₆ s₃₀ (R := c₄) e₃₆ e₃₀ (by lia)
  generalize (subInto q₃₆.toUSlice q₃₀.toUSlice 0).1 = q₄₀ at *
  -- The recombination: clear the middle, then add `c₁`, …, `c_5`.
  obtain ⟨z₁, z₂, z₃⟩ := zero_at arr r h n (k + k) (6 * k) hn (by rw [hkk, h6k]; lia)
    (by rw [h6k]; lia)
  rw [hkk, h6k, hc₀, hc₆] at z₃
  rw [hkk, h6k] at z₂
  generalize zeroInto ((arr.uslice r.start r.stop).slice (k + k) (6 * k)) = A₀ at *
  obtain ⟨a₁₁, a₁₂, a₁₃⟩ := rec_step A₀ r z₁ n k hn (by lia) hL q₃₇ s₃₇ c₁ e₃₇
    (by
      rw [z₃]
      generalize 2 ^ (64 * k.toNat) * c₁ = T₁ at *
      generalize 2 ^ (64 * (2 * k.toNat)) * c₂ = T₂ at *
      generalize 2 ^ (64 * (3 * k.toNat)) * c₃ = T₃ at *
      generalize 2 ^ (64 * (4 * k.toNat)) * c₄ = T₄ at *
      generalize 2 ^ (64 * (5 * k.toNat)) * c₅ = T₅ at *
      generalize 2 ^ (64 * (6 * k.toNat)) * c₆ = T₆ at *
      lia)
  rw [z₃] at a₁₃
  generalize (addInto ((A₀.uslice r.start r.stop).slice k n)
    (q₃₇.toUSlice.slice 0 (min (n - k) q₃₇.usize)) 0).1 = A₁ at *
  obtain ⟨a₂₁, a₂₂, a₂₃⟩ := rec_step A₁ r a₁₁ n (k + k) hn (by rw [hkk]; lia) hL q₃₈ s₃₈ c₂ e₃₈
    (by
      rw [hkk, a₁₃]
      generalize 2 ^ (64 * k.toNat) * c₁ = T₁ at *
      generalize 2 ^ (64 * (2 * k.toNat)) * c₂ = T₂ at *
      generalize 2 ^ (64 * (3 * k.toNat)) * c₃ = T₃ at *
      generalize 2 ^ (64 * (4 * k.toNat)) * c₄ = T₄ at *
      generalize 2 ^ (64 * (5 * k.toNat)) * c₅ = T₅ at *
      generalize 2 ^ (64 * (6 * k.toNat)) * c₆ = T₆ at *
      lia)
  rw [hkk, a₁₃] at a₂₃
  rw [hkk] at a₂₂
  generalize (addInto ((A₁.uslice r.start r.stop).slice (k + k) n)
    (q₃₈.toUSlice.slice 0 (min (n - (k + k)) q₃₈.usize)) 0).1 = A₂ at *
  obtain ⟨a₃₁, a₃₂, a₃₃⟩ := rec_step A₂ r a₂₁ n (3 * k) hn (by rw [h3k]; lia) hL q₃₉ s₃₉ c₃ e₃₉
    (by
      rw [h3k, a₂₃]
      generalize 2 ^ (64 * k.toNat) * c₁ = T₁ at *
      generalize 2 ^ (64 * (2 * k.toNat)) * c₂ = T₂ at *
      generalize 2 ^ (64 * (3 * k.toNat)) * c₃ = T₃ at *
      generalize 2 ^ (64 * (4 * k.toNat)) * c₄ = T₄ at *
      generalize 2 ^ (64 * (5 * k.toNat)) * c₅ = T₅ at *
      generalize 2 ^ (64 * (6 * k.toNat)) * c₆ = T₆ at *
      lia)
  rw [h3k, a₂₃] at a₃₃
  rw [h3k] at a₃₂
  generalize (addInto ((A₂.uslice r.start r.stop).slice (3 * k) n)
    (q₃₉.toUSlice.slice 0 (min (n - (3 * k)) q₃₉.usize)) 0).1 = A₃ at *
  obtain ⟨a₄₁, a₄₂, a₄₃⟩ := rec_step A₃ r a₃₁ n (4 * k) hn (by rw [h4k]; lia) hL q₄₀ s₄₀ c₄ e₄₀
    (by
      rw [h4k, a₃₃]
      generalize 2 ^ (64 * k.toNat) * c₁ = T₁ at *
      generalize 2 ^ (64 * (2 * k.toNat)) * c₂ = T₂ at *
      generalize 2 ^ (64 * (3 * k.toNat)) * c₃ = T₃ at *
      generalize 2 ^ (64 * (4 * k.toNat)) * c₄ = T₄ at *
      generalize 2 ^ (64 * (5 * k.toNat)) * c₅ = T₅ at *
      generalize 2 ^ (64 * (6 * k.toNat)) * c₆ = T₆ at *
      lia)
  rw [h4k, a₃₃] at a₄₃
  rw [h4k] at a₄₂
  generalize (addInto ((A₃.uslice r.start r.stop).slice (4 * k) n)
    (q₄₀.toUSlice.slice 0 (min (n - (4 * k)) q₄₀.usize)) 0).1 = A₄ at *
  obtain ⟨a₅₁, a₅₂, a₅₃⟩ := rec_step A₄ r a₄₁ n (5 * k) hn (by rw [h5k]; lia) hL q₃₀ s₃₀ c₅ e₃₀
    (by
      rw [h5k, a₄₃]
      generalize 2 ^ (64 * k.toNat) * c₁ = T₁ at *
      generalize 2 ^ (64 * (2 * k.toNat)) * c₂ = T₂ at *
      generalize 2 ^ (64 * (3 * k.toNat)) * c₃ = T₃ at *
      generalize 2 ^ (64 * (4 * k.toNat)) * c₄ = T₄ at *
      generalize 2 ^ (64 * (5 * k.toNat)) * c₅ = T₅ at *
      generalize 2 ^ (64 * (6 * k.toNat)) * c₆ = T₆ at *
      lia)
  rw [h5k, a₄₃] at a₅₃
  rw [h5k] at a₅₂
  generalize (addInto ((A₄.uslice r.start r.stop).slice (5 * k) n)
    (q₃₀.toUSlice.slice 0 (min (n - (5 * k)) q₃₀.usize)) 0).1 = A₅ at *
  refine ⟨a₅₁, fun i hi => ?_, ?_⟩
  · rw [a₅₂ i (by lia), a₄₂ i (by lia), a₃₂ i (by lia), a₂₂ i (by lia), a₁₂ i (by lia),
      z₂ i (by lia)]
  · rw [a₅₃]
    lia

/--
The interpolation of degree 5 at `0, 1, …, 4, ∞`: from `c₀` in limbs `[r.start, r.start + 2 k)`
and `c_5` from limb `r.start + 5 k` to `r.start + n`, with `w₁, …, w_4` the values at `1, …, 4`,
writes `c₀ + c₁ x + ⋯ + c_5 x^5` into the `n` limbs from `r.start`, `x = 2^(64 k)`. The values
`(w_j - c₀ - j^5 c_5) / j`, their divided differences and Horner's rule are all in place on the `w`.
-/
public def interp5 (arr : UInt64Array) (r : USlice) (n k : USize) (w₁ w₂ w₃ w₄ : UInt64Array) :
    UInt64Array :=
  let R := arr.uslice r.start r.stop
  let X₀ := R.slice 0 (k + k)
  let Xd := R.slice (5 * k) n
  let w₁ := (subInto w₁.toUSlice X₀).1
  let w₁ := (subInto w₁.toUSlice Xd).1
  let w₂ := (subInto w₂.toUSlice X₀).1
  let w₂ := (subMulInto w₂.toUSlice Xd 32).1
  let w₂ := rshiftInto w₂.toUSlice 1
  let w₃ := (subInto w₃.toUSlice X₀).1
  let w₃ := (subMulInto w₃.toUSlice Xd 243).1
  let w₃ := (divExact3Into w₃.toUSlice).1
  let w₄ := (subInto w₄.toUSlice X₀).1
  let w₄ := (subMulInto w₄.toUSlice Xd 1024).1
  let w₄ := rshiftInto w₄.toUSlice 2
  let w₄ := (subInto w₄.toUSlice w₃.toUSlice).1
  let w₃ := (subInto w₃.toUSlice w₂.toUSlice).1
  let w₂ := (subInto w₂.toUSlice w₁.toUSlice).1
  let w₄ := (subInto w₄.toUSlice w₃.toUSlice).1
  let w₄ := rshiftInto w₄.toUSlice 1
  let w₃ := (subInto w₃.toUSlice w₂.toUSlice).1
  let w₃ := rshiftInto w₃.toUSlice 1
  let w₄ := (subInto w₄.toUSlice w₃.toUSlice).1
  let w₄ := (divExact3Into w₄.toUSlice).1
  let w₃ := (subMulInto w₃.toUSlice w₄.toUSlice 3).1
  let w₂ := (subMulInto w₂.toUSlice w₃.toUSlice 2).1
  let w₃ := (subMulInto w₃.toUSlice w₄.toUSlice 2).1
  let w₁ := (subInto w₁.toUSlice w₂.toUSlice).1
  let w₂ := (subInto w₂.toUSlice w₃.toUSlice).1
  let w₃ := (subInto w₃.toUSlice w₄.toUSlice).1
  -- The recombination.
  let arr := zeroInto ((arr.uslice r.start r.stop).slice (k + k) (5 * k))
  let arr := (addInto ((arr.uslice r.start r.stop).slice k n)
    (w₁.toUSlice.slice 0 (min (n - k) w₁.usize))).1
  let arr := (addInto ((arr.uslice r.start r.stop).slice (k + k) n)
    (w₂.toUSlice.slice 0 (min (n - (k + k)) w₂.usize))).1
  let arr := (addInto ((arr.uslice r.start r.stop).slice (3 * k) n)
    (w₃.toUSlice.slice 0 (min (n - (3 * k)) w₃.usize))).1
  (addInto ((arr.uslice r.start r.stop).slice (4 * k) n)
    (w₄.toUSlice.slice 0 (min (n - (4 * k)) w₄.usize))).1

set_option maxHeartbeats 1000000 in
private theorem interp5_spec (arr : UInt64Array) (r : USlice) (n k : USize)
    (w₁ w₂ w₃ w₄ : UInt64Array) (L c₀ c₁ c₂ c₃ c₄ c₅ : Nat)
    (h : arr.size = r.array.size) (hn : n.toNat ≤ r.size.toNat) (hk : 5 * k.toNat ≤ n.toNat)
    (hk₁ : 1 ≤ k.toNat) (hL : L < USize.size) (hw₁ : w₁.size = L) (hw₂ : w₂.size = L)
        (hw₃ : w₃.size = L) (hw₄ : w₄.size = L)
    (hX₀ : 2 * k.toNat ≤ L) (hXd : n.toNat - 5 * k.toNat ≤ L)
    (hc₀ : arr.valAt r.start.toNat (2 * k.toNat) = c₀)
    (hc₅ : arr.valAt (r.start.toNat + 5 * k.toNat) (n.toNat - 5 * k.toNat) = c₅)
    (hv₁ : w₁.valAt 0 L = c₀ + c₁ + c₂ + c₃ + c₄ + c₅)
    (hv₂ : w₂.valAt 0 L = c₀ + 2 * c₁ + 4 * c₂ + 8 * c₃ + 16 * c₄ + 32 * c₅)
    (hv₃ : w₃.valAt 0 L = c₀ + 3 * c₁ + 9 * c₂ + 27 * c₃ + 81 * c₄ + 243 * c₅)
    (hv₄ : w₄.valAt 0 L = c₀ + 4 * c₁ + 16 * c₂ + 64 * c₃ + 256 * c₄ + 1024 * c₅)
    (htot : c₀ + 2 ^ (64 * k.toNat) * c₁ + 2 ^ (64 * (2 * k.toNat)) * c₂ + 2 ^
        (64 * (3 * k.toNat)) * c₃ + 2 ^ (64 * (4 * k.toNat)) * c₄ + 2 ^ (64 * (5 * k.toNat)) * c₅ <
        2 ^ (64 * n.toNat)) :
    (interp5 arr r n k w₁ w₂ w₃ w₄).size = r.array.size ∧
      (∀ i, (i < r.start.toNat ∨ r.start.toNat + n.toNat ≤ i) →
        (interp5 arr r n k w₁ w₂ w₃ w₄)[i]! = arr[i]!) ∧
      (interp5 arr r n k w₁ w₂ w₃ w₄).valAt r.start.toNat n.toNat =
        c₀ + 2 ^ (64 * k.toNat) * c₁ + 2 ^ (64 * (2 * k.toNat)) * c₂ + 2 ^ (64 * (3 * k.toNat)) *
            c₃ + 2 ^ (64 * (4 * k.toNat)) * c₄ + 2 ^ (64 * (5 * k.toNat)) * c₅ := by
  dsimp only [interp5]
  have hnS := n.toNat_lt_size
  have hkk : (k + k).toNat = 2 * k.toNat := by rw [USize.toNat_add_of_lt (by lia)]; lia
  have h3k : (3 * k).toNat = 3 * k.toNat := toNat_mul_k k 3 (by decide) n (by lia)
  have h4k : (4 * k).toNat = 4 * k.toNat := toNat_mul_k k 4 (by decide) n (by lia)
  have h5k : (5 * k).toNat = 5 * k.toNat := toNat_mul_k k 5 (by decide) n (by lia)
  -- `c₀` and `c_5` in `arr`.
  obtain ⟨x₀₁, x₀₂, x₀₃, x₀₄⟩ := window arr r h (i := 0) (j := k + k) (by simp) (by rw [hkk]; lia)
  obtain ⟨xd₁, xd₂, xd₃, xd₄⟩ := window arr r h (i := 5 * k) (j := n) (by rw [h5k]; lia) hn
  simp only [USize.toNat_zero, Nat.add_zero, Nat.sub_zero, hkk, hc₀] at x₀₃ x₀₄
  rw [h5k, hc₅] at xd₄
  rw [h5k] at xd₃
  generalize (arr.uslice r.start r.stop).slice 0 (k + k) = X₀ at *
  generalize (arr.uslice r.start r.stop).slice (5 * k) n = Xd at *
  obtain ⟨s₁, e₁⟩ := subSl hL w₁ hw₁ X₀ (by rw [x₀₃]; exact hX₀) (R := c₁ + c₂ + c₃ + c₄ + c₅) hv₁
      x₀₄ (by lia)
  generalize (subInto w₁.toUSlice X₀ 0).1 = q₁ at *
  obtain ⟨s₂, e₂⟩ := subSl hL q₁ s₁ Xd (by rw [xd₃]; exact hXd) (R := c₁ + c₂ + c₃ + c₄) e₁ xd₄
      (by lia)
  generalize (subInto q₁.toUSlice Xd 0).1 = q₂ at *
  obtain ⟨s₃, e₃⟩ := subSl hL w₂ hw₂ X₀ (by rw [x₀₃]; exact hX₀)
      (R := 2 * c₁ + 4 * c₂ + 8 * c₃ + 16 * c₄ + 32 * c₅) hv₂ x₀₄ (by lia)
  generalize (subInto w₂.toUSlice X₀ 0).1 = q₃ at *
  obtain ⟨s₄, e₄⟩ := subMulSl hL q₃ s₃ Xd (by rw [xd₃]; exact hXd) 32
      (R := 2 * c₁ + 4 * c₂ + 8 * c₃ + 16 * c₄) e₃ xd₄ rfl (by lia)
  generalize (subMulInto q₃.toUSlice Xd 32).1 = q₄ at *
  obtain ⟨s₅, e₅⟩ := shrW hL q₄ s₄ 1 (by decide) (by decide) (R := c₁ + 2 * c₂ + 4 * c₃ + 8 * c₄)
      rfl e₄ (by lia)
  generalize rshiftInto q₄.toUSlice 1 = q₅ at *
  obtain ⟨s₆, e₆⟩ := subSl hL w₃ hw₃ X₀ (by rw [x₀₃]; exact hX₀)
      (R := 3 * c₁ + 9 * c₂ + 27 * c₃ + 81 * c₄ + 243 * c₅) hv₃ x₀₄ (by lia)
  generalize (subInto w₃.toUSlice X₀ 0).1 = q₆ at *
  obtain ⟨s₇, e₇⟩ := subMulSl hL q₆ s₆ Xd (by rw [xd₃]; exact hXd) 243
      (R := 3 * c₁ + 9 * c₂ + 27 * c₃ + 81 * c₄) e₆ xd₄ rfl (by lia)
  generalize (subMulInto q₆.toUSlice Xd 243).1 = q₇ at *
  obtain ⟨s₈, e₈⟩ := div3W hL q₇ s₇ (R := c₁ + 3 * c₂ + 9 * c₃ + 27 * c₄) e₇ (by lia)
  generalize (divExact3Into q₇.toUSlice).1 = q₈ at *
  obtain ⟨s₉, e₉⟩ := subSl hL w₄ hw₄ X₀ (by rw [x₀₃]; exact hX₀)
      (R := 4 * c₁ + 16 * c₂ + 64 * c₃ + 256 * c₄ + 1024 * c₅) hv₄ x₀₄ (by lia)
  generalize (subInto w₄.toUSlice X₀ 0).1 = q₉ at *
  obtain ⟨s₁₀, e₁₀⟩ := subMulSl hL q₉ s₉ Xd (by rw [xd₃]; exact hXd) 1024
      (R := 4 * c₁ + 16 * c₂ + 64 * c₃ + 256 * c₄) e₉ xd₄ rfl (by lia)
  generalize (subMulInto q₉.toUSlice Xd 1024).1 = q₁₀ at *
  obtain ⟨s₁₁, e₁₁⟩ := shrW hL q₁₀ s₁₀ 2 (by decide) (by decide)
      (R := c₁ + 4 * c₂ + 16 * c₃ + 64 * c₄) rfl e₁₀ (by lia)
  generalize rshiftInto q₁₀.toUSlice 2 = q₁₁ at *
  obtain ⟨s₁₂, e₁₂⟩ := subW hL q₁₁ q₈ s₁₁ s₈ (R := c₂ + 7 * c₃ + 37 * c₄) e₁₁ e₈ (by lia)
  generalize (subInto q₁₁.toUSlice q₈.toUSlice 0).1 = q₁₂ at *
  obtain ⟨s₁₃, e₁₃⟩ := subW hL q₈ q₅ s₈ s₅ (R := c₂ + 5 * c₃ + 19 * c₄) e₈ e₅ (by lia)
  generalize (subInto q₈.toUSlice q₅.toUSlice 0).1 = q₁₃ at *
  obtain ⟨s₁₄, e₁₄⟩ := subW hL q₅ q₂ s₅ s₂ (R := c₂ + 3 * c₃ + 7 * c₄) e₅ e₂ (by lia)
  generalize (subInto q₅.toUSlice q₂.toUSlice 0).1 = q₁₄ at *
  obtain ⟨s₁₅, e₁₅⟩ := subW hL q₁₂ q₁₃ s₁₂ s₁₃ (R := 2 * c₃ + 18 * c₄) e₁₂ e₁₃ (by lia)
  generalize (subInto q₁₂.toUSlice q₁₃.toUSlice 0).1 = q₁₅ at *
  obtain ⟨s₁₆, e₁₆⟩ := shrW hL q₁₅ s₁₅ 1 (by decide) (by decide) (R := c₃ + 9 * c₄) rfl e₁₅ (by lia)
  generalize rshiftInto q₁₅.toUSlice 1 = q₁₆ at *
  obtain ⟨s₁₇, e₁₇⟩ := subW hL q₁₃ q₁₄ s₁₃ s₁₄ (R := 2 * c₃ + 12 * c₄) e₁₃ e₁₄ (by lia)
  generalize (subInto q₁₃.toUSlice q₁₄.toUSlice 0).1 = q₁₇ at *
  obtain ⟨s₁₈, e₁₈⟩ := shrW hL q₁₇ s₁₇ 1 (by decide) (by decide) (R := c₃ + 6 * c₄) rfl e₁₇ (by lia)
  generalize rshiftInto q₁₇.toUSlice 1 = q₁₈ at *
  obtain ⟨s₁₉, e₁₉⟩ := subW hL q₁₆ q₁₈ s₁₆ s₁₈ (R := 3 * c₄) e₁₆ e₁₈ (by lia)
  generalize (subInto q₁₆.toUSlice q₁₈.toUSlice 0).1 = q₁₉ at *
  obtain ⟨s₂₀, e₂₀⟩ := div3W hL q₁₉ s₁₉ (R := c₄) e₁₉ (by lia)
  generalize (divExact3Into q₁₉.toUSlice).1 = q₂₀ at *
  obtain ⟨s₂₁, e₂₁⟩ := subMulW hL q₁₈ q₂₀ s₁₈ s₂₀ 3 (R := c₃ + 3 * c₄) e₁₈ e₂₀ rfl (by lia)
  generalize (subMulInto q₁₈.toUSlice q₂₀.toUSlice 3).1 = q₂₁ at *
  obtain ⟨s₂₂, e₂₂⟩ := subMulW hL q₁₄ q₂₁ s₁₄ s₂₁ 2 (R := c₂ + c₃ + c₄) e₁₄ e₂₁ rfl (by lia)
  generalize (subMulInto q₁₄.toUSlice q₂₁.toUSlice 2).1 = q₂₂ at *
  obtain ⟨s₂₃, e₂₃⟩ := subMulW hL q₂₁ q₂₀ s₂₁ s₂₀ 2 (R := c₃ + c₄) e₂₁ e₂₀ rfl (by lia)
  generalize (subMulInto q₂₁.toUSlice q₂₀.toUSlice 2).1 = q₂₃ at *
  obtain ⟨s₂₄, e₂₄⟩ := subW hL q₂ q₂₂ s₂ s₂₂ (R := c₁) e₂ e₂₂ (by lia)
  generalize (subInto q₂.toUSlice q₂₂.toUSlice 0).1 = q₂₄ at *
  obtain ⟨s₂₅, e₂₅⟩ := subW hL q₂₂ q₂₃ s₂₂ s₂₃ (R := c₂) e₂₂ e₂₃ (by lia)
  generalize (subInto q₂₂.toUSlice q₂₃.toUSlice 0).1 = q₂₅ at *
  obtain ⟨s₂₆, e₂₆⟩ := subW hL q₂₃ q₂₀ s₂₃ s₂₀ (R := c₃) e₂₃ e₂₀ (by lia)
  generalize (subInto q₂₃.toUSlice q₂₀.toUSlice 0).1 = q₂₆ at *
  -- The recombination: clear the middle, then add `c₁`, …, `c_4`.
  obtain ⟨z₁, z₂, z₃⟩ := zero_at arr r h n (k + k) (5 * k) hn (by rw [hkk, h5k]; lia)
    (by rw [h5k]; lia)
  rw [hkk, h5k, hc₀, hc₅] at z₃
  rw [hkk, h5k] at z₂
  generalize zeroInto ((arr.uslice r.start r.stop).slice (k + k) (5 * k)) = A₀ at *
  obtain ⟨a₁₁, a₁₂, a₁₃⟩ := rec_step A₀ r z₁ n k hn (by lia) hL q₂₄ s₂₄ c₁ e₂₄
    (by
      rw [z₃]
      generalize 2 ^ (64 * k.toNat) * c₁ = T₁ at *
      generalize 2 ^ (64 * (2 * k.toNat)) * c₂ = T₂ at *
      generalize 2 ^ (64 * (3 * k.toNat)) * c₃ = T₃ at *
      generalize 2 ^ (64 * (4 * k.toNat)) * c₄ = T₄ at *
      generalize 2 ^ (64 * (5 * k.toNat)) * c₅ = T₅ at *
      lia)
  rw [z₃] at a₁₃
  generalize (addInto ((A₀.uslice r.start r.stop).slice k n)
    (q₂₄.toUSlice.slice 0 (min (n - k) q₂₄.usize)) 0).1 = A₁ at *
  obtain ⟨a₂₁, a₂₂, a₂₃⟩ := rec_step A₁ r a₁₁ n (k + k) hn (by rw [hkk]; lia) hL q₂₅ s₂₅ c₂ e₂₅
    (by
      rw [hkk, a₁₃]
      generalize 2 ^ (64 * k.toNat) * c₁ = T₁ at *
      generalize 2 ^ (64 * (2 * k.toNat)) * c₂ = T₂ at *
      generalize 2 ^ (64 * (3 * k.toNat)) * c₃ = T₃ at *
      generalize 2 ^ (64 * (4 * k.toNat)) * c₄ = T₄ at *
      generalize 2 ^ (64 * (5 * k.toNat)) * c₅ = T₅ at *
      lia)
  rw [hkk, a₁₃] at a₂₃
  rw [hkk] at a₂₂
  generalize (addInto ((A₁.uslice r.start r.stop).slice (k + k) n)
    (q₂₅.toUSlice.slice 0 (min (n - (k + k)) q₂₅.usize)) 0).1 = A₂ at *
  obtain ⟨a₃₁, a₃₂, a₃₃⟩ := rec_step A₂ r a₂₁ n (3 * k) hn (by rw [h3k]; lia) hL q₂₆ s₂₆ c₃ e₂₆
    (by
      rw [h3k, a₂₃]
      generalize 2 ^ (64 * k.toNat) * c₁ = T₁ at *
      generalize 2 ^ (64 * (2 * k.toNat)) * c₂ = T₂ at *
      generalize 2 ^ (64 * (3 * k.toNat)) * c₃ = T₃ at *
      generalize 2 ^ (64 * (4 * k.toNat)) * c₄ = T₄ at *
      generalize 2 ^ (64 * (5 * k.toNat)) * c₅ = T₅ at *
      lia)
  rw [h3k, a₂₃] at a₃₃
  rw [h3k] at a₃₂
  generalize (addInto ((A₂.uslice r.start r.stop).slice (3 * k) n)
    (q₂₆.toUSlice.slice 0 (min (n - (3 * k)) q₂₆.usize)) 0).1 = A₃ at *
  obtain ⟨a₄₁, a₄₂, a₄₃⟩ := rec_step A₃ r a₃₁ n (4 * k) hn (by rw [h4k]; lia) hL q₂₀ s₂₀ c₄ e₂₀
    (by
      rw [h4k, a₃₃]
      generalize 2 ^ (64 * k.toNat) * c₁ = T₁ at *
      generalize 2 ^ (64 * (2 * k.toNat)) * c₂ = T₂ at *
      generalize 2 ^ (64 * (3 * k.toNat)) * c₃ = T₃ at *
      generalize 2 ^ (64 * (4 * k.toNat)) * c₄ = T₄ at *
      generalize 2 ^ (64 * (5 * k.toNat)) * c₅ = T₅ at *
      lia)
  rw [h4k, a₃₃] at a₄₃
  rw [h4k] at a₄₂
  generalize (addInto ((A₃.uslice r.start r.stop).slice (4 * k) n)
    (q₂₀.toUSlice.slice 0 (min (n - (4 * k)) q₂₀.usize)) 0).1 = A₄ at *
  refine ⟨a₄₁, fun i hi => ?_, ?_⟩
  · rw [a₄₂ i (by lia), a₃₂ i (by lia), a₂₂ i (by lia), a₁₂ i (by lia), z₂ i (by lia)]
  · rw [a₄₃]
    lia

/-! ## The three methods -/

/-- A multiplier for products whose sizes add up to less than `N`. -/
public abbrev Mul (N : Nat) : Type :=
  (r a b : USlice) → a.size.toNat + b.size.toNat < N → UInt64Array

/-- The shape of Toom-3: three pieces of `k` limbs each, the top ones nonempty. -/
public abbrev Shape33 (r a b : USlice) (k : USize) : Prop :=
  1 ≤ k.toNat ∧ 2 * k.toNat < a.size.toNat ∧ a.size.toNat ≤ 3 * k.toNat ∧
    2 * k.toNat < b.size.toNat ∧ b.size.toNat ≤ a.size.toNat ∧
    a.size.toNat + b.size.toNat ≤ r.size.toNat

/-- The shape of Toom-4 by 2: four pieces of `a` and two of `b`, the top ones nonempty. -/
public abbrev Shape42 (r a b : USlice) (k : USize) : Prop :=
  1 ≤ k.toNat ∧ 3 * k.toNat < a.size.toNat ∧ a.size.toNat ≤ 4 * k.toNat ∧
    k.toNat < b.size.toNat ∧ b.size.toNat ≤ 2 * k.toNat ∧
    a.size.toNat + b.size.toNat ≤ r.size.toNat

/-- The shape of Toom-3 by 2: three pieces of `a` and two of `b`, the top ones nonempty. -/
public abbrev Shape32 (r a b : USlice) (k : USize) : Prop :=
  1 ≤ k.toNat ∧ 2 * k.toNat < a.size.toNat ∧ a.size.toNat ≤ 3 * k.toNat ∧
    k.toNat < b.size.toNat ∧ b.size.toNat ≤ 2 * k.toNat ∧
    a.size.toNat + b.size.toNat ≤ r.size.toNat

private theorem size_eval3 (x₀ x₁ x₂ : USlice) (len : USize) (j : UInt64) :
    (eval3 x₀ x₁ x₂ len j).size = len.toNat := by
  simp [eval3]

private theorem size_eval4 (x₀ x₁ x₂ x₃ : USlice) (len : USize) (j : UInt64) :
    (eval4 x₀ x₁ x₂ x₃ len j).size = len.toNat := by
  simp [eval4, size_eval3]

private theorem size_eval2 (x₀ x₁ : USlice) (len : USize) (j : UInt64) :
    (eval2 x₀ x₁ len j).size = len.toNat := by
  simp [eval2]

/-- The sizes of the pieces, the windows and the values, as `Nat`s. -/
private theorem toom_sizes {r a b : USlice} {k : USize}
    (hr : a.size.toNat + b.size.toNat ≤ r.size.toNat)
    (hab : 2 * k.toNat + 2 ≤ a.size.toNat + b.size.toNat) :
    (k + k).toNat = 2 * k.toNat ∧ (k + 1).toNat = k.toNat + 1 ∧
      (k + k + 2).toNat = 2 * k.toNat + 2 ∧
      (a.size + b.size).toNat = a.size.toNat + b.size.toNat := by
  have := r.size.toNat_lt_size
  have : 4294967296 ≤ USize.size := by cases USize.size_eq <;> lia
  have h2 : (2 : USize).toNat = 2 := by
    rw [USize.toNat_ofNat, Nat.mod_eq_of_lt (by simp only [USize.size] at this; lia)]
  have hkk : (k + k).toNat = 2 * k.toNat := by rw [USize.toNat_add_of_lt (by lia)]; lia
  refine ⟨hkk, ?_, ?_, USize.toNat_add_of_lt (by lia)⟩
  · rw [USize.toNat_add_of_lt (by rw [USize.toNat_one]; lia), USize.toNat_one]
  · rw [USize.toNat_add_of_lt (by rw [hkk, h2]; lia), hkk, h2]

private theorem eval_toUSlice_size {e : UInt64Array} {len : USize} (he : e.size = len.toNat) :
    e.toUSlice.size.toNat = len.toNat := by
  rw [size_toUSlice _ (by rw [he]; exact len.toNat_lt_size), he]

/-- Toom-3: `a` and `b` in three pieces of `k` limbs, at most, the top pieces nonempty. -/
public def toom33 (r a b : USlice) (k : USize) (hk : Shape33 r a b k)
    (mul : Mul (a.size.toNat + b.size.toNat)) : UInt64Array :=
  have hs := toom_sizes (r := r) (k := k) hk.2.2.2.2.2 (by lia)
  let n := a.size + b.size
  let a₀ := a.slice 0 k
  let a₁ := a.slice k (k + k)
  let a₂ := a.slice (k + k) a.size
  let b₀ := b.slice 0 k
  let b₁ := b.slice k (k + k)
  let b₂ := b.slice (k + k) b.size
  let arr := mul (r.slice 0 (k + k)) a₀ b₀ (by
    rw [USlice.size_slice _ (by simp) (by lia), USlice.size_slice _ (by simp) (by lia),
      USize.toNat_zero]; lia)
  let arr := mul ((arr.uslice r.start r.stop).slice (4 * k) n) a₂ b₂ (by
    rw [USlice.size_slice _ (by rw [hs.1]; lia) (Nat.le_refl _),
      USlice.size_slice _ (by rw [hs.1]; lia) (Nat.le_refl _), hs.1]; lia)
  let w (j : UInt64) := mul (UInt64Array.replicate (k + k + 2).toNat 0).toUSlice
    (eval3 a₀ a₁ a₂ (k + 1) j).toUSlice (eval3 b₀ b₁ b₂ (k + 1) j).toUSlice (by
      rw [eval_toUSlice_size (size_eval3 ..), eval_toUSlice_size (size_eval3 ..), hs.2.1]; lia)
  interp4 arr r n k (w 1) (w 2) (w 3)

/-- Toom-4 by 2: `a` in four pieces of `k` limbs and `b` in two, the top pieces nonempty. -/
public def toom42 (r a b : USlice) (k : USize) (hk : Shape42 r a b k)
    (mul : Mul (a.size.toNat + b.size.toNat)) : UInt64Array :=
  have hs := toom_sizes (r := r) (k := k) hk.2.2.2.2.2 (by lia)
  have h3k : (3 * k).toNat = 3 * k.toNat := toNat_mul_k k 3 (by decide) a.size (by lia)
  let n := a.size + b.size
  let a₀ := a.slice 0 k
  let a₁ := a.slice k (k + k)
  let a₂ := a.slice (k + k) (3 * k)
  let a₃ := a.slice (3 * k) a.size
  let b₀ := b.slice 0 k
  let b₁ := b.slice k b.size
  let arr := mul (r.slice 0 (k + k)) a₀ b₀ (by
    rw [USlice.size_slice _ (by simp) (by lia), USlice.size_slice _ (by simp) (by lia),
      USize.toNat_zero]; lia)
  let arr := mul ((arr.uslice r.start r.stop).slice (4 * k) n) a₃ b₁ (by
    rw [USlice.size_slice _ (by rw [h3k]; lia) (Nat.le_refl _),
      USlice.size_slice _ (by lia) (Nat.le_refl _), h3k]; lia)
  let w (j : UInt64) := mul (UInt64Array.replicate (k + k + 2).toNat 0).toUSlice
    (eval4 a₀ a₁ a₂ a₃ (k + 1) j).toUSlice (eval2 b₀ b₁ (k + 1) j).toUSlice (by
      rw [eval_toUSlice_size (size_eval4 ..), eval_toUSlice_size (size_eval2 ..), hs.2.1]; lia)
  interp4 arr r n k (w 1) (w 2) (w 3)

/-- Toom-3 by 2: `a` in three pieces of `k` limbs and `b` in two, the top pieces nonempty. -/
public def toom32 (r a b : USlice) (k : USize) (hk : Shape32 r a b k)
    (mul : Mul (a.size.toNat + b.size.toNat)) : UInt64Array :=
  have hs := toom_sizes (r := r) (k := k) hk.2.2.2.2.2 (by lia)
  let n := a.size + b.size
  let a₀ := a.slice 0 k
  let a₁ := a.slice k (k + k)
  let a₂ := a.slice (k + k) a.size
  let b₀ := b.slice 0 k
  let b₁ := b.slice k b.size
  let arr := mul (r.slice 0 (k + k)) a₀ b₀ (by
    rw [USlice.size_slice _ (by simp) (by lia), USlice.size_slice _ (by simp) (by lia),
      USize.toNat_zero]; lia)
  let arr := mul ((arr.uslice r.start r.stop).slice (3 * k) n) a₂ b₁ (by
    rw [USlice.size_slice _ (by rw [hs.1]; lia) (Nat.le_refl _),
      USlice.size_slice _ (by lia) (Nat.le_refl _), hs.1]; lia)
  let w (j : UInt64) := mul (UInt64Array.replicate (k + k + 2).toNat 0).toUSlice
    (eval3 a₀ a₁ a₂ (k + 1) j).toUSlice (eval2 b₀ b₁ (k + 1) j).toUSlice (by
      rw [eval_toUSlice_size (size_eval3 ..), eval_toUSlice_size (size_eval2 ..), hs.2.1]; lia)
  interp3 arr r n k (w 1) (w 2)

/-- The shape of Toom-4: four pieces of `a` and of `b`, the top ones nonempty. -/
public abbrev Shape44 (r a b : USlice) (k : USize) : Prop :=
  1 ≤ k.toNat ∧ 3 * k.toNat < a.size.toNat ∧ a.size.toNat ≤ 4 * k.toNat ∧
    3 * k.toNat < b.size.toNat ∧ b.size.toNat ≤ a.size.toNat ∧
    a.size.toNat + b.size.toNat ≤ r.size.toNat

/-- The shape of Toom-4 by 3: four pieces of `a` and three of `b`, the top ones nonempty. -/
public abbrev Shape43 (r a b : USlice) (k : USize) : Prop :=
  1 ≤ k.toNat ∧ 3 * k.toNat < a.size.toNat ∧ a.size.toNat ≤ 4 * k.toNat ∧
    2 * k.toNat < b.size.toNat ∧ b.size.toNat ≤ 3 * k.toNat ∧
    a.size.toNat + b.size.toNat ≤ r.size.toNat

/-- Toom-4: `a` and `b` in four pieces of `k` limbs, at most, the top pieces nonempty. -/
public def toom44 (r a b : USlice) (k : USize) (hk : Shape44 r a b k)
    (mul : Mul (a.size.toNat + b.size.toNat)) : UInt64Array :=
  have hs := toom_sizes (r := r) (k := k) hk.2.2.2.2.2 (by lia)
  have h3k : (3 * k).toNat = 3 * k.toNat := toNat_mul_k k 3 (by decide) a.size (by lia)
  have h6k : (6 * k).toNat = 6 * k.toNat := toNat_mul_k k 6 (by decide) r.size (by lia)
  let n := a.size + b.size
  let a₀ := a.slice 0 k
  let a₁ := a.slice k (k + k)
  let a₂ := a.slice (k + k) (3 * k)
  let a₃ := a.slice (3 * k) a.size
  let b₀ := b.slice 0 k
  let b₁ := b.slice k (k + k)
  let b₂ := b.slice (k + k) (3 * k)
  let b₃ := b.slice (3 * k) b.size
  let arr := mul (r.slice 0 (k + k)) a₀ b₀ (by
    rw [USlice.size_slice _ (by simp) (by lia), USlice.size_slice _ (by simp) (by lia),
      USize.toNat_zero]; lia)
  let arr := mul ((arr.uslice r.start r.stop).slice (6 * k) n) a₃ b₃ (by
    rw [USlice.size_slice _ (by rw [h3k]; lia) (Nat.le_refl _),
      USlice.size_slice _ (by rw [h3k]; lia) (Nat.le_refl _), h3k]; lia)
  let w (j : UInt64) := mul (UInt64Array.replicate (k + k + 2).toNat 0).toUSlice
    (eval4 a₀ a₁ a₂ a₃ (k + 1) j).toUSlice (eval4 b₀ b₁ b₂ b₃ (k + 1) j).toUSlice (by
      rw [eval_toUSlice_size (size_eval4 ..), eval_toUSlice_size (size_eval4 ..), hs.2.1]; lia)
  interp6 arr r n k (w 1) (w 2) (w 3) (w 4) (w 5)

/-- Toom-4 by 3: `a` in four pieces of `k` limbs and `b` in three, the top pieces nonempty. -/
public def toom43 (r a b : USlice) (k : USize) (hk : Shape43 r a b k)
    (mul : Mul (a.size.toNat + b.size.toNat)) : UInt64Array :=
  have hs := toom_sizes (r := r) (k := k) hk.2.2.2.2.2 (by lia)
  have h3k : (3 * k).toNat = 3 * k.toNat := toNat_mul_k k 3 (by decide) a.size (by lia)
  let n := a.size + b.size
  let a₀ := a.slice 0 k
  let a₁ := a.slice k (k + k)
  let a₂ := a.slice (k + k) (3 * k)
  let a₃ := a.slice (3 * k) a.size
  let b₀ := b.slice 0 k
  let b₁ := b.slice k (k + k)
  let b₂ := b.slice (k + k) b.size
  let arr := mul (r.slice 0 (k + k)) a₀ b₀ (by
    rw [USlice.size_slice _ (by simp) (by lia), USlice.size_slice _ (by simp) (by lia),
      USize.toNat_zero]; lia)
  let arr := mul ((arr.uslice r.start r.stop).slice (5 * k) n) a₃ b₂ (by
    rw [USlice.size_slice _ (by rw [h3k]; lia) (Nat.le_refl _),
      USlice.size_slice _ (by rw [hs.1]; lia) (Nat.le_refl _), h3k, hs.1]; lia)
  let w (j : UInt64) := mul (UInt64Array.replicate (k + k + 2).toNat 0).toUSlice
    (eval4 a₀ a₁ a₂ a₃ (k + 1) j).toUSlice (eval3 b₀ b₁ b₂ (k + 1) j).toUSlice (by
      rw [eval_toUSlice_size (size_eval4 ..), eval_toUSlice_size (size_eval3 ..), hs.2.1]; lia)
  interp5 arr r n k (w 1) (w 2) (w 3) (w 4)

/-! ### Correctness of the methods -/

/-- What a multiplication of `a` by `b` into `r` guarantees: the result `R`. -/
public def MulOK (R : UInt64Array) (r a b : USlice) : Prop :=
  R.size = r.array.size ∧
    (∀ i, (i < r.start.toNat ∨ r.start.toNat + a.size.toNat + b.size.toNat ≤ i) →
      R[i]! = r.array[i]!) ∧
    (0 < a.size → 0 < b.size → a.size.toNat + b.size.toNat ≤ r.size.toNat →
      R.valAt r.start.toNat (a.size.toNat + b.size.toNat) = a.toNat * b.toNat)

/-- A piece of `a`, the limbs from `i` to `j`. -/
private theorem piece (a : USlice) {i j : USize} (hij : i.toNat ≤ j.toNat)
    (hj : j.toNat ≤ a.size.toNat) :
    (a.slice i j).size.toNat = j.toNat - i.toNat ∧
      (a.slice i j).toNat = a.array.valAt (a.start.toNat + i.toNat) (j.toNat - i.toNat) :=
  ⟨a.size_slice hij hj, a.toNat_slice hij hj⟩

/-- A piece of at most `K` limbs is less than `2^(64 K)`. -/
private theorem slice_lt (x : USlice) {K : Nat} (h : x.size.toNat ≤ K) :
    x.toNat < 2 ^ (64 * K) := by
  rw [USlice.toNat_eq_valAt]
  exact Nat.lt_of_lt_of_le (valAt_lt ..) (Nat.pow_le_pow_right (by decide) (by lia))

private theorem pow_succ_k (K : Nat) : 2 ^ (64 * (K + 1)) = 2 ^ (64 * K) * 2 ^ 64 := by
  rw [Nat.mul_succ, Nat.pow_add]

/-- The evaluation of three pieces of at most `k` limbs at `j ≤ 5`. -/
private theorem eval3_at (x₀ x₁ x₂ : USlice) (k : USize) (j : UInt64)
    (hk : (k + 1).toNat = k.toNat + 1) (h₀ : x₀.size.toNat ≤ k.toNat)
    (h₁ : x₁.size.toNat ≤ k.toNat) (h₂ : x₂.size.toNat ≤ k.toNat) (hj : j.toNat ≤ 5) :
    (eval3 x₀ x₁ x₂ (k + 1) j).valAt 0 (k.toNat + 1) =
      x₀.toNat + x₁.toNat * j.toNat + x₂.toNat * (j.toNat * j.toNat) := by
  have l₀ := slice_lt x₀ h₀
  have l₁ := slice_lt x₁ h₁
  have l₂ := slice_lt x₂ h₂
  have m₁ := Nat.mul_le_mul_left x₁.toNat hj
  have m₂ := Nat.mul_le_mul_left x₂.toNat (Nat.mul_le_mul hj hj)
  rw [← hk]
  refine (eval3_spec x₀ x₁ x₂ (k + 1) j (USize.le_iff_toNat_le.2 (by lia))
    (USize.le_iff_toNat_le.2 (by lia)) (USize.le_iff_toNat_le.2 (by lia)) (by lia) ?_).2
  rw [hk, pow_succ_k]; lia

/-- The evaluation of four pieces of at most `k` limbs at `j ≤ 5`. -/
private theorem eval4_at (x₀ x₁ x₂ x₃ : USlice) (k : USize) (j : UInt64)
    (hk : (k + 1).toNat = k.toNat + 1) (h₀ : x₀.size.toNat ≤ k.toNat)
    (h₁ : x₁.size.toNat ≤ k.toNat) (h₂ : x₂.size.toNat ≤ k.toNat) (h₃ : x₃.size.toNat ≤ k.toNat)
    (hj : j.toNat ≤ 5) :
    (eval4 x₀ x₁ x₂ x₃ (k + 1) j).valAt 0 (k.toNat + 1) =
      x₀.toNat + x₁.toNat * j.toNat + x₂.toNat * (j.toNat * j.toNat) +
        x₃.toNat * (j.toNat * j.toNat * j.toNat) := by
  have l₀ := slice_lt x₀ h₀
  have l₁ := slice_lt x₁ h₁
  have l₂ := slice_lt x₂ h₂
  have l₃ := slice_lt x₃ h₃
  have m₁ := Nat.mul_le_mul_left x₁.toNat hj
  have m₂ := Nat.mul_le_mul_left x₂.toNat (Nat.mul_le_mul hj hj)
  have m₃ := Nat.mul_le_mul_left x₃.toNat (Nat.mul_le_mul (Nat.mul_le_mul hj hj) hj)
  rw [← hk]
  refine (eval4_spec x₀ x₁ x₂ x₃ (k + 1) j (USize.le_iff_toNat_le.2 (by lia))
    (USize.le_iff_toNat_le.2 (by lia)) (USize.le_iff_toNat_le.2 (by lia))
    (USize.le_iff_toNat_le.2 (by lia)) (by lia) ?_).2
  rw [hk, pow_succ_k]; lia

/-- The evaluation of two pieces of at most `k` limbs at `j ≤ 5`. -/
private theorem eval2_at (x₀ x₁ : USlice) (k : USize) (j : UInt64)
    (hk : (k + 1).toNat = k.toNat + 1) (h₀ : x₀.size.toNat ≤ k.toNat)
    (h₁ : x₁.size.toNat ≤ k.toNat) (hj : j.toNat ≤ 5) :
    (eval2 x₀ x₁ (k + 1) j).valAt 0 (k.toNat + 1) = x₀.toNat + x₁.toNat * j.toNat := by
  have l₀ := slice_lt x₀ h₀
  have l₁ := slice_lt x₁ h₁
  have m₁ := Nat.mul_le_mul_left x₁.toNat hj
  rw [← hk]
  refine (eval2_spec x₀ x₁ (k + 1) j (USize.le_iff_toNat_le.2 (by lia))
    (USize.le_iff_toNat_le.2 (by lia)) ?_).2
  rw [hk, pow_succ_k]; lia

/-- The product of two evaluations, into a new array of `2 k + 2` limbs. -/
private theorem prod_at {N : Nat} (mul : Mul N)
    (hmul : ∀ r' a' b' h', MulOK (mul r' a' b' h') r' a' b') (k : USize)
    (hk : (k + 1).toNat = k.toNat + 1) (hkk : (k + k + 2).toNat = 2 * k.toNat + 2)
    (EA EB : UInt64Array) (hA : EA.size = (k + 1).toNat) (hB : EB.size = (k + 1).toNat)
    (h : EA.toUSlice.size.toNat + EB.toUSlice.size.toNat < N) :
    (mul (UInt64Array.replicate (k + k + 2).toNat 0).toUSlice EA.toUSlice EB.toUSlice h).size =
        2 * k.toNat + 2 ∧
      (mul (UInt64Array.replicate (k + k + 2).toNat 0).toUSlice EA.toUSlice EB.toUSlice h).valAt
        0 (2 * k.toNat + 2) = EA.valAt 0 (k.toNat + 1) * EB.valAt 0 (k.toNat + 1) := by
  obtain ⟨z₁, z₂, -, z₄⟩ := zeros (k + k + 2)
  obtain ⟨s, -, v⟩ := hmul (UInt64Array.replicate (k + k + 2).toNat 0).toUSlice EA.toUSlice
    EB.toUSlice h
  have hS := (k + 1).toNat_lt_size
  have sA := size_toUSlice EA (by rw [hA]; exact hS)
  have sB := size_toUSlice EB (by rw [hB]; exact hS)
  rw [UInt64Array.array_toUSlice, z₄] at s
  rw [z₁, sA, sB, hA, hB, hk, toUSlice_toNat _ (by rw [hA]; exact hS),
    toUSlice_toNat _ (by rw [hB]; exact hS), UInt64Array.toNat_eq_valAt,
    UInt64Array.toNat_eq_valAt, hA, hB, hk, show k.toNat + 1 + (k.toNat + 1) =
      2 * k.toNat + 2 by lia] at v
  refine ⟨s.trans hkk, v ?_ ?_ ?_⟩
  · exact USize.lt_iff_toNat_lt.2 (by rw [sA, hA, hk, USize.toNat_zero]; lia)
  · exact USize.lt_iff_toNat_lt.2 (by rw [sB, hB, hk, USize.toNat_zero]; lia)
  · rw [z₂, hkk]; lia

/-- A slice of `a` from `i` to its end, split at `j`. -/
private theorem toNat_split (a : USlice) {i j : USize} (hij : i.toNat ≤ j.toNat)
    (hj : j.toNat ≤ a.size.toNat) :
    (a.slice i a.size).toNat =
      (a.slice i j).toNat + 2 ^ (64 * (j.toNat - i.toNat)) * (a.slice j a.size).toNat := by
  rw [a.toNat_slice hij hj, a.toNat_slice (Nat.le_trans hij hj) (Nat.le_refl _),
    a.toNat_slice hj (Nat.le_refl _),
    show a.size.toNat - i.toNat = (j.toNat - i.toNat) + (a.size.toNat - j.toNat) by lia,
    UInt64Array.valAt_add, show a.start.toNat + i.toNat + (j.toNat - i.toNat) =
      a.start.toNat + j.toNat by lia]

private theorem toNat_whole (a : USlice) : a.toNat = (a.slice 0 a.size).toNat := by
  rw [a.toNat_slice (by simp) (Nat.le_refl _), USlice.toNat_eq_valAt]; simp

private theorem toom33_spec (r a b : USlice) (k : USize) (hk : Shape33 r a b k)
    (mul : Mul (a.size.toNat + b.size.toNat))
    (hmul : ∀ r' a' b' h', MulOK (mul r' a' b' h') r' a' b') :
    MulOK (toom33 r a b k hk mul) r a b := by
  obtain ⟨hk₁, ha₁, ha₂, hb₁, hba, hr⟩ := hk
  obtain ⟨hkk, hk1, hkk2, hn⟩ := toom_sizes (r := r) (k := k) hr (by lia)
  have hnS := r.size.toNat_lt_size
  have hT : (4 * k).toNat = 4 * k.toNat := toNat_mul_k k 4 (by decide) r.size (by lia)
  have h3k : (3 * k).toNat = 3 * k.toNat := toNat_mul_k k 3 (by decide) r.size (by lia)
  dsimp only [toom33]
  -- The pieces.
  have pa₀ := (a.size_slice (i := 0) (j := k) (by simp) (by lia) :)
  have pa₁ := (a.size_slice (i := k) (j := (k + k)) (by lia) (by lia) :)
  have pa₂ := (a.size_slice (i := (k + k)) (j := a.size) (by lia) (Nat.le_refl _) :)
  simp only [USize.toNat_zero, Nat.sub_zero, hkk] at pa₀ pa₁ pa₂
  have hA := toNat_whole a
  rw [toNat_split a (i := 0) (j := k) (by simp) (by lia)] at hA
  rw [toNat_split a (i := k) (j := (k + k)) (by lia) (by lia)] at hA
  simp only [USize.toNat_zero, Nat.sub_zero, hkk,
    show 2 * k.toNat - k.toNat = k.toNat by lia] at hA
  have hA₀ := slice_lt (a.slice 0 k) (K := k.toNat) (by lia)
  have hA₁ := slice_lt (a.slice k (k + k)) (K := k.toNat) (by lia)
  have hA₂ := slice_lt (a.slice (k + k) a.size) (K := k.toNat) (by lia)
  generalize eA₀ : (a.slice 0 k).toNat = A₀ at *
  generalize eA₁ : (a.slice k (k + k)).toNat = A₁ at *
  generalize eA₂ : (a.slice (k + k) a.size).toNat = A₂ at *
  have pb₀ := (b.size_slice (i := 0) (j := k) (by simp) (by lia) :)
  have pb₁ := (b.size_slice (i := k) (j := (k + k)) (by lia) (by lia) :)
  have pb₂ := (b.size_slice (i := (k + k)) (j := b.size) (by lia) (Nat.le_refl _) :)
  simp only [USize.toNat_zero, Nat.sub_zero, hkk] at pb₀ pb₁ pb₂
  have hB := toNat_whole b
  rw [toNat_split b (i := 0) (j := k) (by simp) (by lia)] at hB
  rw [toNat_split b (i := k) (j := (k + k)) (by lia) (by lia)] at hB
  simp only [USize.toNat_zero, Nat.sub_zero, hkk,
    show 2 * k.toNat - k.toNat = k.toNat by lia] at hB
  have hB₀ := slice_lt (b.slice 0 k) (K := k.toNat) (by lia)
  have hB₁ := slice_lt (b.slice k (k + k)) (K := k.toNat) (by lia)
  have hB₂ := slice_lt (b.slice (k + k) b.size) (K := k.toNat) (by lia)
  generalize eB₀ : (b.slice 0 k).toNat = B₀ at *
  generalize eB₁ : (b.slice k (k + k)).toNat = B₁ at *
  generalize eB₂ : (b.slice (k + k) b.size).toNat = B₂ at *
  -- `c₀ = a₀ b₀` into the low limbs of `r`.
  have hd₁ : (a.slice 0 k).size.toNat + (b.slice 0 k).size.toNat <
      a.size.toNat + b.size.toNat := by lia
  obtain ⟨m₁s, m₁u, m₁v⟩ := hmul (r.slice 0 (k + k)) (a.slice 0 k) (b.slice 0 k) hd₁
  have hW₀s := r.start_slice (i := 0) (j := k + k) (by simp) (by lia)
  have hW₀z := r.size_slice (i := 0) (j := k + k) (by simp) (by lia)
  simp only [USize.toNat_zero, Nat.add_zero, Nat.sub_zero, hkk] at hW₀s hW₀z
  simp only [USlice.array_slice] at m₁s m₁u m₁v
  rw [hW₀s, pa₀, pb₀] at m₁u m₁v
  rw [hW₀z, eA₀, eB₀] at m₁v
  replace m₁v := m₁v (USize.lt_iff_toNat_lt.2 (by rw [pa₀, USize.toNat_zero]; lia))
    (USize.lt_iff_toNat_lt.2 (by rw [pb₀, USize.toNat_zero]; lia)) (by lia)
  generalize mul (r.slice 0 (k + k)) (a.slice 0 k) (b.slice 0 k) hd₁ = R₁ at *
  -- The top coefficient into the top limbs.
  obtain ⟨x₁, x₂, x₃, -⟩ := window R₁ r m₁s (i := 4 * k) (j := a.size + b.size)
    (by rw [hT, hn]; lia) (by rw [hn]; lia)
  rw [hT] at x₂ x₃
  rw [hn] at x₃
  have hd₂ : (a.slice (k + k) a.size).size.toNat + (b.slice (k + k) b.size).size.toNat <
      a.size.toNat + b.size.toNat := by lia
  obtain ⟨m₂s, m₂u, m₂v⟩ := hmul ((R₁.uslice r.start r.stop).slice (4 * k) (a.size + b.size))
    (a.slice (k + k) a.size) (b.slice (k + k) b.size) hd₂
  rw [x₁, m₁s] at m₂s
  rw [x₁, x₂, pa₂, pb₂] at m₂u
  rw [x₂, x₃, pa₂, pb₂, eA₂, eB₂] at m₂v
  replace m₂v := m₂v (USize.lt_iff_toNat_lt.2 (by rw [pa₂, USize.toNat_zero]; lia))
    (USize.lt_iff_toNat_lt.2 (by rw [pb₂, USize.toNat_zero]; lia)) (by lia)
  generalize mul ((R₁.uslice r.start r.stop).slice (4 * k) (a.size + b.size))
    (a.slice (k + k) a.size) (b.slice (k + k) b.size) hd₂ = R₂ at *
  have hc₀ : R₂.valAt r.start.toNat (2 * k.toNat) = A₀ * B₀ := by
    rw [← m₁v, show k.toNat + k.toNat = 2 * k.toNat by lia]
    exact UInt64Array.valAt_congr _ fun i _ hi => m₂u i (by lia)
  have hc₄ : R₂.valAt (r.start.toNat + 4 * k.toNat)
      ((a.size + b.size).toNat - 4 * k.toNat) = A₂ * B₂ := by
    rw [← m₂v, hn]; congr 1; lia
  -- The evaluations and their products.
  have pA (j : UInt64) (hj : j.toNat ≤ 5) :=
    eval3_at (a.slice 0 k) (a.slice k (k + k)) (a.slice (k + k) a.size)
       k j hk1
      (by lia) (by lia) (by lia) hj
  have pB (j : UInt64) (hj : j.toNat ≤ 5) :=
    eval3_at (b.slice 0 k) (b.slice k (k + k)) (b.slice (k + k) b.size) k j hk1
      (by lia) (by lia) (by lia) hj
  rw [eA₀, eA₁, eA₂] at pA
  rw [eB₀, eB₁, eB₂] at pB
  have hdw (EA EB : UInt64Array) (hA' : EA.size = (k + 1).toNat) (hB' : EB.size = (k + 1).toNat) :
      EA.toUSlice.size.toNat + EB.toUSlice.size.toNat < a.size.toNat + b.size.toNat := by
    rw [eval_toUSlice_size hA', eval_toUSlice_size hB', hk1]; lia
  obtain ⟨w1s, w1v⟩ := prod_at mul hmul k hk1 hkk2
    (eval3 (a.slice 0 k) (a.slice k (k + k)) (a.slice (k + k) a.size) (k + 1) 1)
    (eval3 (b.slice 0 k) (b.slice k (k + k)) (b.slice (k + k) b.size) (k + 1) 1)
    (size_eval3 ..) (size_eval3 ..) (hdw _ _ (size_eval3 ..) (size_eval3 ..))
  rw [pA 1 (by decide), pB 1 (by decide)] at w1v
  obtain ⟨w2s, w2v⟩ := prod_at mul hmul k hk1 hkk2
    (eval3 (a.slice 0 k) (a.slice k (k + k)) (a.slice (k + k) a.size) (k + 1) 2)
    (eval3 (b.slice 0 k) (b.slice k (k + k)) (b.slice (k + k) b.size) (k + 1) 2)
    (size_eval3 ..) (size_eval3 ..) (hdw _ _ (size_eval3 ..) (size_eval3 ..))
  rw [pA 2 (by decide), pB 2 (by decide)] at w2v
  obtain ⟨w3s, w3v⟩ := prod_at mul hmul k hk1 hkk2
    (eval3 (a.slice 0 k) (a.slice k (k + k)) (a.slice (k + k) a.size) (k + 1) 3)
    (eval3 (b.slice 0 k) (b.slice k (k + k)) (b.slice (k + k) b.size) (k + 1) 3)
    (size_eval3 ..) (size_eval3 ..) (hdw _ _ (size_eval3 ..) (size_eval3 ..))
  rw [pA 3 (by decide), pB 3 (by decide)] at w3v
  simp only [show (1 : UInt64).toNat = 1 from rfl,
    show (2 : UInt64).toNat = 2 from rfl,
    show (3 : UInt64).toNat = 3 from rfl] at w1v w2v w3v
  -- The interpolation.
  generalize hX : 2 ^ (64 * k.toNat) = X at *
  have hXX : 2 ^ (64 * (2 * k.toNat)) = X * X := by rw [← hX, ← Nat.pow_add]; congr 1; lia
  have hX3 : 2 ^ (64 * (3 * k.toNat)) = X * X * X := by
    rw [← hX, ← Nat.pow_add, ← Nat.pow_add]; congr 1; lia
  have hX4 : 2 ^ (64 * (4 * k.toNat)) = X * X * X * X := by
    rw [← hX, ← Nat.pow_add, ← Nat.pow_add, ← Nat.pow_add]; congr 1; lia
  have hval : a.toNat * b.toNat =
      A₀ * B₀ +
      X * (A₀ * B₁ + A₁ * B₀) +
      X * X * (A₀ * B₂ + A₁ * B₁ + A₂ * B₀) +
      X * X * X * (A₁ * B₂ + A₂ * B₁) +
      X * X * X * X * (A₂ * B₂) := by
    rw [hA, hB]; grind
  have hab : a.toNat * b.toNat < 2 ^ (64 * (a.size.toNat + b.size.toNat)) := by
    rw [Nat.mul_add, Nat.pow_add]
    exact Nat.mul_lt_mul_of_lt_of_lt (slice_lt a (Nat.le_refl _)) (slice_lt b (Nat.le_refl _))
  have hbm : (A₀ + A₁ * 3 + A₂ * (3 * 3)) * (B₀ + B₁ * 3 + B₂ * (3 * 3)) <
      2 ^ (64 * (2 * k.toNat + 2 - 1)) := by
    rw [show 2 * k.toNat + 2 - 1 = 2 * k.toNat + 1 by lia, pow_succ_k, hXX]
    have := Nat.mul_lt_mul_of_lt_of_lt
      (show A₀ + A₁ * 3 + A₂ * (3 * 3) < 13 * X by lia)
      (show B₀ + B₁ * 3 + B₂ * (3 * 3) < 13 * X by lia)
    rw [show 13 * X * (13 * X) = 169 * (X * X) by grind] at this
    generalize X * X = Y at *
    lia
  obtain ⟨f₁, f₂, f₃⟩ := interp4_spec R₂ r (a.size + b.size) k _ _ _ (2 * k.toNat + 2)
    (A₀ * B₀) (A₀ * B₁ + A₁ * B₀) (A₀ * B₂ + A₁ * B₁ + A₂ * B₀) (A₁ * B₂ + A₂ * B₁) (A₂ * B₂)
    m₂s (by rw [hn]; lia) (by rw [hn]; lia) hk₁ (by have := (k + k + 2).toNat_lt_size; lia)
    (by lia) w1s w2s w3s (by lia) (by rw [hn]; lia) hc₀ hc₄
    (by rw [w1v]; grind)
    (by rw [w2v]; grind)
    (by rw [w3v]; grind)
    (by refine Nat.lt_of_le_of_lt (Nat.le_of_eq ?_) hbm; grind)
    (by rw [hX, hXX, hX3, hX4, hn, ← hval]; exact hab)
  rw [hn, hX, hXX, hX3, hX4, ← hval] at f₃
  refine ⟨f₁, fun i hi => ?_, fun _ _ _ => f₃⟩
  rw [f₂ i (by rw [hn]; lia), m₂u i (by lia), m₁u i (by lia)]

private theorem toom42_spec (r a b : USlice) (k : USize) (hk : Shape42 r a b k)
    (mul : Mul (a.size.toNat + b.size.toNat))
    (hmul : ∀ r' a' b' h', MulOK (mul r' a' b' h') r' a' b') :
    MulOK (toom42 r a b k hk mul) r a b := by
  obtain ⟨hk₁, ha₁, ha₂, hb₁, hba, hr⟩ := hk
  obtain ⟨hkk, hk1, hkk2, hn⟩ := toom_sizes (r := r) (k := k) hr (by lia)
  have hnS := r.size.toNat_lt_size
  have hT : (4 * k).toNat = 4 * k.toNat := toNat_mul_k k 4 (by decide) r.size (by lia)
  have h3k : (3 * k).toNat = 3 * k.toNat := toNat_mul_k k 3 (by decide) r.size (by lia)
  dsimp only [toom42]
  -- The pieces.
  have pa₀ := (a.size_slice (i := 0) (j := k) (by simp) (by lia) :)
  have pa₁ := (a.size_slice (i := k) (j := (k + k)) (by lia) (by lia) :)
  have pa₂ := (a.size_slice (i := (k + k)) (j := (3 * k)) (by lia) (by lia) :)
  have pa₃ := (a.size_slice (i := (3 * k)) (j := a.size) (by lia) (Nat.le_refl _) :)
  simp only [USize.toNat_zero, Nat.sub_zero, hkk, h3k] at pa₀ pa₁ pa₂ pa₃
  have hA := toNat_whole a
  rw [toNat_split a (i := 0) (j := k) (by simp) (by lia)] at hA
  rw [toNat_split a (i := k) (j := (k + k)) (by lia) (by lia)] at hA
  rw [toNat_split a (i := (k + k)) (j := (3 * k)) (by lia) (by lia)] at hA
  simp only [USize.toNat_zero, Nat.sub_zero, hkk, h3k,
    show 2 * k.toNat - k.toNat = k.toNat by lia,
    show 3 * k.toNat - 2 * k.toNat = k.toNat by lia] at hA
  have hA₀ := slice_lt (a.slice 0 k) (K := k.toNat) (by lia)
  have hA₁ := slice_lt (a.slice k (k + k)) (K := k.toNat) (by lia)
  have hA₂ := slice_lt (a.slice (k + k) (3 * k)) (K := k.toNat) (by lia)
  have hA₃ := slice_lt (a.slice (3 * k) a.size) (K := k.toNat) (by lia)
  generalize eA₀ : (a.slice 0 k).toNat = A₀ at *
  generalize eA₁ : (a.slice k (k + k)).toNat = A₁ at *
  generalize eA₂ : (a.slice (k + k) (3 * k)).toNat = A₂ at *
  generalize eA₃ : (a.slice (3 * k) a.size).toNat = A₃ at *
  have pb₀ := (b.size_slice (i := 0) (j := k) (by simp) (by lia) :)
  have pb₁ := (b.size_slice (i := k) (j := b.size) (by lia) (Nat.le_refl _) :)
  simp only [USize.toNat_zero, Nat.sub_zero] at pb₀ pb₁
  have hB := toNat_whole b
  rw [toNat_split b (i := 0) (j := k) (by simp) (by lia)] at hB
  simp only [USize.toNat_zero, Nat.sub_zero] at hB
  have hB₀ := slice_lt (b.slice 0 k) (K := k.toNat) (by lia)
  have hB₁ := slice_lt (b.slice k b.size) (K := k.toNat) (by lia)
  generalize eB₀ : (b.slice 0 k).toNat = B₀ at *
  generalize eB₁ : (b.slice k b.size).toNat = B₁ at *
  -- `c₀ = a₀ b₀` into the low limbs of `r`.
  have hd₁ : (a.slice 0 k).size.toNat + (b.slice 0 k).size.toNat <
      a.size.toNat + b.size.toNat := by lia
  obtain ⟨m₁s, m₁u, m₁v⟩ := hmul (r.slice 0 (k + k)) (a.slice 0 k) (b.slice 0 k) hd₁
  have hW₀s := r.start_slice (i := 0) (j := k + k) (by simp) (by lia)
  have hW₀z := r.size_slice (i := 0) (j := k + k) (by simp) (by lia)
  simp only [USize.toNat_zero, Nat.add_zero, Nat.sub_zero, hkk] at hW₀s hW₀z
  simp only [USlice.array_slice] at m₁s m₁u m₁v
  rw [hW₀s, pa₀, pb₀] at m₁u m₁v
  rw [hW₀z, eA₀, eB₀] at m₁v
  replace m₁v := m₁v (USize.lt_iff_toNat_lt.2 (by rw [pa₀, USize.toNat_zero]; lia))
    (USize.lt_iff_toNat_lt.2 (by rw [pb₀, USize.toNat_zero]; lia)) (by lia)
  generalize mul (r.slice 0 (k + k)) (a.slice 0 k) (b.slice 0 k) hd₁ = R₁ at *
  -- The top coefficient into the top limbs.
  obtain ⟨x₁, x₂, x₃, -⟩ := window R₁ r m₁s (i := 4 * k) (j := a.size + b.size)
    (by rw [hT, hn]; lia) (by rw [hn]; lia)
  rw [hT] at x₂ x₃
  rw [hn] at x₃
  have hd₂ : (a.slice (3 * k) a.size).size.toNat + (b.slice k b.size).size.toNat <
      a.size.toNat + b.size.toNat := by lia
  obtain ⟨m₂s, m₂u, m₂v⟩ := hmul ((R₁.uslice r.start r.stop).slice (4 * k) (a.size + b.size))
    (a.slice (3 * k) a.size) (b.slice k b.size) hd₂
  rw [x₁, m₁s] at m₂s
  rw [x₁, x₂, pa₃, pb₁] at m₂u
  rw [x₂, x₃, pa₃, pb₁, eA₃, eB₁] at m₂v
  replace m₂v := m₂v (USize.lt_iff_toNat_lt.2 (by rw [pa₃, USize.toNat_zero]; lia))
    (USize.lt_iff_toNat_lt.2 (by rw [pb₁, USize.toNat_zero]; lia)) (by lia)
  generalize mul ((R₁.uslice r.start r.stop).slice (4 * k) (a.size + b.size))
    (a.slice (3 * k) a.size) (b.slice k b.size) hd₂ = R₂ at *
  have hc₀ : R₂.valAt r.start.toNat (2 * k.toNat) = A₀ * B₀ := by
    rw [← m₁v, show k.toNat + k.toNat = 2 * k.toNat by lia]
    exact UInt64Array.valAt_congr _ fun i _ hi => m₂u i (by lia)
  have hc₄ : R₂.valAt (r.start.toNat + 4 * k.toNat)
      ((a.size + b.size).toNat - 4 * k.toNat) = A₃ * B₁ := by
    rw [← m₂v, hn]; congr 1; lia
  -- The evaluations and their products.
  have pA (j : UInt64) (hj : j.toNat ≤ 5) :=
    eval4_at (a.slice 0 k) (a.slice k (k + k)) (a.slice (k + k) (3 * k))
      (a.slice (3 * k) a.size) k j hk1
      (by lia) (by lia) (by lia) (by lia) hj
  have pB (j : UInt64) (hj : j.toNat ≤ 5) :=
    eval2_at (b.slice 0 k) (b.slice k b.size) k j hk1
      (by lia) (by lia) hj
  rw [eA₀, eA₁, eA₂, eA₃] at pA
  rw [eB₀, eB₁] at pB
  have hdw (EA EB : UInt64Array) (hA' : EA.size = (k + 1).toNat) (hB' : EB.size = (k + 1).toNat) :
      EA.toUSlice.size.toNat + EB.toUSlice.size.toNat < a.size.toNat + b.size.toNat := by
    rw [eval_toUSlice_size hA', eval_toUSlice_size hB', hk1]; lia
  obtain ⟨w1s, w1v⟩ := prod_at mul hmul k hk1 hkk2
    (eval4 (a.slice 0 k) (a.slice k (k + k)) (a.slice (k + k) (3 * k))
      (a.slice (3 * k) a.size) (k + 1) 1)
    (eval2 (b.slice 0 k) (b.slice k b.size) (k + 1) 1)
    (size_eval4 ..) (size_eval2 ..) (hdw _ _ (size_eval4 ..) (size_eval2 ..))
  rw [pA 1 (by decide), pB 1 (by decide)] at w1v
  obtain ⟨w2s, w2v⟩ := prod_at mul hmul k hk1 hkk2
    (eval4 (a.slice 0 k) (a.slice k (k + k)) (a.slice (k + k) (3 * k))
      (a.slice (3 * k) a.size) (k + 1) 2)
    (eval2 (b.slice 0 k) (b.slice k b.size) (k + 1) 2)
    (size_eval4 ..) (size_eval2 ..) (hdw _ _ (size_eval4 ..) (size_eval2 ..))
  rw [pA 2 (by decide), pB 2 (by decide)] at w2v
  obtain ⟨w3s, w3v⟩ := prod_at mul hmul k hk1 hkk2
    (eval4 (a.slice 0 k) (a.slice k (k + k)) (a.slice (k + k) (3 * k))
      (a.slice (3 * k) a.size) (k + 1) 3)
    (eval2 (b.slice 0 k) (b.slice k b.size) (k + 1) 3)
    (size_eval4 ..) (size_eval2 ..) (hdw _ _ (size_eval4 ..) (size_eval2 ..))
  rw [pA 3 (by decide), pB 3 (by decide)] at w3v
  simp only [show (1 : UInt64).toNat = 1 from rfl,
    show (2 : UInt64).toNat = 2 from rfl,
    show (3 : UInt64).toNat = 3 from rfl] at w1v w2v w3v
  -- The interpolation.
  generalize hX : 2 ^ (64 * k.toNat) = X at *
  have hXX : 2 ^ (64 * (2 * k.toNat)) = X * X := by rw [← hX, ← Nat.pow_add]; congr 1; lia
  have hX3 : 2 ^ (64 * (3 * k.toNat)) = X * X * X := by
    rw [← hX, ← Nat.pow_add, ← Nat.pow_add]; congr 1; lia
  have hX4 : 2 ^ (64 * (4 * k.toNat)) = X * X * X * X := by
    rw [← hX, ← Nat.pow_add, ← Nat.pow_add, ← Nat.pow_add]; congr 1; lia
  have hval : a.toNat * b.toNat =
      A₀ * B₀ +
      X * (A₀ * B₁ + A₁ * B₀) +
      X * X * (A₁ * B₁ + A₂ * B₀) +
      X * X * X * (A₂ * B₁ + A₃ * B₀) +
      X * X * X * X * (A₃ * B₁) := by
    rw [hA, hB]; grind
  have hab : a.toNat * b.toNat < 2 ^ (64 * (a.size.toNat + b.size.toNat)) := by
    rw [Nat.mul_add, Nat.pow_add]
    exact Nat.mul_lt_mul_of_lt_of_lt (slice_lt a (Nat.le_refl _)) (slice_lt b (Nat.le_refl _))
  have hbm : (A₀ + A₁ * 3 + A₂ * (3 * 3) + A₃ * (3 * 3 * 3)) * (B₀ + B₁ * 3) <
      2 ^ (64 * (2 * k.toNat + 2 - 1)) := by
    rw [show 2 * k.toNat + 2 - 1 = 2 * k.toNat + 1 by lia, pow_succ_k, hXX]
    have := Nat.mul_lt_mul_of_lt_of_lt
      (show A₀ + A₁ * 3 + A₂ * (3 * 3) + A₃ * (3 * 3 * 3) < 40 * X by lia)
      (show B₀ + B₁ * 3 < 4 * X by lia)
    rw [show 40 * X * (4 * X) = 160 * (X * X) by grind] at this
    generalize X * X = Y at *
    lia
  obtain ⟨f₁, f₂, f₃⟩ := interp4_spec R₂ r (a.size + b.size) k _ _ _ (2 * k.toNat + 2)
    (A₀ * B₀) (A₀ * B₁ + A₁ * B₀) (A₁ * B₁ + A₂ * B₀) (A₂ * B₁ + A₃ * B₀) (A₃ * B₁)
    m₂s (by rw [hn]; lia) (by rw [hn]; lia) hk₁ (by have := (k + k + 2).toNat_lt_size; lia)
    (by lia) w1s w2s w3s (by lia) (by rw [hn]; lia) hc₀ hc₄
    (by rw [w1v]; grind)
    (by rw [w2v]; grind)
    (by rw [w3v]; grind)
    (by refine Nat.lt_of_le_of_lt (Nat.le_of_eq ?_) hbm; grind)
    (by rw [hX, hXX, hX3, hX4, hn, ← hval]; exact hab)
  rw [hn, hX, hXX, hX3, hX4, ← hval] at f₃
  refine ⟨f₁, fun i hi => ?_, fun _ _ _ => f₃⟩
  rw [f₂ i (by rw [hn]; lia), m₂u i (by lia), m₁u i (by lia)]

private theorem toom32_spec (r a b : USlice) (k : USize) (hk : Shape32 r a b k)
    (mul : Mul (a.size.toNat + b.size.toNat))
    (hmul : ∀ r' a' b' h', MulOK (mul r' a' b' h') r' a' b') :
    MulOK (toom32 r a b k hk mul) r a b := by
  obtain ⟨hk₁, ha₁, ha₂, hb₁, hba, hr⟩ := hk
  obtain ⟨hkk, hk1, hkk2, hn⟩ := toom_sizes (r := r) (k := k) hr (by lia)
  have hnS := r.size.toNat_lt_size
  have hT : (3 * k).toNat = 3 * k.toNat := toNat_mul_k k 3 (by decide) r.size (by lia)
  have h3k : (3 * k).toNat = 3 * k.toNat := toNat_mul_k k 3 (by decide) r.size (by lia)
  dsimp only [toom32]
  -- The pieces.
  have pa₀ := (a.size_slice (i := 0) (j := k) (by simp) (by lia) :)
  have pa₁ := (a.size_slice (i := k) (j := (k + k)) (by lia) (by lia) :)
  have pa₂ := (a.size_slice (i := (k + k)) (j := a.size) (by lia) (Nat.le_refl _) :)
  simp only [USize.toNat_zero, Nat.sub_zero, hkk] at pa₀ pa₁ pa₂
  have hA := toNat_whole a
  rw [toNat_split a (i := 0) (j := k) (by simp) (by lia)] at hA
  rw [toNat_split a (i := k) (j := (k + k)) (by lia) (by lia)] at hA
  simp only [USize.toNat_zero, Nat.sub_zero, hkk,
    show 2 * k.toNat - k.toNat = k.toNat by lia] at hA
  have hA₀ := slice_lt (a.slice 0 k) (K := k.toNat) (by lia)
  have hA₁ := slice_lt (a.slice k (k + k)) (K := k.toNat) (by lia)
  have hA₂ := slice_lt (a.slice (k + k) a.size) (K := k.toNat) (by lia)
  generalize eA₀ : (a.slice 0 k).toNat = A₀ at *
  generalize eA₁ : (a.slice k (k + k)).toNat = A₁ at *
  generalize eA₂ : (a.slice (k + k) a.size).toNat = A₂ at *
  have pb₀ := (b.size_slice (i := 0) (j := k) (by simp) (by lia) :)
  have pb₁ := (b.size_slice (i := k) (j := b.size) (by lia) (Nat.le_refl _) :)
  simp only [USize.toNat_zero, Nat.sub_zero] at pb₀ pb₁
  have hB := toNat_whole b
  rw [toNat_split b (i := 0) (j := k) (by simp) (by lia)] at hB
  simp only [USize.toNat_zero, Nat.sub_zero] at hB
  have hB₀ := slice_lt (b.slice 0 k) (K := k.toNat) (by lia)
  have hB₁ := slice_lt (b.slice k b.size) (K := k.toNat) (by lia)
  generalize eB₀ : (b.slice 0 k).toNat = B₀ at *
  generalize eB₁ : (b.slice k b.size).toNat = B₁ at *
  -- `c₀ = a₀ b₀` into the low limbs of `r`.
  have hd₁ : (a.slice 0 k).size.toNat + (b.slice 0 k).size.toNat <
      a.size.toNat + b.size.toNat := by lia
  obtain ⟨m₁s, m₁u, m₁v⟩ := hmul (r.slice 0 (k + k)) (a.slice 0 k) (b.slice 0 k) hd₁
  have hW₀s := r.start_slice (i := 0) (j := k + k) (by simp) (by lia)
  have hW₀z := r.size_slice (i := 0) (j := k + k) (by simp) (by lia)
  simp only [USize.toNat_zero, Nat.add_zero, Nat.sub_zero, hkk] at hW₀s hW₀z
  simp only [USlice.array_slice] at m₁s m₁u m₁v
  rw [hW₀s, pa₀, pb₀] at m₁u m₁v
  rw [hW₀z, eA₀, eB₀] at m₁v
  replace m₁v := m₁v (USize.lt_iff_toNat_lt.2 (by rw [pa₀, USize.toNat_zero]; lia))
    (USize.lt_iff_toNat_lt.2 (by rw [pb₀, USize.toNat_zero]; lia)) (by lia)
  generalize mul (r.slice 0 (k + k)) (a.slice 0 k) (b.slice 0 k) hd₁ = R₁ at *
  -- The top coefficient into the top limbs.
  obtain ⟨x₁, x₂, x₃, -⟩ := window R₁ r m₁s (i := 3 * k) (j := a.size + b.size)
    (by rw [hT, hn]; lia) (by rw [hn]; lia)
  rw [hT] at x₂ x₃
  rw [hn] at x₃
  have hd₂ : (a.slice (k + k) a.size).size.toNat + (b.slice k b.size).size.toNat <
      a.size.toNat + b.size.toNat := by lia
  obtain ⟨m₂s, m₂u, m₂v⟩ := hmul ((R₁.uslice r.start r.stop).slice (3 * k) (a.size + b.size))
    (a.slice (k + k) a.size) (b.slice k b.size) hd₂
  rw [x₁, m₁s] at m₂s
  rw [x₁, x₂, pa₂, pb₁] at m₂u
  rw [x₂, x₃, pa₂, pb₁, eA₂, eB₁] at m₂v
  replace m₂v := m₂v (USize.lt_iff_toNat_lt.2 (by rw [pa₂, USize.toNat_zero]; lia))
    (USize.lt_iff_toNat_lt.2 (by rw [pb₁, USize.toNat_zero]; lia)) (by lia)
  generalize mul ((R₁.uslice r.start r.stop).slice (3 * k) (a.size + b.size))
    (a.slice (k + k) a.size) (b.slice k b.size) hd₂ = R₂ at *
  have hc₀ : R₂.valAt r.start.toNat (2 * k.toNat) = A₀ * B₀ := by
    rw [← m₁v, show k.toNat + k.toNat = 2 * k.toNat by lia]
    exact UInt64Array.valAt_congr _ fun i _ hi => m₂u i (by lia)
  have hc₄ : R₂.valAt (r.start.toNat + 3 * k.toNat)
      ((a.size + b.size).toNat - 3 * k.toNat) = A₂ * B₁ := by
    rw [← m₂v, hn]; congr 1; lia
  -- The evaluations and their products.
  have pA (j : UInt64) (hj : j.toNat ≤ 5) :=
    eval3_at (a.slice 0 k) (a.slice k (k + k)) (a.slice (k + k) a.size)
       k j hk1
      (by lia) (by lia) (by lia) hj
  have pB (j : UInt64) (hj : j.toNat ≤ 5) :=
    eval2_at (b.slice 0 k) (b.slice k b.size) k j hk1
      (by lia) (by lia) hj
  rw [eA₀, eA₁, eA₂] at pA
  rw [eB₀, eB₁] at pB
  have hdw (EA EB : UInt64Array) (hA' : EA.size = (k + 1).toNat) (hB' : EB.size = (k + 1).toNat) :
      EA.toUSlice.size.toNat + EB.toUSlice.size.toNat < a.size.toNat + b.size.toNat := by
    rw [eval_toUSlice_size hA', eval_toUSlice_size hB', hk1]; lia
  obtain ⟨w1s, w1v⟩ := prod_at mul hmul k hk1 hkk2
    (eval3 (a.slice 0 k) (a.slice k (k + k)) (a.slice (k + k) a.size) (k + 1) 1)
    (eval2 (b.slice 0 k) (b.slice k b.size) (k + 1) 1)
    (size_eval3 ..) (size_eval2 ..) (hdw _ _ (size_eval3 ..) (size_eval2 ..))
  rw [pA 1 (by decide), pB 1 (by decide)] at w1v
  obtain ⟨w2s, w2v⟩ := prod_at mul hmul k hk1 hkk2
    (eval3 (a.slice 0 k) (a.slice k (k + k)) (a.slice (k + k) a.size) (k + 1) 2)
    (eval2 (b.slice 0 k) (b.slice k b.size) (k + 1) 2)
    (size_eval3 ..) (size_eval2 ..) (hdw _ _ (size_eval3 ..) (size_eval2 ..))
  rw [pA 2 (by decide), pB 2 (by decide)] at w2v
  simp only [show (1 : UInt64).toNat = 1 from rfl,
    show (2 : UInt64).toNat = 2 from rfl] at w1v w2v
  -- The interpolation.
  generalize hX : 2 ^ (64 * k.toNat) = X at *
  have hXX : 2 ^ (64 * (2 * k.toNat)) = X * X := by rw [← hX, ← Nat.pow_add]; congr 1; lia
  have hX3 : 2 ^ (64 * (3 * k.toNat)) = X * X * X := by
    rw [← hX, ← Nat.pow_add, ← Nat.pow_add]; congr 1; lia
  have hX4 : 2 ^ (64 * (4 * k.toNat)) = X * X * X * X := by
    rw [← hX, ← Nat.pow_add, ← Nat.pow_add, ← Nat.pow_add]; congr 1; lia
  have hval : a.toNat * b.toNat =
      A₀ * B₀ +
      X * (A₀ * B₁ + A₁ * B₀) +
      X * X * (A₁ * B₁ + A₂ * B₀) +
      X * X * X * (A₂ * B₁) := by
    rw [hA, hB]; grind
  have hab : a.toNat * b.toNat < 2 ^ (64 * (a.size.toNat + b.size.toNat)) := by
    rw [Nat.mul_add, Nat.pow_add]
    exact Nat.mul_lt_mul_of_lt_of_lt (slice_lt a (Nat.le_refl _)) (slice_lt b (Nat.le_refl _))
  have hbm : (A₀ + A₁ * 2 + A₂ * (2 * 2)) * (B₀ + B₁ * 2) <
      2 ^ (64 * (2 * k.toNat + 2 - 1)) := by
    rw [show 2 * k.toNat + 2 - 1 = 2 * k.toNat + 1 by lia, pow_succ_k, hXX]
    have := Nat.mul_lt_mul_of_lt_of_lt
      (show A₀ + A₁ * 2 + A₂ * (2 * 2) < 7 * X by lia)
      (show B₀ + B₁ * 2 < 3 * X by lia)
    rw [show 7 * X * (3 * X) = 21 * (X * X) by grind] at this
    generalize X * X = Y at *
    lia
  obtain ⟨f₁, f₂, f₃⟩ := interp3_spec R₂ r (a.size + b.size) k _ _ (2 * k.toNat + 2)
    (A₀ * B₀) (A₀ * B₁ + A₁ * B₀) (A₁ * B₁ + A₂ * B₀) (A₂ * B₁)
    m₂s (by rw [hn]; lia) (by rw [hn]; lia) hk₁ (by have := (k + k + 2).toNat_lt_size; lia)
    (by lia) w1s w2s (by lia) (by rw [hn]; lia) hc₀ hc₄
    (by rw [w1v]; grind)
    (by rw [w2v]; grind)
    (by refine Nat.lt_of_le_of_lt (Nat.le_of_eq ?_) hbm; grind)
    (by rw [hX, hXX, hX3, hn, ← hval]; exact hab)
  rw [hn, hX, hXX, hX3, ← hval] at f₃
  refine ⟨f₁, fun i hi => ?_, fun _ _ _ => f₃⟩
  rw [f₂ i (by rw [hn]; lia), m₂u i (by lia), m₁u i (by lia)]

private theorem toom44_spec (r a b : USlice) (k : USize) (hk : Shape44 r a b k)
    (mul : Mul (a.size.toNat + b.size.toNat))
    (hmul : ∀ r' a' b' h', MulOK (mul r' a' b' h') r' a' b') :
    MulOK (toom44 r a b k hk mul) r a b := by
  obtain ⟨hk₁, ha₁, ha₂, hb₁, hba, hr⟩ := hk
  obtain ⟨hkk, hk1, hkk2, hn⟩ := toom_sizes (r := r) (k := k) hr (by lia)
  have hnS := r.size.toNat_lt_size
  have hT : (6 * k).toNat = 6 * k.toNat := toNat_mul_k k 6 (by decide) r.size (by lia)
  have h3k : (3 * k).toNat = 3 * k.toNat := toNat_mul_k k 3 (by decide) r.size (by lia)
  dsimp only [toom44]
  -- The pieces.
  have pa₀ := (a.size_slice (i := 0) (j := k) (by simp) (by lia) :)
  have pa₁ := (a.size_slice (i := k) (j := (k + k)) (by lia) (by lia) :)
  have pa₂ := (a.size_slice (i := (k + k)) (j := (3 * k)) (by lia) (by lia) :)
  have pa₃ := (a.size_slice (i := (3 * k)) (j := a.size) (by lia) (Nat.le_refl _) :)
  simp only [USize.toNat_zero, Nat.sub_zero, hkk, h3k] at pa₀ pa₁ pa₂ pa₃
  have hA := toNat_whole a
  rw [toNat_split a (i := 0) (j := k) (by simp) (by lia)] at hA
  rw [toNat_split a (i := k) (j := (k + k)) (by lia) (by lia)] at hA
  rw [toNat_split a (i := (k + k)) (j := (3 * k)) (by lia) (by lia)] at hA
  simp only [USize.toNat_zero, Nat.sub_zero, hkk, h3k,
    show 2 * k.toNat - k.toNat = k.toNat by lia,
    show 3 * k.toNat - 2 * k.toNat = k.toNat by lia] at hA
  have hA₀ := slice_lt (a.slice 0 k) (K := k.toNat) (by lia)
  have hA₁ := slice_lt (a.slice k (k + k)) (K := k.toNat) (by lia)
  have hA₂ := slice_lt (a.slice (k + k) (3 * k)) (K := k.toNat) (by lia)
  have hA₃ := slice_lt (a.slice (3 * k) a.size) (K := k.toNat) (by lia)
  generalize eA₀ : (a.slice 0 k).toNat = A₀ at *
  generalize eA₁ : (a.slice k (k + k)).toNat = A₁ at *
  generalize eA₂ : (a.slice (k + k) (3 * k)).toNat = A₂ at *
  generalize eA₃ : (a.slice (3 * k) a.size).toNat = A₃ at *
  have pb₀ := (b.size_slice (i := 0) (j := k) (by simp) (by lia) :)
  have pb₁ := (b.size_slice (i := k) (j := (k + k)) (by lia) (by lia) :)
  have pb₂ := (b.size_slice (i := (k + k)) (j := (3 * k)) (by lia) (by lia) :)
  have pb₃ := (b.size_slice (i := (3 * k)) (j := b.size) (by lia) (Nat.le_refl _) :)
  simp only [USize.toNat_zero, Nat.sub_zero, hkk, h3k] at pb₀ pb₁ pb₂ pb₃
  have hB := toNat_whole b
  rw [toNat_split b (i := 0) (j := k) (by simp) (by lia)] at hB
  rw [toNat_split b (i := k) (j := (k + k)) (by lia) (by lia)] at hB
  rw [toNat_split b (i := (k + k)) (j := (3 * k)) (by lia) (by lia)] at hB
  simp only [USize.toNat_zero, Nat.sub_zero, hkk, h3k,
    show 2 * k.toNat - k.toNat = k.toNat by lia,
    show 3 * k.toNat - 2 * k.toNat = k.toNat by lia] at hB
  have hB₀ := slice_lt (b.slice 0 k) (K := k.toNat) (by lia)
  have hB₁ := slice_lt (b.slice k (k + k)) (K := k.toNat) (by lia)
  have hB₂ := slice_lt (b.slice (k + k) (3 * k)) (K := k.toNat) (by lia)
  have hB₃ := slice_lt (b.slice (3 * k) b.size) (K := k.toNat) (by lia)
  generalize eB₀ : (b.slice 0 k).toNat = B₀ at *
  generalize eB₁ : (b.slice k (k + k)).toNat = B₁ at *
  generalize eB₂ : (b.slice (k + k) (3 * k)).toNat = B₂ at *
  generalize eB₃ : (b.slice (3 * k) b.size).toNat = B₃ at *
  -- `c₀ = a₀ b₀` into the low limbs of `r`.
  have hd₁ : (a.slice 0 k).size.toNat + (b.slice 0 k).size.toNat <
      a.size.toNat + b.size.toNat := by lia
  obtain ⟨m₁s, m₁u, m₁v⟩ := hmul (r.slice 0 (k + k)) (a.slice 0 k) (b.slice 0 k) hd₁
  have hW₀s := r.start_slice (i := 0) (j := k + k) (by simp) (by lia)
  have hW₀z := r.size_slice (i := 0) (j := k + k) (by simp) (by lia)
  simp only [USize.toNat_zero, Nat.add_zero, Nat.sub_zero, hkk] at hW₀s hW₀z
  simp only [USlice.array_slice] at m₁s m₁u m₁v
  rw [hW₀s, pa₀, pb₀] at m₁u m₁v
  rw [hW₀z, eA₀, eB₀] at m₁v
  replace m₁v := m₁v (USize.lt_iff_toNat_lt.2 (by rw [pa₀, USize.toNat_zero]; lia))
    (USize.lt_iff_toNat_lt.2 (by rw [pb₀, USize.toNat_zero]; lia)) (by lia)
  generalize mul (r.slice 0 (k + k)) (a.slice 0 k) (b.slice 0 k) hd₁ = R₁ at *
  -- The top coefficient into the top limbs.
  obtain ⟨x₁, x₂, x₃, -⟩ := window R₁ r m₁s (i := 6 * k) (j := a.size + b.size)
    (by rw [hT, hn]; lia) (by rw [hn]; lia)
  rw [hT] at x₂ x₃
  rw [hn] at x₃
  have hd₂ : (a.slice (3 * k) a.size).size.toNat + (b.slice (3 * k) b.size).size.toNat <
      a.size.toNat + b.size.toNat := by lia
  obtain ⟨m₂s, m₂u, m₂v⟩ := hmul ((R₁.uslice r.start r.stop).slice (6 * k) (a.size + b.size))
    (a.slice (3 * k) a.size) (b.slice (3 * k) b.size) hd₂
  rw [x₁, m₁s] at m₂s
  rw [x₁, x₂, pa₃, pb₃] at m₂u
  rw [x₂, x₃, pa₃, pb₃, eA₃, eB₃] at m₂v
  replace m₂v := m₂v (USize.lt_iff_toNat_lt.2 (by rw [pa₃, USize.toNat_zero]; lia))
    (USize.lt_iff_toNat_lt.2 (by rw [pb₃, USize.toNat_zero]; lia)) (by lia)
  generalize mul ((R₁.uslice r.start r.stop).slice (6 * k) (a.size + b.size))
    (a.slice (3 * k) a.size) (b.slice (3 * k) b.size) hd₂ = R₂ at *
  have hc₀ : R₂.valAt r.start.toNat (2 * k.toNat) = A₀ * B₀ := by
    rw [← m₁v, show k.toNat + k.toNat = 2 * k.toNat by lia]
    exact UInt64Array.valAt_congr _ fun i _ hi => m₂u i (by lia)
  have hc₄ : R₂.valAt (r.start.toNat + 6 * k.toNat)
      ((a.size + b.size).toNat - 6 * k.toNat) = A₃ * B₃ := by
    rw [← m₂v, hn]; congr 1; lia
  -- The evaluations and their products.
  have pA (j : UInt64) (hj : j.toNat ≤ 5) :=
    eval4_at (a.slice 0 k) (a.slice k (k + k)) (a.slice (k + k) (3 * k))
      (a.slice (3 * k) a.size) k j hk1
      (by lia) (by lia) (by lia) (by lia) hj
  have pB (j : UInt64) (hj : j.toNat ≤ 5) :=
    eval4_at (b.slice 0 k) (b.slice k (k + k)) (b.slice (k + k) (3 * k))
      (b.slice (3 * k) b.size) k j hk1
      (by lia) (by lia) (by lia) (by lia) hj
  rw [eA₀, eA₁, eA₂, eA₃] at pA
  rw [eB₀, eB₁, eB₂, eB₃] at pB
  have hdw (EA EB : UInt64Array) (hA' : EA.size = (k + 1).toNat) (hB' : EB.size = (k + 1).toNat) :
      EA.toUSlice.size.toNat + EB.toUSlice.size.toNat < a.size.toNat + b.size.toNat := by
    rw [eval_toUSlice_size hA', eval_toUSlice_size hB', hk1]; lia
  obtain ⟨w1s, w1v⟩ := prod_at mul hmul k hk1 hkk2
    (eval4 (a.slice 0 k) (a.slice k (k + k)) (a.slice (k + k) (3 * k))
      (a.slice (3 * k) a.size) (k + 1) 1)
    (eval4 (b.slice 0 k) (b.slice k (k + k)) (b.slice (k + k) (3 * k))
      (b.slice (3 * k) b.size) (k + 1) 1)
    (size_eval4 ..) (size_eval4 ..) (hdw _ _ (size_eval4 ..) (size_eval4 ..))
  rw [pA 1 (by decide), pB 1 (by decide)] at w1v
  obtain ⟨w2s, w2v⟩ := prod_at mul hmul k hk1 hkk2
    (eval4 (a.slice 0 k) (a.slice k (k + k)) (a.slice (k + k) (3 * k))
      (a.slice (3 * k) a.size) (k + 1) 2)
    (eval4 (b.slice 0 k) (b.slice k (k + k)) (b.slice (k + k) (3 * k))
      (b.slice (3 * k) b.size) (k + 1) 2)
    (size_eval4 ..) (size_eval4 ..) (hdw _ _ (size_eval4 ..) (size_eval4 ..))
  rw [pA 2 (by decide), pB 2 (by decide)] at w2v
  obtain ⟨w3s, w3v⟩ := prod_at mul hmul k hk1 hkk2
    (eval4 (a.slice 0 k) (a.slice k (k + k)) (a.slice (k + k) (3 * k))
      (a.slice (3 * k) a.size) (k + 1) 3)
    (eval4 (b.slice 0 k) (b.slice k (k + k)) (b.slice (k + k) (3 * k))
      (b.slice (3 * k) b.size) (k + 1) 3)
    (size_eval4 ..) (size_eval4 ..) (hdw _ _ (size_eval4 ..) (size_eval4 ..))
  rw [pA 3 (by decide), pB 3 (by decide)] at w3v
  obtain ⟨w4s, w4v⟩ := prod_at mul hmul k hk1 hkk2
    (eval4 (a.slice 0 k) (a.slice k (k + k)) (a.slice (k + k) (3 * k))
      (a.slice (3 * k) a.size) (k + 1) 4)
    (eval4 (b.slice 0 k) (b.slice k (k + k)) (b.slice (k + k) (3 * k))
      (b.slice (3 * k) b.size) (k + 1) 4)
    (size_eval4 ..) (size_eval4 ..) (hdw _ _ (size_eval4 ..) (size_eval4 ..))
  rw [pA 4 (by decide), pB 4 (by decide)] at w4v
  obtain ⟨w5s, w5v⟩ := prod_at mul hmul k hk1 hkk2
    (eval4 (a.slice 0 k) (a.slice k (k + k)) (a.slice (k + k) (3 * k))
      (a.slice (3 * k) a.size) (k + 1) 5)
    (eval4 (b.slice 0 k) (b.slice k (k + k)) (b.slice (k + k) (3 * k))
      (b.slice (3 * k) b.size) (k + 1) 5)
    (size_eval4 ..) (size_eval4 ..) (hdw _ _ (size_eval4 ..) (size_eval4 ..))
  rw [pA 5 (by decide), pB 5 (by decide)] at w5v
  simp only [show (1 : UInt64).toNat = 1 from rfl,
    show (2 : UInt64).toNat = 2 from rfl,
    show (3 : UInt64).toNat = 3 from rfl,
    show (4 : UInt64).toNat = 4 from rfl,
    show (5 : UInt64).toNat = 5 from rfl] at w1v w2v w3v w4v w5v
  -- The interpolation.
  generalize hX : 2 ^ (64 * k.toNat) = X at *
  have hXX : 2 ^ (64 * (2 * k.toNat)) = X * X := by rw [← hX, ← Nat.pow_add]; congr 1; lia
  have hX3 : 2 ^ (64 * (3 * k.toNat)) = X * X * X := by
    rw [← hX, ← Nat.pow_add, ← Nat.pow_add]; congr 1; lia
  have hX4 : 2 ^ (64 * (4 * k.toNat)) = X * X * X * X := by
    rw [← hX, ← Nat.pow_add, ← Nat.pow_add, ← Nat.pow_add]; congr 1; lia
  have hX5 : 2 ^ (64 * (5 * k.toNat)) = X * X * X * X * X := by
    rw [← hX, ← Nat.pow_add, ← Nat.pow_add, ← Nat.pow_add, ← Nat.pow_add]; congr 1; lia
  have hX6 : 2 ^ (64 * (6 * k.toNat)) = X * X * X * X * X * X := by
    rw [← hX, ← Nat.pow_add, ← Nat.pow_add, ← Nat.pow_add, ← Nat.pow_add, ← Nat.pow_add]
    congr 1; lia
  have hval : a.toNat * b.toNat =
      A₀ * B₀ +
      X * (A₀ * B₁ + A₁ * B₀) +
      X * X * (A₀ * B₂ + A₁ * B₁ + A₂ * B₀) +
      X * X * X * (A₀ * B₃ + A₁ * B₂ + A₂ * B₁ + A₃ * B₀) +
      X * X * X * X * (A₁ * B₃ + A₂ * B₂ + A₃ * B₁) +
      X * X * X * X * X * (A₂ * B₃ + A₃ * B₂) +
      X * X * X * X * X * X * (A₃ * B₃) := by
    rw [hA, hB]; grind
  have hab : a.toNat * b.toNat < 2 ^ (64 * (a.size.toNat + b.size.toNat)) := by
    rw [Nat.mul_add, Nat.pow_add]
    exact Nat.mul_lt_mul_of_lt_of_lt (slice_lt a (Nat.le_refl _)) (slice_lt b (Nat.le_refl _))
  obtain ⟨f₁, f₂, f₃⟩ := interp6_spec R₂ r (a.size + b.size) k _ _ _ _ _ (2 * k.toNat + 2)
    (A₀ * B₀) (A₀ * B₁ + A₁ * B₀) (A₀ * B₂ + A₁ * B₁ + A₂ * B₀)
        (A₀ * B₃ + A₁ * B₂ + A₂ * B₁ + A₃ * B₀) (A₁ * B₃ + A₂ * B₂ + A₃ * B₁) (A₂ * B₃ + A₃ * B₂)
        (A₃ * B₃)
    m₂s (by rw [hn]; lia) (by rw [hn]; lia) hk₁ (by have := (k + k + 2).toNat_lt_size; lia)
    w1s w2s w3s w4s w5s (by lia) (by rw [hn]; lia) hc₀ hc₄
    (by rw [w1v]; grind)
    (by rw [w2v]; grind)
    (by rw [w3v]; grind)
    (by rw [w4v]; grind)
    (by rw [w5v]; grind)
    (by rw [hX, hXX, hX3, hX4, hX5, hX6, hn, ← hval]; exact hab)
  rw [hn, hX, hXX, hX3, hX4, hX5, hX6, ← hval] at f₃
  refine ⟨f₁, fun i hi => ?_, fun _ _ _ => f₃⟩
  rw [f₂ i (by rw [hn]; lia), m₂u i (by lia), m₁u i (by lia)]

private theorem toom43_spec (r a b : USlice) (k : USize) (hk : Shape43 r a b k)
    (mul : Mul (a.size.toNat + b.size.toNat))
    (hmul : ∀ r' a' b' h', MulOK (mul r' a' b' h') r' a' b') :
    MulOK (toom43 r a b k hk mul) r a b := by
  obtain ⟨hk₁, ha₁, ha₂, hb₁, hba, hr⟩ := hk
  obtain ⟨hkk, hk1, hkk2, hn⟩ := toom_sizes (r := r) (k := k) hr (by lia)
  have hnS := r.size.toNat_lt_size
  have hT : (5 * k).toNat = 5 * k.toNat := toNat_mul_k k 5 (by decide) r.size (by lia)
  have h3k : (3 * k).toNat = 3 * k.toNat := toNat_mul_k k 3 (by decide) r.size (by lia)
  dsimp only [toom43]
  -- The pieces.
  have pa₀ := (a.size_slice (i := 0) (j := k) (by simp) (by lia) :)
  have pa₁ := (a.size_slice (i := k) (j := (k + k)) (by lia) (by lia) :)
  have pa₂ := (a.size_slice (i := (k + k)) (j := (3 * k)) (by lia) (by lia) :)
  have pa₃ := (a.size_slice (i := (3 * k)) (j := a.size) (by lia) (Nat.le_refl _) :)
  simp only [USize.toNat_zero, Nat.sub_zero, hkk, h3k] at pa₀ pa₁ pa₂ pa₃
  have hA := toNat_whole a
  rw [toNat_split a (i := 0) (j := k) (by simp) (by lia)] at hA
  rw [toNat_split a (i := k) (j := (k + k)) (by lia) (by lia)] at hA
  rw [toNat_split a (i := (k + k)) (j := (3 * k)) (by lia) (by lia)] at hA
  simp only [USize.toNat_zero, Nat.sub_zero, hkk, h3k,
    show 2 * k.toNat - k.toNat = k.toNat by lia,
    show 3 * k.toNat - 2 * k.toNat = k.toNat by lia] at hA
  have hA₀ := slice_lt (a.slice 0 k) (K := k.toNat) (by lia)
  have hA₁ := slice_lt (a.slice k (k + k)) (K := k.toNat) (by lia)
  have hA₂ := slice_lt (a.slice (k + k) (3 * k)) (K := k.toNat) (by lia)
  have hA₃ := slice_lt (a.slice (3 * k) a.size) (K := k.toNat) (by lia)
  generalize eA₀ : (a.slice 0 k).toNat = A₀ at *
  generalize eA₁ : (a.slice k (k + k)).toNat = A₁ at *
  generalize eA₂ : (a.slice (k + k) (3 * k)).toNat = A₂ at *
  generalize eA₃ : (a.slice (3 * k) a.size).toNat = A₃ at *
  have pb₀ := (b.size_slice (i := 0) (j := k) (by simp) (by lia) :)
  have pb₁ := (b.size_slice (i := k) (j := (k + k)) (by lia) (by lia) :)
  have pb₂ := (b.size_slice (i := (k + k)) (j := b.size) (by lia) (Nat.le_refl _) :)
  simp only [USize.toNat_zero, Nat.sub_zero, hkk] at pb₀ pb₁ pb₂
  have hB := toNat_whole b
  rw [toNat_split b (i := 0) (j := k) (by simp) (by lia)] at hB
  rw [toNat_split b (i := k) (j := (k + k)) (by lia) (by lia)] at hB
  simp only [USize.toNat_zero, Nat.sub_zero, hkk,
    show 2 * k.toNat - k.toNat = k.toNat by lia] at hB
  have hB₀ := slice_lt (b.slice 0 k) (K := k.toNat) (by lia)
  have hB₁ := slice_lt (b.slice k (k + k)) (K := k.toNat) (by lia)
  have hB₂ := slice_lt (b.slice (k + k) b.size) (K := k.toNat) (by lia)
  generalize eB₀ : (b.slice 0 k).toNat = B₀ at *
  generalize eB₁ : (b.slice k (k + k)).toNat = B₁ at *
  generalize eB₂ : (b.slice (k + k) b.size).toNat = B₂ at *
  -- `c₀ = a₀ b₀` into the low limbs of `r`.
  have hd₁ : (a.slice 0 k).size.toNat + (b.slice 0 k).size.toNat <
      a.size.toNat + b.size.toNat := by lia
  obtain ⟨m₁s, m₁u, m₁v⟩ := hmul (r.slice 0 (k + k)) (a.slice 0 k) (b.slice 0 k) hd₁
  have hW₀s := r.start_slice (i := 0) (j := k + k) (by simp) (by lia)
  have hW₀z := r.size_slice (i := 0) (j := k + k) (by simp) (by lia)
  simp only [USize.toNat_zero, Nat.add_zero, Nat.sub_zero, hkk] at hW₀s hW₀z
  simp only [USlice.array_slice] at m₁s m₁u m₁v
  rw [hW₀s, pa₀, pb₀] at m₁u m₁v
  rw [hW₀z, eA₀, eB₀] at m₁v
  replace m₁v := m₁v (USize.lt_iff_toNat_lt.2 (by rw [pa₀, USize.toNat_zero]; lia))
    (USize.lt_iff_toNat_lt.2 (by rw [pb₀, USize.toNat_zero]; lia)) (by lia)
  generalize mul (r.slice 0 (k + k)) (a.slice 0 k) (b.slice 0 k) hd₁ = R₁ at *
  -- The top coefficient into the top limbs.
  obtain ⟨x₁, x₂, x₃, -⟩ := window R₁ r m₁s (i := 5 * k) (j := a.size + b.size)
    (by rw [hT, hn]; lia) (by rw [hn]; lia)
  rw [hT] at x₂ x₃
  rw [hn] at x₃
  have hd₂ : (a.slice (3 * k) a.size).size.toNat + (b.slice (k + k) b.size).size.toNat <
      a.size.toNat + b.size.toNat := by lia
  obtain ⟨m₂s, m₂u, m₂v⟩ := hmul ((R₁.uslice r.start r.stop).slice (5 * k) (a.size + b.size))
    (a.slice (3 * k) a.size) (b.slice (k + k) b.size) hd₂
  rw [x₁, m₁s] at m₂s
  rw [x₁, x₂, pa₃, pb₂] at m₂u
  rw [x₂, x₃, pa₃, pb₂, eA₃, eB₂] at m₂v
  replace m₂v := m₂v (USize.lt_iff_toNat_lt.2 (by rw [pa₃, USize.toNat_zero]; lia))
    (USize.lt_iff_toNat_lt.2 (by rw [pb₂, USize.toNat_zero]; lia)) (by lia)
  generalize mul ((R₁.uslice r.start r.stop).slice (5 * k) (a.size + b.size))
    (a.slice (3 * k) a.size) (b.slice (k + k) b.size) hd₂ = R₂ at *
  have hc₀ : R₂.valAt r.start.toNat (2 * k.toNat) = A₀ * B₀ := by
    rw [← m₁v, show k.toNat + k.toNat = 2 * k.toNat by lia]
    exact UInt64Array.valAt_congr _ fun i _ hi => m₂u i (by lia)
  have hc₄ : R₂.valAt (r.start.toNat + 5 * k.toNat)
      ((a.size + b.size).toNat - 5 * k.toNat) = A₃ * B₂ := by
    rw [← m₂v, hn]; congr 1; lia
  -- The evaluations and their products.
  have pA (j : UInt64) (hj : j.toNat ≤ 5) :=
    eval4_at (a.slice 0 k) (a.slice k (k + k)) (a.slice (k + k) (3 * k))
      (a.slice (3 * k) a.size) k j hk1
      (by lia) (by lia) (by lia) (by lia) hj
  have pB (j : UInt64) (hj : j.toNat ≤ 5) :=
    eval3_at (b.slice 0 k) (b.slice k (k + k)) (b.slice (k + k) b.size)
       k j hk1
      (by lia) (by lia) (by lia) hj
  rw [eA₀, eA₁, eA₂, eA₃] at pA
  rw [eB₀, eB₁, eB₂] at pB
  have hdw (EA EB : UInt64Array) (hA' : EA.size = (k + 1).toNat) (hB' : EB.size = (k + 1).toNat) :
      EA.toUSlice.size.toNat + EB.toUSlice.size.toNat < a.size.toNat + b.size.toNat := by
    rw [eval_toUSlice_size hA', eval_toUSlice_size hB', hk1]; lia
  obtain ⟨w1s, w1v⟩ := prod_at mul hmul k hk1 hkk2
    (eval4 (a.slice 0 k) (a.slice k (k + k)) (a.slice (k + k) (3 * k))
      (a.slice (3 * k) a.size) (k + 1) 1)
    (eval3 (b.slice 0 k) (b.slice k (k + k)) (b.slice (k + k) b.size) (k + 1) 1)
    (size_eval4 ..) (size_eval3 ..) (hdw _ _ (size_eval4 ..) (size_eval3 ..))
  rw [pA 1 (by decide), pB 1 (by decide)] at w1v
  obtain ⟨w2s, w2v⟩ := prod_at mul hmul k hk1 hkk2
    (eval4 (a.slice 0 k) (a.slice k (k + k)) (a.slice (k + k) (3 * k))
      (a.slice (3 * k) a.size) (k + 1) 2)
    (eval3 (b.slice 0 k) (b.slice k (k + k)) (b.slice (k + k) b.size) (k + 1) 2)
    (size_eval4 ..) (size_eval3 ..) (hdw _ _ (size_eval4 ..) (size_eval3 ..))
  rw [pA 2 (by decide), pB 2 (by decide)] at w2v
  obtain ⟨w3s, w3v⟩ := prod_at mul hmul k hk1 hkk2
    (eval4 (a.slice 0 k) (a.slice k (k + k)) (a.slice (k + k) (3 * k))
      (a.slice (3 * k) a.size) (k + 1) 3)
    (eval3 (b.slice 0 k) (b.slice k (k + k)) (b.slice (k + k) b.size) (k + 1) 3)
    (size_eval4 ..) (size_eval3 ..) (hdw _ _ (size_eval4 ..) (size_eval3 ..))
  rw [pA 3 (by decide), pB 3 (by decide)] at w3v
  obtain ⟨w4s, w4v⟩ := prod_at mul hmul k hk1 hkk2
    (eval4 (a.slice 0 k) (a.slice k (k + k)) (a.slice (k + k) (3 * k))
      (a.slice (3 * k) a.size) (k + 1) 4)
    (eval3 (b.slice 0 k) (b.slice k (k + k)) (b.slice (k + k) b.size) (k + 1) 4)
    (size_eval4 ..) (size_eval3 ..) (hdw _ _ (size_eval4 ..) (size_eval3 ..))
  rw [pA 4 (by decide), pB 4 (by decide)] at w4v
  simp only [show (1 : UInt64).toNat = 1 from rfl,
    show (2 : UInt64).toNat = 2 from rfl,
    show (3 : UInt64).toNat = 3 from rfl,
    show (4 : UInt64).toNat = 4 from rfl] at w1v w2v w3v w4v
  -- The interpolation.
  generalize hX : 2 ^ (64 * k.toNat) = X at *
  have hXX : 2 ^ (64 * (2 * k.toNat)) = X * X := by rw [← hX, ← Nat.pow_add]; congr 1; lia
  have hX3 : 2 ^ (64 * (3 * k.toNat)) = X * X * X := by
    rw [← hX, ← Nat.pow_add, ← Nat.pow_add]; congr 1; lia
  have hX4 : 2 ^ (64 * (4 * k.toNat)) = X * X * X * X := by
    rw [← hX, ← Nat.pow_add, ← Nat.pow_add, ← Nat.pow_add]; congr 1; lia
  have hX5 : 2 ^ (64 * (5 * k.toNat)) = X * X * X * X * X := by
    rw [← hX, ← Nat.pow_add, ← Nat.pow_add, ← Nat.pow_add, ← Nat.pow_add]; congr 1; lia
  have hX6 : 2 ^ (64 * (6 * k.toNat)) = X * X * X * X * X * X := by
    rw [← hX, ← Nat.pow_add, ← Nat.pow_add, ← Nat.pow_add, ← Nat.pow_add, ← Nat.pow_add]
    congr 1; lia
  have hval : a.toNat * b.toNat =
      A₀ * B₀ +
      X * (A₀ * B₁ + A₁ * B₀) +
      X * X * (A₀ * B₂ + A₁ * B₁ + A₂ * B₀) +
      X * X * X * (A₁ * B₂ + A₂ * B₁ + A₃ * B₀) +
      X * X * X * X * (A₂ * B₂ + A₃ * B₁) +
      X * X * X * X * X * (A₃ * B₂) := by
    rw [hA, hB]; grind
  have hab : a.toNat * b.toNat < 2 ^ (64 * (a.size.toNat + b.size.toNat)) := by
    rw [Nat.mul_add, Nat.pow_add]
    exact Nat.mul_lt_mul_of_lt_of_lt (slice_lt a (Nat.le_refl _)) (slice_lt b (Nat.le_refl _))
  obtain ⟨f₁, f₂, f₃⟩ := interp5_spec R₂ r (a.size + b.size) k _ _ _ _ (2 * k.toNat + 2)
    (A₀ * B₀) (A₀ * B₁ + A₁ * B₀) (A₀ * B₂ + A₁ * B₁ + A₂ * B₀) (A₁ * B₂ + A₂ * B₁ + A₃ * B₀)
        (A₂ * B₂ + A₃ * B₁) (A₃ * B₂)
    m₂s (by rw [hn]; lia) (by rw [hn]; lia) hk₁ (by have := (k + k + 2).toNat_lt_size; lia)
    w1s w2s w3s w4s (by lia) (by rw [hn]; lia) hc₀ hc₄
    (by rw [w1v]; grind)
    (by rw [w2v]; grind)
    (by rw [w3v]; grind)
    (by rw [w4v]; grind)
    (by rw [hX, hXX, hX3, hX4, hX5, hn, ← hval]; exact hab)
  rw [hn, hX, hXX, hX3, hX4, hX5, ← hval] at f₃
  refine ⟨f₁, fun i hi => ?_, fun _ _ _ => f₃⟩
  rw [f₂ i (by rw [hn]; lia), m₂u i (by lia), m₁u i (by lia)]

/-! ## The dispatcher -/

/-- The guard of the Toom methods, and the split points as `Nat`s. -/
private theorem toom_guard {r a b : USlice}
    (h : toom3Threshold ≤ b.size ∧ b.size ≤ a.size ∧ a.size ≤ r.size ∧ b.size ≤ r.size - a.size) :
    384 ≤ b.size.toNat ∧ b.size.toNat ≤ a.size.toNat ∧
      a.size.toNat + b.size.toNat ≤ r.size.toNat ∧
      ((a.size + 2) / 3).toNat = (a.size.toNat + 2) / 3 ∧
      ((a.size + 3) / 4).toNat = (a.size.toNat + 3) / 4 := by
  have : 4294967296 ≤ USize.size := by cases USize.size_eq <;> lia
  have hT : toom3Threshold.toNat = 384 := by
    rw [toom3Threshold, USize.toNat_ofNat,
      Nat.mod_eq_of_lt (by simp only [USize.size] at this; lia)]
  have h₁ := USize.le_iff_toNat_le.1 h.1
  have h₂ := USize.le_iff_toNat_le.1 h.2.1
  have h₃ := USize.le_iff_toNat_le.1 h.2.2.1
  have h₄ := USize.le_iff_toNat_le.1 h.2.2.2
  rw [USize.toNat_sub_of_le _ _ h.2.2.1] at h₄
  rw [hT] at h₁
  have := r.size.toNat_lt_size
  have hc2 : (2 : USize).toNat = 2 := by
    rw [USize.toNat_ofNat, Nat.mod_eq_of_lt (by simp only [USize.size] at this; lia)]
  have hc3 : (3 : USize).toNat = 3 := by
    rw [USize.toNat_ofNat, Nat.mod_eq_of_lt (by simp only [USize.size] at this; lia)]
  have hc4 : (4 : USize).toNat = 4 := by
    rw [USize.toNat_ofNat, Nat.mod_eq_of_lt (by simp only [USize.size] at this; lia)]
  refine ⟨h₁, h₂, by lia, ?_, ?_⟩
  · rw [USize.toNat_div, USize.toNat_add_of_lt (by rw [hc2]; lia), hc2, hc3]
  · rw [USize.toNat_div, USize.toNat_add_of_lt (by rw [hc3]; lia), hc3, hc4]

/-- `mulToom` for `b.size ≤ a.size`. -/
def mulToomAux (r a b : USlice) : UInt64Array :=
  let mul : Mul (a.size.toNat + b.size.toNat) := fun r' a' b' _ =>
    if b'.size ≤ a'.size then mulToomAux r' a' b' else mulToomAux r' b' a'
  if h : toom3Threshold ≤ b.size ∧ b.size ≤ a.size ∧ a.size ≤ r.size ∧ b.size ≤ r.size - a.size then
    have hg := toom_guard h
    if h₄₄ : toom4Threshold ≤ b.size.toNat ∧ 3 * ((a.size.toNat + 3) / 4) < b.size.toNat then
      toom44 r a b ((a.size + 3) / 4) (by refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> lia) mul
    else if h₄₃ : toom4Threshold ≤ b.size.toNat ∧ 2 * ((a.size.toNat + 3) / 4) < b.size.toNat ∧
        b.size.toNat ≤ 3 * ((a.size.toNat + 3) / 4) then
      toom43 r a b ((a.size + 3) / 4) (by refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> lia) mul
    else if h₃₃ : (a.size + 2) / 3 + (a.size + 2) / 3 < b.size then
      toom33 r a b ((a.size + 2) / 3) (by
        have := USize.lt_iff_toNat_lt.1 h₃₃
        rw [USize.toNat_add_of_lt (by lia)] at this
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> lia) mul
    else if h₃₂ : (a.size + 2) / 3 < b.size then
      toom32 r a b ((a.size + 2) / 3) (by
        have := USize.lt_iff_toNat_lt.1 h₃₂
        have := mt (USize.lt_iff_toNat_lt (a := (a.size + 2) / 3 + (a.size + 2) / 3)).2 h₃₃
        rw [USize.toNat_add_of_lt (by lia)] at this
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> lia) mul
    else if h₄₂ : (a.size + 3) / 4 < b.size ∧ b.size ≤ (a.size + 3) / 4 + (a.size + 3) / 4 then
      toom42 r a b ((a.size + 3) / 4) (by
        have := USize.lt_iff_toNat_lt.1 h₄₂.1
        have := USize.le_iff_toNat_le.1 h₄₂.2
        rw [USize.toNat_add_of_lt (by lia)] at this
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> lia) mul
    else
      mulKaratsuba r a b
  else
    mulKaratsuba r a b
termination_by a.size.toNat + b.size.toNat
decreasing_by all_goals lia

private theorem MulOK.swap {R : UInt64Array} {r a b : USlice} (h : MulOK R r b a) :
    MulOK R r a b := by
  obtain ⟨h₁, h₂, h₃⟩ := h
  refine ⟨h₁, fun i hi => h₂ i (by lia), fun ha hb hr => ?_⟩
  rw [Nat.add_comm, Nat.mul_comm]; exact h₃ hb ha (by lia)

private theorem mulKaratsuba_ok (r a b : USlice) : MulOK (mulKaratsuba r a b) r a b :=
  ⟨size_mulKaratsuba r a b, getElem!_mulKaratsuba r a b,
    fun _ hb hr => valAt_mulKaratsuba r a b hb hr⟩

private theorem mulToomAux_spec (r a b : USlice) : MulOK (mulToomAux r a b) r a b := by
  have hmul (r' a' b' : USlice) (h' : a'.size.toNat + b'.size.toNat < a.size.toNat + b.size.toNat) :
      MulOK (if b'.size ≤ a'.size then mulToomAux r' a' b' else mulToomAux r' b' a') r' a' b' := by
    split
    · exact mulToomAux_spec r' a' b'
    · exact (mulToomAux_spec r' b' a').swap
  rw [mulToomAux]
  split
  · split
    · exact toom44_spec _ _ _ _ _ _ hmul
    · split
      · exact toom43_spec _ _ _ _ _ _ hmul
      · split
        · exact toom33_spec _ _ _ _ _ _ hmul
        · split
          · exact toom32_spec _ _ _ _ _ _ hmul
          · split
            · exact toom42_spec _ _ _ _ _ _ hmul
            · exact mulKaratsuba_ok r a b
  · exact mulKaratsuba_ok r a b
termination_by a.size.toNat + b.size.toNat
decreasing_by all_goals lia

/--
Writes the `a.size + b.size` limbs of `a * b` into `r`, by Toom-4 or Toom-4 by 3 from
`toom4Threshold` limbs in the smaller operand, and by Toom-3, Toom-3 by 2 or Toom-4 by 2,
depending on the sizes, from `toom3Threshold` limbs, and by
`mulKaratsuba` below. It requires `0 < a.size`, `0 < b.size` and `a.size + b.size ≤ r.size`, and
leaves `r` unchanged otherwise.
-/
public def mulToom (r a b : USlice) : UInt64Array :=
  if b.size ≤ a.size then mulToomAux r a b else mulToomAux r b a

private theorem mulToom_spec (r a b : USlice) : MulOK (mulToom r a b) r a b := by
  rw [mulToom]
  split
  · exact mulToomAux_spec r a b
  · exact (mulToomAux_spec r b a).swap

/-- `mulToom` keeps the size of the array of `r`. -/
@[simp] public theorem size_mulToom (r a b : USlice) : (mulToom r a b).size = r.array.size :=
  (mulToom_spec r a b).1

/-- `mulToom` leaves the limbs of `r` outside the ones it writes unchanged. -/
public theorem getElem!_mulToom (r a b : USlice) (i : Nat)
    (hi : i < r.start.toNat ∨ r.start.toNat + a.size.toNat + b.size.toNat ≤ i) :
    (mulToom r a b)[i]! = r.array[i]! :=
  (mulToom_spec r a b).2.1 i hi

public theorem valAt_mulToom (r a b : USlice) (ha : 0 < a.size) (hb : 0 < b.size)
    (hr : a.size.toNat + b.size.toNat ≤ r.size.toNat) :
    (mulToom r a b).valAt r.start.toNat (a.size.toNat + b.size.toNat) = a.toNat * b.toNat :=
  (mulToom_spec r a b).2.2 ha hb hr

/-! ## Squaring

Toom-3 and Toom-4 on `a` by itself: one set of pieces and evaluations, and squares for the
products, with the interpolations of the products. The squares recurse through `Sqr`.
-/

/-- The size from which `sqrToom` uses Toom-3. -/
public def toom3SqrThreshold : Nat := 600

/-- The size from which `sqrToom` uses Toom-4. -/
public def toom4SqrThreshold : Nat := 1000

/-- A squaring of operands of fewer than `N` limbs, the recursive calls of the Toom squares. -/
public abbrev Sqr (N : Nat) : Type := (r a : USlice) → a.size.toNat < N → UInt64Array

/-- The shape of the Toom-3 square: three pieces, the top one nonempty. -/
public abbrev Shape3S (r a : USlice) (k : USize) : Prop :=
  1 ≤ k.toNat ∧ 2 * k.toNat < a.size.toNat ∧ a.size.toNat ≤ 3 * k.toNat ∧
    a.size.toNat + a.size.toNat ≤ r.size.toNat

/-- The shape of the Toom-4 square: four pieces, the top one nonempty. -/
public abbrev Shape4S (r a : USlice) (k : USize) : Prop :=
  1 ≤ k.toNat ∧ 3 * k.toNat < a.size.toNat ∧ a.size.toNat ≤ 4 * k.toNat ∧
    a.size.toNat + a.size.toNat ≤ r.size.toNat

/-- The Toom-3 square: `a` in three pieces of `k` limbs, at most, the top one nonempty. -/
public def toom3Sqr (r a : USlice) (k : USize) (hk : Shape3S r a k) (sq : Sqr a.size.toNat) :
    UInt64Array :=
  have hs := toom_sizes (r := r) (a := a) (b := a) (k := k) hk.2.2.2 (by lia)
  let n := a.size + a.size
  let a₀ := a.slice 0 k
  let a₁ := a.slice k (k + k)
  let a₂ := a.slice (k + k) a.size
  let arr := sq (r.slice 0 (k + k)) a₀ (by
    rw [USlice.size_slice _ (by simp) (by lia), USize.toNat_zero]; lia)
  let arr := sq ((arr.uslice r.start r.stop).slice (4 * k) n) a₂ (by
    rw [USlice.size_slice _ (by rw [hs.1]; lia) (Nat.le_refl _), hs.1]; lia)
  let w (j : UInt64) := sq (UInt64Array.replicate (k + k + 2).toNat 0).toUSlice
    (eval3 a₀ a₁ a₂ (k + 1) j).toUSlice (by
      rw [eval_toUSlice_size (size_eval3 ..), hs.2.1]; lia)
  interp4 arr r n k (w 1) (w 2) (w 3)

/-- The Toom-4 square: `a` in four pieces of `k` limbs, at most, the top one nonempty. -/
public def toom4Sqr (r a : USlice) (k : USize) (hk : Shape4S r a k) (sq : Sqr a.size.toNat) :
    UInt64Array :=
  have hs := toom_sizes (r := r) (a := a) (b := a) (k := k) hk.2.2.2 (by lia)
  have h3k : (3 * k).toNat = 3 * k.toNat := toNat_mul_k k 3 (by decide) a.size (by lia)
  let n := a.size + a.size
  let a₀ := a.slice 0 k
  let a₁ := a.slice k (k + k)
  let a₂ := a.slice (k + k) (3 * k)
  let a₃ := a.slice (3 * k) a.size
  let arr := sq (r.slice 0 (k + k)) a₀ (by
    rw [USlice.size_slice _ (by simp) (by lia), USize.toNat_zero]; lia)
  let arr := sq ((arr.uslice r.start r.stop).slice (6 * k) n) a₃ (by
    rw [USlice.size_slice _ (by rw [h3k]; lia) (Nat.le_refl _), h3k]; lia)
  let w (j : UInt64) := sq (UInt64Array.replicate (k + k + 2).toNat 0).toUSlice
    (eval4 a₀ a₁ a₂ a₃ (k + 1) j).toUSlice (by
      rw [eval_toUSlice_size (size_eval4 ..), hs.2.1]; lia)
  interp6 arr r n k (w 1) (w 2) (w 3) (w 4) (w 5)

/-- The square of an evaluation, into a new array of `2 k + 2` limbs. -/
private theorem sqr_at {N : Nat} (sq : Sqr N)
    (hsq : ∀ r' a' h', MulOK (sq r' a' h') r' a' a') (k : USize)
    (hk : (k + 1).toNat = k.toNat + 1) (hkk : (k + k + 2).toNat = 2 * k.toNat + 2)
    (EA : UInt64Array) (hA : EA.size = (k + 1).toNat) (h : EA.toUSlice.size.toNat < N) :
    (sq (UInt64Array.replicate (k + k + 2).toNat 0).toUSlice EA.toUSlice h).size =
        2 * k.toNat + 2 ∧
      (sq (UInt64Array.replicate (k + k + 2).toNat 0).toUSlice EA.toUSlice h).valAt
        0 (2 * k.toNat + 2) = EA.valAt 0 (k.toNat + 1) * EA.valAt 0 (k.toNat + 1) := by
  obtain ⟨z₁, z₂, -, z₄⟩ := zeros (k + k + 2)
  obtain ⟨s, -, v⟩ := hsq (UInt64Array.replicate (k + k + 2).toNat 0).toUSlice EA.toUSlice h
  have hS := (k + 1).toNat_lt_size
  have sA := size_toUSlice EA (by rw [hA]; exact hS)
  rw [UInt64Array.array_toUSlice, z₄] at s
  rw [z₁, sA, hA, hk, toUSlice_toNat _ (by rw [hA]; exact hS), UInt64Array.toNat_eq_valAt, hA, hk,
    show k.toNat + 1 + (k.toNat + 1) = 2 * k.toNat + 2 by lia] at v
  have hp : 0 < EA.toUSlice.size :=
    USize.lt_iff_toNat_lt.2 (by rw [sA, hA, hk, USize.toNat_zero]; lia)
  refine ⟨s.trans hkk, v hp hp ?_⟩
  rw [z₂, hkk]; lia

set_option maxHeartbeats 800000 in
private theorem toom3Sqr_spec (r a : USlice) (k : USize) (hk : Shape3S r a k)
    (sq : Sqr a.size.toNat) (hsq : ∀ r' a' h', MulOK (sq r' a' h') r' a' a') :
    MulOK (toom3Sqr r a k hk sq) r a a := by
  obtain ⟨hk₁, ha₁, ha₂, hr⟩ := hk
  obtain ⟨hkk, hk1, hkk2, hn⟩ := toom_sizes (r := r) (a := a) (b := a) (k := k) hr (by lia)
  have hnS := r.size.toNat_lt_size
  have hT : (4 * k).toNat = 4 * k.toNat := toNat_mul_k k 4 (by decide) r.size (by lia)
  have h3k : (3 * k).toNat = 3 * k.toNat := toNat_mul_k k 3 (by decide) r.size (by lia)
  dsimp only [toom3Sqr]
  -- The pieces.
  have pa₀ := (a.size_slice (i := 0) (j := k) (by simp) (by lia) :)
  have pa₁ := (a.size_slice (i := k) (j := (k + k)) (by lia) (by lia) :)
  have pa₂ := (a.size_slice (i := (k + k)) (j := a.size) (by lia) (Nat.le_refl _) :)
  simp only [USize.toNat_zero, Nat.sub_zero, hkk] at pa₀ pa₁ pa₂
  have hA := toNat_whole a
  rw [toNat_split a (i := 0) (j := k) (by simp) (by lia)] at hA
  rw [toNat_split a (i := k) (j := (k + k)) (by lia) (by lia)] at hA
  simp only [USize.toNat_zero, Nat.sub_zero, hkk,
    show 2 * k.toNat - k.toNat = k.toNat by lia] at hA
  have hA₀ := slice_lt (a.slice 0 k) (K := k.toNat) (by lia)
  have hA₁ := slice_lt (a.slice k (k + k)) (K := k.toNat) (by lia)
  have hA₂ := slice_lt (a.slice (k + k) a.size) (K := k.toNat) (by lia)
  generalize eA₀ : (a.slice 0 k).toNat = A₀ at *
  generalize eA₁ : (a.slice k (k + k)).toNat = A₁ at *
  generalize eA₂ : (a.slice (k + k) a.size).toNat = A₂ at *
  -- `c₀ = a₀²` into the low limbs of `r`.
  have hd₁ : (a.slice 0 k).size.toNat < a.size.toNat := by lia
  obtain ⟨m₁s, m₁u, m₁v⟩ := hsq (r.slice 0 (k + k)) (a.slice 0 k) hd₁
  have hW₀s := r.start_slice (i := 0) (j := k + k) (by simp) (by lia)
  have hW₀z := r.size_slice (i := 0) (j := k + k) (by simp) (by lia)
  simp only [USize.toNat_zero, Nat.add_zero, Nat.sub_zero, hkk] at hW₀s hW₀z
  simp only [USlice.array_slice] at m₁s m₁u m₁v
  rw [hW₀s, pa₀] at m₁u m₁v
  rw [hW₀z, eA₀] at m₁v
  replace m₁v := m₁v (USize.lt_iff_toNat_lt.2 (by rw [pa₀, USize.toNat_zero]; lia))
    (USize.lt_iff_toNat_lt.2 (by rw [pa₀, USize.toNat_zero]; lia)) (by lia)
  generalize sq (r.slice 0 (k + k)) (a.slice 0 k) hd₁ = R₁ at *
  -- The top coefficient into the top limbs.
  obtain ⟨x₁, x₂, x₃, -⟩ := window R₁ r m₁s (i := 4 * k) (j := a.size + a.size)
    (by rw [hT, hn]; lia) (by rw [hn]; lia)
  rw [hT] at x₂ x₃
  rw [hn] at x₃
  have hd₂ : (a.slice (k + k) a.size).size.toNat < a.size.toNat := by lia
  obtain ⟨m₂s, m₂u, m₂v⟩ := hsq ((R₁.uslice r.start r.stop).slice (4 * k) (a.size + a.size))
    (a.slice (k + k) a.size) hd₂
  rw [x₁, m₁s] at m₂s
  rw [x₁, x₂, pa₂] at m₂u
  rw [x₂, x₃, pa₂, eA₂] at m₂v
  replace m₂v := m₂v (USize.lt_iff_toNat_lt.2 (by rw [pa₂, USize.toNat_zero]; lia))
    (USize.lt_iff_toNat_lt.2 (by rw [pa₂, USize.toNat_zero]; lia)) (by lia)
  generalize sq ((R₁.uslice r.start r.stop).slice (4 * k) (a.size + a.size))
    (a.slice (k + k) a.size) hd₂ = R₂ at *
  have hc₀ : R₂.valAt r.start.toNat (2 * k.toNat) = A₀ * A₀ := by
    rw [← m₁v, show k.toNat + k.toNat = 2 * k.toNat by lia]
    exact UInt64Array.valAt_congr _ fun i _ hi => m₂u i (by lia)
  have hc₄ : R₂.valAt (r.start.toNat + 4 * k.toNat)
      ((a.size + a.size).toNat - 4 * k.toNat) = A₂ * A₂ := by
    rw [← m₂v, hn]; congr 1; lia
  -- The evaluations and their squares.
  have pA (j : UInt64) (hj : j.toNat ≤ 5) :=
    eval3_at (a.slice 0 k) (a.slice k (k + k)) (a.slice (k + k) a.size)
       k j hk1
      (by lia) (by lia) (by lia) hj
  rw [eA₀, eA₁, eA₂] at pA
  have hdw (EA : UInt64Array) (hA' : EA.size = (k + 1).toNat) :
      EA.toUSlice.size.toNat < a.size.toNat := by
    rw [eval_toUSlice_size hA', hk1]; lia
  obtain ⟨w1s, w1v⟩ := sqr_at sq hsq k hk1 hkk2
    (eval3 (a.slice 0 k) (a.slice k (k + k)) (a.slice (k + k) a.size) (k + 1) 1)
    (size_eval3 ..) (hdw _ (size_eval3 ..))
  rw [pA 1 (by decide)] at w1v
  obtain ⟨w2s, w2v⟩ := sqr_at sq hsq k hk1 hkk2
    (eval3 (a.slice 0 k) (a.slice k (k + k)) (a.slice (k + k) a.size) (k + 1) 2)
    (size_eval3 ..) (hdw _ (size_eval3 ..))
  rw [pA 2 (by decide)] at w2v
  obtain ⟨w3s, w3v⟩ := sqr_at sq hsq k hk1 hkk2
    (eval3 (a.slice 0 k) (a.slice k (k + k)) (a.slice (k + k) a.size) (k + 1) 3)
    (size_eval3 ..) (hdw _ (size_eval3 ..))
  rw [pA 3 (by decide)] at w3v
  simp only [show (1 : UInt64).toNat = 1 from rfl,
    show (2 : UInt64).toNat = 2 from rfl,
    show (3 : UInt64).toNat = 3 from rfl] at w1v w2v w3v
  -- The interpolation.
  generalize hX : 2 ^ (64 * k.toNat) = X at *
  have hXX : 2 ^ (64 * (2 * k.toNat)) = X * X := by rw [← hX, ← Nat.pow_add]; congr 1; lia
  have hX3 : 2 ^ (64 * (3 * k.toNat)) = X * X * X := by
    rw [← hX, ← Nat.pow_add, ← Nat.pow_add]; congr 1; lia
  have hX4 : 2 ^ (64 * (4 * k.toNat)) = X * X * X * X := by
    rw [← hX, ← Nat.pow_add, ← Nat.pow_add, ← Nat.pow_add]; congr 1; lia
  have hval : a.toNat * a.toNat =
      A₀ * A₀ +
      X * (A₀ * A₁ + A₁ * A₀) +
      X * X * (A₀ * A₂ + A₁ * A₁ + A₂ * A₀) +
      X * X * X * (A₁ * A₂ + A₂ * A₁) +
      X * X * X * X * (A₂ * A₂) := by
    rw [hA]; grind
  have hab : a.toNat * a.toNat < 2 ^ (64 * (a.size.toNat + a.size.toNat)) := by
    rw [Nat.mul_add, Nat.pow_add]
    exact Nat.mul_lt_mul_of_lt_of_lt (slice_lt a (Nat.le_refl _)) (slice_lt a (Nat.le_refl _))
  have hbm : (A₀ + A₁ * 3 + A₂ * (3 * 3)) * (A₀ + A₁ * 3 + A₂ * (3 * 3)) <
      2 ^ (64 * (2 * k.toNat + 2 - 1)) := by
    rw [show 2 * k.toNat + 2 - 1 = 2 * k.toNat + 1 by lia, pow_succ_k, hXX]
    have := Nat.mul_lt_mul_of_lt_of_lt
      (show A₀ + A₁ * 3 + A₂ * (3 * 3) < 13 * X by lia)
      (show A₀ + A₁ * 3 + A₂ * (3 * 3) < 13 * X by lia)
    rw [show 13 * X * (13 * X) = 169 * (X * X) by grind] at this
    generalize X * X = Y at *
    lia
  obtain ⟨f₁, f₂, f₃⟩ := interp4_spec R₂ r (a.size + a.size) k _ _ _ (2 * k.toNat + 2)
    (A₀ * A₀) (A₀ * A₁ + A₁ * A₀) (A₀ * A₂ + A₁ * A₁ + A₂ * A₀) (A₁ * A₂ + A₂ * A₁) (A₂ * A₂)
    m₂s (by rw [hn]; lia) (by rw [hn]; lia) hk₁ (by have := (k + k + 2).toNat_lt_size; lia)
    (by lia) w1s w2s w3s (by lia) (by rw [hn]; lia) hc₀ hc₄
    (by rw [w1v]; grind)
    (by rw [w2v]; grind)
    (by rw [w3v]; grind)
    (by refine Nat.lt_of_le_of_lt (Nat.le_of_eq ?_) hbm; grind)
    (by rw [hX, hXX, hX3, hX4, hn, ← hval]; exact hab)
  rw [hn, hX, hXX, hX3, hX4, ← hval] at f₃
  refine ⟨f₁, fun i hi => ?_, fun _ _ _ => f₃⟩
  rw [f₂ i (by rw [hn]; lia), m₂u i (by lia), m₁u i (by lia)]

set_option maxHeartbeats 800000 in
private theorem toom4Sqr_spec (r a : USlice) (k : USize) (hk : Shape4S r a k)
    (sq : Sqr a.size.toNat) (hsq : ∀ r' a' h', MulOK (sq r' a' h') r' a' a') :
    MulOK (toom4Sqr r a k hk sq) r a a := by
  obtain ⟨hk₁, ha₁, ha₂, hr⟩ := hk
  obtain ⟨hkk, hk1, hkk2, hn⟩ := toom_sizes (r := r) (a := a) (b := a) (k := k) hr (by lia)
  have hnS := r.size.toNat_lt_size
  have hT : (6 * k).toNat = 6 * k.toNat := toNat_mul_k k 6 (by decide) r.size (by lia)
  have h3k : (3 * k).toNat = 3 * k.toNat := toNat_mul_k k 3 (by decide) r.size (by lia)
  dsimp only [toom4Sqr]
  -- The pieces.
  have pa₀ := (a.size_slice (i := 0) (j := k) (by simp) (by lia) :)
  have pa₁ := (a.size_slice (i := k) (j := (k + k)) (by lia) (by lia) :)
  have pa₂ := (a.size_slice (i := (k + k)) (j := (3 * k)) (by lia) (by lia) :)
  have pa₃ := (a.size_slice (i := (3 * k)) (j := a.size) (by lia) (Nat.le_refl _) :)
  simp only [USize.toNat_zero, Nat.sub_zero, hkk, h3k] at pa₀ pa₁ pa₂ pa₃
  have hA := toNat_whole a
  rw [toNat_split a (i := 0) (j := k) (by simp) (by lia)] at hA
  rw [toNat_split a (i := k) (j := (k + k)) (by lia) (by lia)] at hA
  rw [toNat_split a (i := (k + k)) (j := (3 * k)) (by lia) (by lia)] at hA
  simp only [USize.toNat_zero, Nat.sub_zero, hkk, h3k,
    show 2 * k.toNat - k.toNat = k.toNat by lia,
    show 3 * k.toNat - 2 * k.toNat = k.toNat by lia] at hA
  have hA₀ := slice_lt (a.slice 0 k) (K := k.toNat) (by lia)
  have hA₁ := slice_lt (a.slice k (k + k)) (K := k.toNat) (by lia)
  have hA₂ := slice_lt (a.slice (k + k) (3 * k)) (K := k.toNat) (by lia)
  have hA₃ := slice_lt (a.slice (3 * k) a.size) (K := k.toNat) (by lia)
  generalize eA₀ : (a.slice 0 k).toNat = A₀ at *
  generalize eA₁ : (a.slice k (k + k)).toNat = A₁ at *
  generalize eA₂ : (a.slice (k + k) (3 * k)).toNat = A₂ at *
  generalize eA₃ : (a.slice (3 * k) a.size).toNat = A₃ at *
  -- `c₀ = a₀²` into the low limbs of `r`.
  have hd₁ : (a.slice 0 k).size.toNat < a.size.toNat := by lia
  obtain ⟨m₁s, m₁u, m₁v⟩ := hsq (r.slice 0 (k + k)) (a.slice 0 k) hd₁
  have hW₀s := r.start_slice (i := 0) (j := k + k) (by simp) (by lia)
  have hW₀z := r.size_slice (i := 0) (j := k + k) (by simp) (by lia)
  simp only [USize.toNat_zero, Nat.add_zero, Nat.sub_zero, hkk] at hW₀s hW₀z
  simp only [USlice.array_slice] at m₁s m₁u m₁v
  rw [hW₀s, pa₀] at m₁u m₁v
  rw [hW₀z, eA₀] at m₁v
  replace m₁v := m₁v (USize.lt_iff_toNat_lt.2 (by rw [pa₀, USize.toNat_zero]; lia))
    (USize.lt_iff_toNat_lt.2 (by rw [pa₀, USize.toNat_zero]; lia)) (by lia)
  generalize sq (r.slice 0 (k + k)) (a.slice 0 k) hd₁ = R₁ at *
  -- The top coefficient into the top limbs.
  obtain ⟨x₁, x₂, x₃, -⟩ := window R₁ r m₁s (i := 6 * k) (j := a.size + a.size)
    (by rw [hT, hn]; lia) (by rw [hn]; lia)
  rw [hT] at x₂ x₃
  rw [hn] at x₃
  have hd₂ : (a.slice (3 * k) a.size).size.toNat < a.size.toNat := by lia
  obtain ⟨m₂s, m₂u, m₂v⟩ := hsq ((R₁.uslice r.start r.stop).slice (6 * k) (a.size + a.size))
    (a.slice (3 * k) a.size) hd₂
  rw [x₁, m₁s] at m₂s
  rw [x₁, x₂, pa₃] at m₂u
  rw [x₂, x₃, pa₃, eA₃] at m₂v
  replace m₂v := m₂v (USize.lt_iff_toNat_lt.2 (by rw [pa₃, USize.toNat_zero]; lia))
    (USize.lt_iff_toNat_lt.2 (by rw [pa₃, USize.toNat_zero]; lia)) (by lia)
  generalize sq ((R₁.uslice r.start r.stop).slice (6 * k) (a.size + a.size))
    (a.slice (3 * k) a.size) hd₂ = R₂ at *
  have hc₀ : R₂.valAt r.start.toNat (2 * k.toNat) = A₀ * A₀ := by
    rw [← m₁v, show k.toNat + k.toNat = 2 * k.toNat by lia]
    exact UInt64Array.valAt_congr _ fun i _ hi => m₂u i (by lia)
  have hc₄ : R₂.valAt (r.start.toNat + 6 * k.toNat)
      ((a.size + a.size).toNat - 6 * k.toNat) = A₃ * A₃ := by
    rw [← m₂v, hn]; congr 1; lia
  -- The evaluations and their squares.
  have pA (j : UInt64) (hj : j.toNat ≤ 5) :=
    eval4_at (a.slice 0 k) (a.slice k (k + k)) (a.slice (k + k) (3 * k))
      (a.slice (3 * k) a.size) k j hk1
      (by lia) (by lia) (by lia) (by lia) hj
  rw [eA₀, eA₁, eA₂, eA₃] at pA
  have hdw (EA : UInt64Array) (hA' : EA.size = (k + 1).toNat) :
      EA.toUSlice.size.toNat < a.size.toNat := by
    rw [eval_toUSlice_size hA', hk1]; lia
  obtain ⟨w1s, w1v⟩ := sqr_at sq hsq k hk1 hkk2
    (eval4 (a.slice 0 k) (a.slice k (k + k)) (a.slice (k + k) (3 * k))
      (a.slice (3 * k) a.size) (k + 1) 1)
    (size_eval4 ..) (hdw _ (size_eval4 ..))
  rw [pA 1 (by decide)] at w1v
  obtain ⟨w2s, w2v⟩ := sqr_at sq hsq k hk1 hkk2
    (eval4 (a.slice 0 k) (a.slice k (k + k)) (a.slice (k + k) (3 * k))
      (a.slice (3 * k) a.size) (k + 1) 2)
    (size_eval4 ..) (hdw _ (size_eval4 ..))
  rw [pA 2 (by decide)] at w2v
  obtain ⟨w3s, w3v⟩ := sqr_at sq hsq k hk1 hkk2
    (eval4 (a.slice 0 k) (a.slice k (k + k)) (a.slice (k + k) (3 * k))
      (a.slice (3 * k) a.size) (k + 1) 3)
    (size_eval4 ..) (hdw _ (size_eval4 ..))
  rw [pA 3 (by decide)] at w3v
  obtain ⟨w4s, w4v⟩ := sqr_at sq hsq k hk1 hkk2
    (eval4 (a.slice 0 k) (a.slice k (k + k)) (a.slice (k + k) (3 * k))
      (a.slice (3 * k) a.size) (k + 1) 4)
    (size_eval4 ..) (hdw _ (size_eval4 ..))
  rw [pA 4 (by decide)] at w4v
  obtain ⟨w5s, w5v⟩ := sqr_at sq hsq k hk1 hkk2
    (eval4 (a.slice 0 k) (a.slice k (k + k)) (a.slice (k + k) (3 * k))
      (a.slice (3 * k) a.size) (k + 1) 5)
    (size_eval4 ..) (hdw _ (size_eval4 ..))
  rw [pA 5 (by decide)] at w5v
  simp only [show (1 : UInt64).toNat = 1 from rfl,
    show (2 : UInt64).toNat = 2 from rfl,
    show (3 : UInt64).toNat = 3 from rfl,
    show (4 : UInt64).toNat = 4 from rfl,
    show (5 : UInt64).toNat = 5 from rfl] at w1v w2v w3v w4v w5v
  -- The interpolation.
  generalize hX : 2 ^ (64 * k.toNat) = X at *
  have hXX : 2 ^ (64 * (2 * k.toNat)) = X * X := by rw [← hX, ← Nat.pow_add]; congr 1; lia
  have hX3 : 2 ^ (64 * (3 * k.toNat)) = X * X * X := by
    rw [← hX, ← Nat.pow_add, ← Nat.pow_add]; congr 1; lia
  have hX4 : 2 ^ (64 * (4 * k.toNat)) = X * X * X * X := by
    rw [← hX, ← Nat.pow_add, ← Nat.pow_add, ← Nat.pow_add]; congr 1; lia
  have hX5 : 2 ^ (64 * (5 * k.toNat)) = X * X * X * X * X := by
    rw [← hX, ← Nat.pow_add, ← Nat.pow_add, ← Nat.pow_add, ← Nat.pow_add]; congr 1; lia
  have hX6 : 2 ^ (64 * (6 * k.toNat)) = X * X * X * X * X * X := by
    rw [← hX, ← Nat.pow_add, ← Nat.pow_add, ← Nat.pow_add, ← Nat.pow_add, ← Nat.pow_add]
    congr 1; lia
  have hval : a.toNat * a.toNat =
      A₀ * A₀ +
      X * (A₀ * A₁ + A₁ * A₀) +
      X * X * (A₀ * A₂ + A₁ * A₁ + A₂ * A₀) +
      X * X * X * (A₀ * A₃ + A₁ * A₂ + A₂ * A₁ + A₃ * A₀) +
      X * X * X * X * (A₁ * A₃ + A₂ * A₂ + A₃ * A₁) +
      X * X * X * X * X * (A₂ * A₃ + A₃ * A₂) +
      X * X * X * X * X * X * (A₃ * A₃) := by
    rw [hA]; grind
  have hab : a.toNat * a.toNat < 2 ^ (64 * (a.size.toNat + a.size.toNat)) := by
    rw [Nat.mul_add, Nat.pow_add]
    exact Nat.mul_lt_mul_of_lt_of_lt (slice_lt a (Nat.le_refl _)) (slice_lt a (Nat.le_refl _))
  obtain ⟨f₁, f₂, f₃⟩ := interp6_spec R₂ r (a.size + a.size) k _ _ _ _ _ (2 * k.toNat + 2)
    (A₀ * A₀) (A₀ * A₁ + A₁ * A₀) (A₀ * A₂ + A₁ * A₁ + A₂ * A₀)
    (A₀ * A₃ + A₁ * A₂ + A₂ * A₁ + A₃ * A₀) (A₁ * A₃ + A₂ * A₂ + A₃ * A₁) (A₂ * A₃ + A₃ * A₂)
    (A₃ * A₃)
    m₂s (by rw [hn]; lia) (by rw [hn]; lia) hk₁ (by have := (k + k + 2).toNat_lt_size; lia)
    w1s w2s w3s w4s w5s (by lia) (by rw [hn]; lia) hc₀ hc₄
    (by rw [w1v]; grind)
    (by rw [w2v]; grind)
    (by rw [w3v]; grind)
    (by rw [w4v]; grind)
    (by rw [w5v]; grind)
    (by rw [hX, hXX, hX3, hX4, hX5, hX6, hn, ← hval]; exact hab)
  rw [hn, hX, hXX, hX3, hX4, hX5, hX6, ← hval] at f₃
  refine ⟨f₁, fun i hi => ?_, fun _ _ _ => f₃⟩
  rw [f₂ i (by rw [hn]; lia), m₂u i (by lia), m₁u i (by lia)]

/-- The pieces of the Toom squares as `Nat`s. -/
private theorem sqr_guard {r a : USlice} (h : a.size.toNat + a.size.toNat ≤ r.size.toNat) :
    ((a.size + 2) / 3).toNat = (a.size.toNat + 2) / 3 ∧
      ((a.size + 3) / 4).toNat = (a.size.toNat + 3) / 4 := by
  have : 4294967296 ≤ USize.size := by cases USize.size_eq <;> lia
  have := r.size.toNat_lt_size
  have hc2 : (2 : USize).toNat = 2 := by
    rw [USize.toNat_ofNat, Nat.mod_eq_of_lt (by simp only [USize.size] at this; lia)]
  have hc3 : (3 : USize).toNat = 3 := by
    rw [USize.toNat_ofNat, Nat.mod_eq_of_lt (by simp only [USize.size] at this; lia)]
  have hc4 : (4 : USize).toNat = 4 := by
    rw [USize.toNat_ofNat, Nat.mod_eq_of_lt (by simp only [USize.size] at this; lia)]
  refine ⟨?_, ?_⟩
  · rw [USize.toNat_div, USize.toNat_add_of_lt (by rw [hc2]; lia), hc2, hc3]
  · rw [USize.toNat_div, USize.toNat_add_of_lt (by rw [hc3]; lia), hc3, hc4]

/-- `sqrToom`, recursively. -/
def sqrToomAux (r a : USlice) : UInt64Array :=
  let sq : Sqr a.size.toNat := fun r' a' _ => sqrToomAux r' a'
  if h : toom3SqrThreshold ≤ a.size.toNat ∧ a.size.toNat + a.size.toNat ≤ r.size.toNat then
    have hg := sqr_guard h.2
    if toom4SqrThreshold ≤ a.size.toNat then
      toom4Sqr r a ((a.size + 3) / 4) (by
        simp only [toom3SqrThreshold] at *
        refine ⟨?_, ?_, ?_, ?_⟩ <;> lia) sq
    else
      toom3Sqr r a ((a.size + 2) / 3) (by
        simp only [toom3SqrThreshold] at *
        refine ⟨?_, ?_, ?_, ?_⟩ <;> lia) sq
  else
    sqrKaratsuba r a
termination_by a.size.toNat
decreasing_by all_goals lia

private theorem sqrKaratsuba_ok (r a : USlice) : MulOK (sqrKaratsuba r a) r a a := by
  refine ⟨size_sqrKaratsuba r a, fun i hi => getElem!_sqrKaratsuba r a i (by lia),
    fun ha _ hr => ?_⟩
  rw [← Nat.two_mul]
  exact valAt_sqrKaratsuba r a ha (by lia)

private theorem sqrToomAux_spec (r a : USlice) : MulOK (sqrToomAux r a) r a a := by
  have hsq (r' a' : USlice) (h' : a'.size.toNat < a.size.toNat) :
      MulOK (sqrToomAux r' a') r' a' a' := sqrToomAux_spec r' a'
  rw [sqrToomAux]
  split
  · split
    · exact toom4Sqr_spec _ _ _ _ _ hsq
    · exact toom3Sqr_spec _ _ _ _ _ hsq
  · exact sqrKaratsuba_ok r a
termination_by a.size.toNat
decreasing_by all_goals lia

/--
Writes the `2 a.size` limbs of `a²` into `r`: by the Toom-4 square from `toom4SqrThreshold`
limbs, the Toom-3 square from `toom3SqrThreshold`, and `sqrKaratsuba` below. It requires
`0 < a.size` and `2 a.size ≤ r.size`, and leaves `r` unchanged otherwise.
-/
public def sqrToom (r a : USlice) : UInt64Array := sqrToomAux r a

@[simp] public theorem size_sqrToom (r a : USlice) : (sqrToom r a).size = r.array.size :=
  (sqrToomAux_spec r a).1

/-- `sqrToom` leaves the limbs of `r` outside the ones it writes unchanged. -/
public theorem getElem!_sqrToom (r a : USlice) (i : Nat)
    (hi : i < r.start.toNat ∨ r.start.toNat + 2 * a.size.toNat ≤ i) :
    (sqrToom r a)[i]! = r.array[i]! :=
  (sqrToomAux_spec r a).2.1 i (by lia)

public theorem valAt_sqrToom (r a : USlice) (ha : 0 < a.size)
    (hr : 2 * a.size.toNat ≤ r.size.toNat) :
    (sqrToom r a).valAt r.start.toNat (2 * a.size.toNat) = a.toNat * a.toNat := by
  rw [Nat.two_mul]
  exact (sqrToomAux_spec r a).2.2 ha ha (by lia)

end MPN
