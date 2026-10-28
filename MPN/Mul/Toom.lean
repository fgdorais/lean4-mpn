/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import MPN.Mul.Karatsuba
public import MPN.Sqr.Karatsuba
public import MPN.Toom.Mul

/-!
# Toom multiplication

`mulToom cfg r a b` writes the `a.size + b.size` limbs of `a * b` into the slice `r` and
`sqrToom cfg r a` the `2 a.size` limbs of `a²`, by `main`'s `MPN.Toom.mulToom` and
`MPN.Toom.sqrToom` on the operations of `toomOps64`: Toom-6, Toom-4, Toom-4 by 3, Toom-3,
Toom-3 by 2 and Toom-4 by 2 by the sizes and the shape, with interpolations at the natural points
`0, 1, 2, …, ∞`, and `mulKaratsuba` or `sqrKaratsuba` below the thresholds of `cfg`. They require
`a.size + b.size ≤ r.size`, and leave `r` unchanged otherwise.
-/

open ScalarArray UInt64Array

namespace MPN

variable (cfg : Config)

/--
Writes the `a.size + b.size` limbs of `a * b` into `r`, by the Toom methods from the thresholds of
`cfg` and by `mulKaratsuba` below. It requires `a.size + b.size ≤ r.size`, and leaves `r`
unchanged otherwise.
-/
public def mulToom (cfg : Config) (r a b : USlice) : UInt64Array :=
  if a.size.toNat + b.size.toNat ≤ r.size.toNat then
    Toom.mulToom cfg.toom r.array r.start.toNat a.array a.start.toNat a.size.toNat b.array
      b.start.toNat b.size.toNat
  else r.array

/-- The spec of `MPN.Toom.mulToom` on the slices. -/
private theorem spec (r a b : USlice) (h : a.size.toNat + b.size.toNat ≤ r.size.toNat) :
    let d := Toom.mulToom cfg.toom r.array r.start.toNat a.array a.start.toNat a.size.toNat
      b.array b.start.toNat b.size.toNat
    Toom.Writes d r.array r.start.toNat (a.size.toNat + b.size.toNat) ∧
      d.valAt r.start.toNat (a.size.toNat + b.size.toNat) = a.toNat * b.toNat := by
  have := r.toNat_size; have := r.stop_le_size; have := USize.le_iff_toNat_le.1 r.start_le_stop
  rw [USlice.toNat_eq_valAt a, USlice.toNat_eq_valAt b]
  exact Toom.mulToom_spec cfg.toom _ _ _ _ _ _ _ _ (by show _ ≤ r.array.size; lia)

/-- `mulToom` keeps the size of the array of `r`. -/
@[simp] public theorem size_mulToom (r a b : USlice) : (mulToom cfg r a b).size = r.array.size := by
  rw [mulToom]
  split
  · exact (spec cfg r a b (by assumption)).1.1
  · rfl

/-- `mulToom` leaves the limbs of `r` outside the ones it writes unchanged. -/
public theorem getElem!_mulToom (r a b : USlice) (i : Nat)
    (hi : i < r.start.toNat ∨ r.start.toNat + a.size.toNat + b.size.toNat ≤ i) :
    (mulToom cfg r a b)[i]! = r.array[i]! := by
  rw [mulToom]
  split
  · exact (spec cfg r a b (by assumption)).1.2 i (by lia)
  · rfl

public theorem valAt_mulToom (r a b : USlice) (_ha : 0 < a.size) (_hb : 0 < b.size)
    (hr : a.size.toNat + b.size.toNat ≤ r.size.toNat) :
    (mulToom cfg r a b).valAt r.start.toNat (a.size.toNat + b.size.toNat) = a.toNat * b.toNat := by
  simp only [mulToom, hr, ↓reduceIte]
  exact (spec cfg r a b hr).2

/--
Writes the `2 a.size` limbs of `a²` into `r`, by the Toom squares from the thresholds of `cfg`
and by `sqrKaratsuba` below. It requires `2 a.size ≤ r.size`, and leaves `r` unchanged
otherwise.
-/
public def sqrToom (cfg : Config) (r a : USlice) : UInt64Array :=
  if 2 * a.size.toNat ≤ r.size.toNat then
    Toom.sqrToom cfg.toom r.array r.start.toNat a.array a.start.toNat a.size.toNat
  else r.array

/-- The spec of `MPN.Toom.sqrToom` on the slices. -/
private theorem sqrSpec (r a : USlice) (h : 2 * a.size.toNat ≤ r.size.toNat) :
    let d := Toom.sqrToom cfg.toom r.array r.start.toNat a.array a.start.toNat a.size.toNat
    Toom.Writes d r.array r.start.toNat (a.size.toNat + a.size.toNat) ∧
      d.valAt r.start.toNat (a.size.toNat + a.size.toNat) = a.toNat * a.toNat := by
  have := r.toNat_size; have := r.stop_le_size; have := USize.le_iff_toNat_le.1 r.start_le_stop
  rw [USlice.toNat_eq_valAt a]
  exact Toom.sqrToom_spec cfg.toom _ _ _ _ _ (by show _ ≤ r.array.size; lia)

@[simp] public theorem size_sqrToom (r a : USlice) : (sqrToom cfg r a).size = r.array.size := by
  rw [sqrToom]
  split
  · exact (sqrSpec cfg r a (by assumption)).1.1
  · rfl

/-- `sqrToom` leaves the limbs of `r` outside the ones it writes unchanged. -/
public theorem getElem!_sqrToom (r a : USlice) (i : Nat)
    (hi : i < r.start.toNat ∨ r.start.toNat + 2 * a.size.toNat ≤ i) :
    (sqrToom cfg r a)[i]! = r.array[i]! := by
  rw [sqrToom]
  split
  · exact (sqrSpec cfg r a (by assumption)).1.2 i (by lia)
  · rfl

public theorem valAt_sqrToom (r a : USlice) (_ha : 0 < a.size)
    (hr : 2 * a.size.toNat ≤ r.size.toNat) :
    (sqrToom cfg r a).valAt r.start.toNat (2 * a.size.toNat) = a.toNat * a.toNat := by
  simp only [sqrToom, hr, ↓reduceIte]
  rw [show 2 * a.size.toNat = a.size.toNat + a.size.toNat by lia]
  exact (sqrSpec cfg r a hr).2

end MPN
