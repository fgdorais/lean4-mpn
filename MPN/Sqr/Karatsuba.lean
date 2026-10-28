/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import MPN.Mul.Karatsuba

/-!
# Karatsuba squaring

`sqrKaratsuba r a` writes the `2 a.size` limbs of `a * a` into the slice `r`, like
`mulKaratsuba r a a` but with three squares, by `main`'s `MPN.Toom.sqrKaratsuba`. Below
`cfg.sqrKaratsuba` limbs it is `sqrBasecase`. It requires `0 < a.size` and `2 a.size ≤ r.size`,
and leaves `r` unchanged otherwise.
-/

open ScalarArray UInt64Array

namespace MPN

variable (cfg : Config)

/--
Writes the `2 a.size` limbs of `a * a` into `r`, by Karatsuba's method above
`cfg.sqrKaratsuba` and by `sqrBasecase` below. It requires `0 < a.size` and
`2 a.size ≤ r.size`, and leaves `r` unchanged otherwise.
-/
public def sqrKaratsuba (cfg : Config) (r a : USlice) : UInt64Array :=
  if 2 * a.size.toNat ≤ r.size.toNat then
    Toom.sqrKaratsuba cfg.toom r.array r.start.toNat a.array a.start.toNat a.size.toNat
  else r.array

/-- The spec of `MPN.Toom.sqrKaratsuba` on the slices. -/
private theorem spec (r a : USlice) (h : 2 * a.size.toNat ≤ r.size.toNat) :
    let d := Toom.sqrKaratsuba cfg.toom r.array r.start.toNat a.array a.start.toNat a.size.toNat
    Toom.Writes d r.array r.start.toNat (a.size.toNat + a.size.toNat) ∧
      d.valAt r.start.toNat (a.size.toNat + a.size.toNat) = a.toNat * a.toNat := by
  have := r.toNat_size; have := r.stop_le_size; have := USize.le_iff_toNat_le.1 r.start_le_stop
  rw [USlice.toNat_eq_valAt a]
  exact Toom.sqrKaratsuba_spec cfg.toom _ _ _ _ _ _ rfl (by show _ ≤ r.array.size; lia)

@[simp] public theorem size_sqrKaratsuba (r a : USlice) :
    (sqrKaratsuba cfg r a).size = r.array.size := by
  rw [sqrKaratsuba]
  split
  · exact (spec cfg r a (by assumption)).1.1
  · rfl

/-- `sqrKaratsuba` leaves the limbs of `r` outside the ones it writes unchanged. -/
public theorem getElem!_sqrKaratsuba (r a : USlice) (i : Nat)
    (hi : i < r.start.toNat ∨ r.start.toNat + 2 * a.size.toNat ≤ i) :
    (sqrKaratsuba cfg r a)[i]! = r.array[i]! := by
  rw [sqrKaratsuba]
  split
  · exact (spec cfg r a (by assumption)).1.2 i (by lia)
  · rfl

public theorem valAt_sqrKaratsuba (r a : USlice) (_ha : 0 < a.size)
    (hr : 2 * a.size.toNat ≤ r.size.toNat) :
    (sqrKaratsuba cfg r a).valAt r.start.toNat (2 * a.size.toNat) = a.toNat * a.toNat := by
  simp only [sqrKaratsuba, hr, ↓reduceIte]
  rw [show 2 * a.size.toNat = a.size.toNat + a.size.toNat by lia]
  exact (spec cfg r a hr).2

end MPN
