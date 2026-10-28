/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import MPN.Mul.ToomOps
public import MPN.Toom.Karatsuba
public import MPN.Config

/-!
# Karatsuba multiplication

`mulKaratsuba r a b` writes the `a.size + b.size` limbs of `a * b` into the slice `r`, like
`mulBasecase`, by `main`'s `MPN.Toom.mulKaratsuba` on the operations of `toomOps64`: from
`cfg.mulKaratsuba` limbs it splits both operands at `k = ⌈a.size / 2⌉`, computes the three
products recursively, and adds the middle term in one pass (`karatsubaMid`). It requires
`0 < b.size` and `a.size + b.size ≤ r.size`, and leaves `r` unchanged otherwise.
-/

open ScalarArray UInt64Array

namespace MPN

/-- The thresholds of the library, from the `mpn.*` options it is compiled with. -/
public def config : Config := mpn_config%

variable (cfg : Config)

/-- The window `[r.start, r.stop)` of an array of the same size as `r`'s, such as a result. -/
public theorem uslice_same (r : USlice) (arr : UInt64Array) (h : arr.size = r.array.size) :
    (arr.uslice r.start r.stop).start = r.start ∧ (arr.uslice r.start r.stop).size = r.size ∧
      (arr.uslice r.start r.stop).array = arr := by
  have h₁ := uslice_start arr r.start r.stop r.start_le_stop (h ▸ r.stop_le_size)
  have h₂ := uslice_stop arr r.start r.stop (h ▸ r.stop_le_size)
  exact ⟨h₁, by rw [USlice.size, USlice.size, h₁, h₂], rfl⟩

/--
Writes the `a.size + b.size` limbs of `a * b` into `r`, by Karatsuba's method above
`cfg.mulKaratsuba` and by `mulBasecase` below. It requires `0 < b.size` and
`a.size + b.size ≤ r.size`, and leaves `r` unchanged otherwise.
-/
public def mulKaratsuba (cfg : Config) (r a b : USlice) : UInt64Array :=
  if a.size.toNat + b.size.toNat ≤ r.size.toNat then
    Toom.mulKaratsuba cfg.toom r.array r.start.toNat a.array a.start.toNat a.size.toNat b.array
      b.start.toNat b.size.toNat
  else r.array

/-- The spec of `MPN.Toom.mulKaratsuba` on the slices. -/
private theorem spec (r a b : USlice) (h : a.size.toNat + b.size.toNat ≤ r.size.toNat) :
    let d := Toom.mulKaratsuba cfg.toom r.array r.start.toNat a.array a.start.toNat a.size.toNat
      b.array b.start.toNat b.size.toNat
    Toom.Writes d r.array r.start.toNat (a.size.toNat + b.size.toNat) ∧
      d.valAt r.start.toNat (a.size.toNat + b.size.toNat) = a.toNat * b.toNat := by
  have := r.toNat_size; have := r.stop_le_size; have := USize.le_iff_toNat_le.1 r.start_le_stop
  rw [USlice.toNat_eq_valAt a, USlice.toNat_eq_valAt b]
  exact Toom.mulKaratsuba_spec cfg.toom _ _ _ _ _ _ _ _ _ rfl (by show _ ≤ r.array.size; lia)

@[simp] public theorem size_mulKaratsuba (r a b : USlice) :
    (mulKaratsuba cfg r a b).size = r.array.size := by
  rw [mulKaratsuba]
  split
  · exact (spec cfg r a b (by assumption)).1.1
  · rfl

/-- `mulKaratsuba` leaves the limbs of `r` outside the ones it writes unchanged. -/
public theorem getElem!_mulKaratsuba (r a b : USlice) (i : Nat)
    (hi : i < r.start.toNat ∨ r.start.toNat + a.size.toNat + b.size.toNat ≤ i) :
    (mulKaratsuba cfg r a b)[i]! = r.array[i]! := by
  rw [mulKaratsuba]
  split
  · exact (spec cfg r a b (by assumption)).1.2 i (by lia)
  · rfl

public theorem valAt_mulKaratsuba (r a b : USlice) (_hb : 0 < b.size)
    (hr : a.size.toNat + b.size.toNat ≤ r.size.toNat) :
    (mulKaratsuba cfg r a b).valAt r.start.toNat (a.size.toNat + b.size.toNat) =
      a.toNat * b.toNat := by
  simp only [mulKaratsuba, hr, ↓reduceIte]
  exact (spec cfg r a b hr).2

end MPN
