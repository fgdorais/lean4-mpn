/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import MPN.Mul.ToomOps
public import MPN.Toom.Mul
public import MPN.Config

/-!
# Products and squares by the Toom methods

`mulToomL cfg a b` and `sqrToomL cfg a` are all the limbs of `a * b` and `a * a` in a new array,
by `main`'s `MPN.Toom.mulToom` and `MPN.Toom.sqrToom` on the instance `toomOps32`: Toom-6, Toom-4,
Toom-4 by 3, Toom-3, Toom-3 by 2, Toom-4 by 2 and their squares by the sizes and the shape, down to
Karatsuba and the schoolbook product below the thresholds of `cfg`.
-/

open ScalarArray

namespace MPN

/-- All the limbs of `a * b`, by the Toom methods and Karatsuba. -/
public def mulToomL (cfg : Config) (a b : UInt32Array.Slice) : UInt32Array :=
  Toom.mulToom cfg.toom (UInt32Array.replicate (a.size + b.size) 0) 0 a.array a.start a.size
    b.array b.start b.size

public theorem mulToomL_spec (cfg : Config) (a b : UInt32Array.Slice) :
    (mulToomL cfg a b).size = a.size + b.size ∧ toNat (mulToomL cfg a b) = toNat a * toNat b := by
  have hR : (UInt32Array.replicate (a.size + b.size) 0).size = a.size + b.size := by simp
  obtain ⟨w, v⟩ := Toom.mulToom_spec (A := UInt32Array) cfg.toom
    (UInt32Array.replicate (a.size + b.size) 0) 0 a.array a.start a.size b.array b.start b.size
    (by show _ ≤ (UInt32Array.replicate _ 0).size; rw [hR]; lia)
  have hs : (mulToomL cfg a b).size = a.size + b.size := w.1.trans hR
  refine ⟨hs, ?_⟩
  rw [toNat_array_eq_valAt, hs, toNat_eq_valAt, toNat_eq_valAt]
  exact v

/-- All the limbs of `a * a`, by the Toom squares and Karatsuba. -/
public def sqrToomL (cfg : Config) (a : UInt32Array.Slice) : UInt32Array :=
  Toom.sqrToom cfg.toom (UInt32Array.replicate (a.size + a.size) 0) 0 a.array a.start a.size

public theorem sqrToomL_spec (cfg : Config) (a : UInt32Array.Slice) :
    (sqrToomL cfg a).size = a.size + a.size ∧ toNat (sqrToomL cfg a) = toNat a * toNat a := by
  have hR : (UInt32Array.replicate (a.size + a.size) 0).size = a.size + a.size := by simp
  obtain ⟨w, v⟩ := Toom.sqrToom_spec (A := UInt32Array) cfg.toom
    (UInt32Array.replicate (a.size + a.size) 0) 0 a.array a.start a.size
    (by show _ ≤ (UInt32Array.replicate _ 0).size; rw [hR]; lia)
  have hs : (sqrToomL cfg a).size = a.size + a.size := w.1.trans hR
  refine ⟨hs, ?_⟩
  rw [toNat_array_eq_valAt, hs, toNat_eq_valAt]
  exact v

end MPN
