/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import MPN.Add

/-!
# Unbalanced multiplication

When `a` is at least twice as long as `b`, splitting `a = a₀ + βᵐ a₁` at `m = a.size / 2` limbs
gives `a * b = a₀ b + βᵐ (a₁ b)`. Repeating the split halves `a` until the products are close to
balanced, which the faster algorithms handle well: Karatsuba halves only the shorter operand, so
it alone would be slower than schoolbook on very unbalanced operands.

Halving `a` keeps the work of the splits at `O(a.size log (a.size / b.size))`. Splitting off
`b.size` limbs at a time instead would copy the remaining result at every step, which is quadratic
in `a.size / b.size`. `mulUnbalanced` takes the multiplier as a parameter, like `karatsuba`.
-/

open ScalarArray

namespace MPN

/--
The product `a * b` for `1 ≤ b.size` and `2 * b.size ≤ a.size`, as `a₀ b + βᵐ (a₁ b)` with
`m = a.size / 2`. It computes the two products with `mulRec`, which only receives inputs smaller
than `a` and `b` together.
-/
public def mulUnbalanced (a b : UInt32Array.Slice) (hb : 1 ≤ b.size) (hab : 2 * b.size ≤ a.size)
    (mulRec : (x y : UInt32Array.Slice) → x.size + y.size < a.size + b.size → UInt32Array) :
    UInt32Array :=
  let r₀ := mulRec (a.slice 0 (a.size / 2)) b (by simp only [UInt32Array.Slice.size_slice]; omega)
  let r₁ := mulRec (a.slice (a.size / 2) a.size) b
    (by simp only [UInt32Array.Slice.size_slice]; omega)
  addInto (padZeros r₀ (a.size - a.size / 2)) (a.size / 2) r₁

public theorem mulUnbalanced_spec (a b : UInt32Array.Slice) (hb : 1 ≤ b.size)
    (hab : 2 * b.size ≤ a.size)
    (mulRec : (x y : UInt32Array.Slice) → x.size + y.size < a.size + b.size → UInt32Array)
    (hrec : ∀ x y h, (mulRec x y h).size = x.size + y.size ∧
      toNat (mulRec x y h) = toNat x * toNat y) :
    (mulUnbalanced a b hb hab mulRec).size = a.size + b.size ∧
      toNat (mulUnbalanced a b hb hab mulRec) = toNat a * toNat b := by
  have hs₀ : (a.slice 0 (a.size / 2)).size = a.size / 2 := by simp; omega
  have hs₁ : (a.slice (a.size / 2) a.size).size = a.size - a.size / 2 := by simp
  obtain ⟨hr₀s, hr₀⟩ := hrec (a.slice 0 (a.size / 2)) b (by omega)
  obtain ⟨hr₁s, hr₁⟩ := hrec (a.slice (a.size / 2) a.size) b (by omega)
  have ha := toNat_slice_add_toNat_slice a (a.size / 2) (by omega)
  -- `r₀` padded with zeros up to `a.size + b.size` limbs.
  have hps : (padZeros (mulRec (a.slice 0 (a.size / 2)) b (by omega)) (a.size - a.size / 2)).size =
      a.size + b.size := by
    simp only [size_padZeros, hr₀s, hs₀]
    omega
  have hp : toNat (padZeros (mulRec (a.slice 0 (a.size / 2)) b (by omega)) (a.size - a.size / 2)) =
      toNat (a.slice 0 (a.size / 2)) * toNat b := by
    rw [toNat_padZeros, hr₀]
  have hfit : a.size / 2 + (mulRec (a.slice (a.size / 2) a.size) b (by omega)).toSlice.size ≤
      (padZeros (mulRec (a.slice 0 (a.size / 2)) b (by omega)) (a.size - a.size / 2)).size := by
    simp only [UInt32Array.size_toSlice, hr₁s, hs₁, hps]
    omega
  have hval : toNat (a.slice 0 (a.size / 2)) * toNat b +
      2 ^ (32 * (a.size / 2)) * (toNat (a.slice (a.size / 2) a.size) * toNat b) =
        toNat a * toNat b := by
    rw [← ha, Nat.add_mul, Nat.mul_assoc]
  have hlt : toNat a * toNat b < 2 ^ (32 * (a.size + b.size)) := by
    rw [Nat.mul_add, Nat.pow_add]
    exact Nat.mul_lt_mul'' (toNat_lt a) (toNat_lt b)
  refine ⟨?_, ?_⟩
  · rw [mulUnbalanced, size_addInto _ _ _ hfit, hps]
  · rw [mulUnbalanced, toNat_addInto_of_lt _ _ _ hfit (by rw [hp, hr₁, hval, hps]; exact hlt), hp,
      hr₁, hval]

end MPN
