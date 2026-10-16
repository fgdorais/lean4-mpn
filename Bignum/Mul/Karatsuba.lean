/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bignum.AddDiff

/-!
# Karatsuba multiplication

Splitting `a = a₀ + βᵏ a₁` and `b = b₀ + βᵏ b₁` at `k` limbs, where `β = 2³²`, gives

  `a * b = z₀ + βᵏ (z₁ - z₀ - z₂) + β²ᵏ z₂`

with `z₀ = a₀ b₀`, `z₂ = a₁ b₁` and `z₁ = (a₀ + a₁) (b₀ + b₁)`: three products of about half the
size instead of four. `karatsuba` takes the multiplier for the three products as a parameter, so
the dispatcher can recurse through it, and `karatsuba_spec` assumes only that this multiplier is
correct on the smaller inputs it is given.
-/

open ScalarArray

namespace Bignum

/--
`z₀ + βᵏ (z₁ - z₀ - z₂) + β²ᵏ z₂`, where `z₀` has `2 k` limbs: the middle term is added to
`z₀ ++ z₂` in one pass over `z₁` by `addDiffInto`.
-/
public def karatsubaCombine (k : Nat) (z₀ z₁ z₂ : UInt32Array) : UInt32Array :=
  addDiffInto (z₀ ++ z₂) k z₁ z₀ z₂

public theorem karatsubaCombine_spec (k : Nat) (z₀ z₁ z₂ : UInt32Array) (A₀ A₁ B₀ B₁ : Nat)
    (h₀ : toNat z₀ = A₀ * B₀) (h₁ : toNat z₁ = (A₀ + A₁) * (B₀ + B₁)) (h₂ : toNat z₂ = A₁ * B₁)
    (hs₀ : z₀.size = 2 * k) (hs₀₁ : z₀.size ≤ z₁.size) (hs₂₁ : z₂.size ≤ z₁.size)
    (hfit : k + z₁.size ≤ z₀.size + z₂.size)
    (htotal : (A₀ + 2 ^ (32 * k) * A₁) * (B₀ + 2 ^ (32 * k) * B₁) <
      2 ^ (32 * (z₀.size + z₂.size))) :
    (karatsubaCombine k z₀ z₁ z₂).size = z₀.size + z₂.size ∧
      toNat (karatsubaCombine k z₀ z₁ z₂) =
        (A₀ + 2 ^ (32 * k) * A₁) * (B₀ + 2 ^ (32 * k) * B₁) := by
  have hexp : (A₀ + A₁) * (B₀ + B₁) = A₀ * B₀ + A₁ * B₁ + (A₀ * B₁ + A₁ * B₀) := by
    simp only [Nat.add_mul, Nat.mul_add]
    omega
  -- The middle term `z₁ - z₀ - z₂ = A₀ B₁ + A₁ B₀`.
  have hm : toNat z₁ - toNat z₀ - toNat z₂ = A₀ * B₁ + A₁ * B₀ := by
    rw [h₀, h₁, h₂, hexp]
    omega
  -- `r = z₀ ++ z₂ = z₀ + β²ᵏ z₂`.
  have hrs : (z₀ ++ z₂).size = z₀.size + z₂.size := UInt32Array.size_append _ _
  have hr : toNat (z₀ ++ z₂) = A₀ * B₀ + 2 ^ (32 * (2 * k)) * (A₁ * B₁) := by
    rw [toNat_toSlice, UInt32Array.toList_append, ofLimbs_append, UInt32Array.length_toList, hs₀,
      ← toNat_toSlice, ← toNat_toSlice, h₀, h₂]
  have hpow : 2 ^ (32 * (2 * k)) = 2 ^ (32 * k) * 2 ^ (32 * k) := by
    rw [← Nat.pow_add]
    congr 1
    omega
  have hid : A₀ * B₀ + 2 ^ (32 * (2 * k)) * (A₁ * B₁) + 2 ^ (32 * k) * (A₀ * B₁ + A₁ * B₀) =
      (A₀ + 2 ^ (32 * k) * A₁) * (B₀ + 2 ^ (32 * k) * B₁) := by
    rw [hpow]
    generalize 2 ^ (32 * k) = P
    simp only [Nat.add_mul, Nat.mul_add]
    grind
  obtain ⟨hs, hv⟩ := addDiffInto_spec (z₀ ++ z₂) k z₁ z₀ z₂ (by rw [hrs]; exact hfit) hs₀₁ hs₂₁
    (by rw [h₀, h₁, h₂, hexp]; omega) (by rw [hr, hm, hid, hrs]; exact htotal)
  refine ⟨by rw [karatsubaCombine, hs, hrs], ?_⟩
  rw [karatsubaCombine, hv, hr, hm, hid]

/--
The product `a * b` by one step of Karatsuba, splitting at `k = b.size / 2`, for
`4 ≤ b.size ≤ a.size`. It computes `z₀`, `z₁` and `z₂` with `mulRec`, which only receives inputs
smaller than `a` and `b` together.
-/
public def karatsuba (a b : UInt32Array.Slice) (hb : 4 ≤ b.size) (hab : b.size ≤ a.size)
    (mulRec : (x y : UInt32Array.Slice) → x.size + y.size < a.size + b.size → UInt32Array) :
    UInt32Array :=
  let k := b.size / 2
  let a₀ := a.slice 0 k
  let a₁ := a.slice k a.size
  let b₀ := b.slice 0 k
  let b₁ := b.slice k b.size
  karatsubaCombine k
    (mulRec a₀ b₀ (by simp only [a₀, b₀, UInt32Array.Slice.size_slice]; omega))
    (mulRec (addLimbs a₀ a₁) (addLimbs b₀ b₁)
      (by
        simp only [a₀, a₁, b₀, b₁, UInt32Array.size_toSlice, size_addLimbs,
          UInt32Array.Slice.size_slice]
        omega))
    (mulRec a₁ b₁ (by simp only [a₁, b₁, UInt32Array.Slice.size_slice]; omega))

public theorem karatsuba_spec (a b : UInt32Array.Slice) (hb : 4 ≤ b.size) (hab : b.size ≤ a.size)
    (mulRec : (x y : UInt32Array.Slice) → x.size + y.size < a.size + b.size → UInt32Array)
    (hrec : ∀ x y h, (mulRec x y h).size = x.size + y.size ∧
      toNat (mulRec x y h) = toNat x * toNat y) :
    (karatsuba a b hb hab mulRec).size = a.size + b.size ∧
      toNat (karatsuba a b hb hab mulRec) = toNat a * toNat b := by
  have hk : b.size / 2 ≤ b.size := Nat.div_le_self _ _
  have hsa₀ : (a.slice 0 (b.size / 2)).size = b.size / 2 := by simp; omega
  have hsa₁ : (a.slice (b.size / 2) a.size).size = a.size - b.size / 2 := by simp
  have hsb₀ : (b.slice 0 (b.size / 2)).size = b.size / 2 := by simp; omega
  have hsb₁ : (b.slice (b.size / 2) b.size).size = b.size - b.size / 2 := by simp
  obtain ⟨hs₀, hv₀⟩ := hrec (a.slice 0 (b.size / 2)) (b.slice 0 (b.size / 2)) (by omega)
  obtain ⟨hs₂, hv₂⟩ := hrec (a.slice (b.size / 2) a.size) (b.slice (b.size / 2) b.size)
    (by omega)
  obtain ⟨hs₁, hv₁⟩ := hrec (addLimbs (a.slice 0 (b.size / 2)) (a.slice (b.size / 2) a.size))
    (addLimbs (b.slice 0 (b.size / 2)) (b.slice (b.size / 2) b.size)) (by simp; omega)
  rw [toNat_addLimbs, toNat_addLimbs] at hv₁
  have hS : (addLimbs (a.slice 0 (b.size / 2)) (a.slice (b.size / 2) a.size)).toSlice.size =
      a.size - b.size / 2 + 1 := by
    simp only [UInt32Array.size_toSlice, size_addLimbs, hsa₀, hsa₁]
    omega
  have hT : (addLimbs (b.slice 0 (b.size / 2)) (b.slice (b.size / 2) b.size)).toSlice.size =
      b.size - b.size / 2 + 1 := by
    simp only [UInt32Array.size_toSlice, size_addLimbs, hsb₀, hsb₁]
    omega
  simp only [hS, hT] at hs₁
  -- The parts of `a` and `b` and their bounds.
  have ha := toNat_slice_add_toNat_slice a (b.size / 2) (by omega)
  have hb' := toNat_slice_add_toNat_slice b (b.size / 2) hk
  have hA₀ := toNat_lt (a.slice 0 (b.size / 2))
  have hA₁ := toNat_lt (a.slice (b.size / 2) a.size)
  have hB₀ := toNat_lt (b.slice 0 (b.size / 2))
  have hB₁ := toNat_lt (b.slice (b.size / 2) b.size)
  rw [hsa₀] at hA₀
  rw [hsa₁] at hA₁
  rw [hsb₀] at hB₀
  rw [hsb₁] at hB₁
  have hA := toNat_lt a
  have hB := toNat_lt b
  generalize toNat (a.slice 0 (b.size / 2)) = A₀ at *
  generalize toNat (a.slice (b.size / 2) a.size) = A₁ at *
  generalize toNat (b.slice 0 (b.size / 2)) = B₀ at *
  generalize toNat (b.slice (b.size / 2) b.size) = B₁ at *
  have hsum : (mulRec (a.slice 0 (b.size / 2)) (b.slice 0 (b.size / 2)) (by omega)).size +
      (mulRec (a.slice (b.size / 2) a.size) (b.slice (b.size / 2) b.size) (by omega)).size =
      a.size + b.size := by
    rw [hs₀, hs₂]
    omega
  have htot : toNat a * toNat b < 2 ^ (32 * (a.size + b.size)) := by
    rw [Nat.mul_add, Nat.pow_add]
    exact Nat.mul_lt_mul'' hA hB
  have key := karatsubaCombine_spec (b.size / 2) _ _ _ A₀ A₁ B₀ B₁ hv₀ hv₁ hv₂
    (by rw [hs₀, hsa₀, hsb₀]; omega) (by rw [hs₀, hs₁]; omega) (by rw [hs₂, hs₁]; omega)
    (by rw [hsum, hs₁]; omega) (by rw [hsum, ha, hb']; exact htot)
  rw [ha, hb', hsum] at key
  exact key

end Bignum
