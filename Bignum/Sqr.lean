/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bignum.Sqr.Basecase
public import Bignum.Mul

/-!
# Squaring

`sqrLimbs` computes all `2 * a.size` limbs of `a * a` by choosing an algorithm from the size of
`a`, like GMP's `mpn_sqr`, and `sqr` trims its result. Squaring is cheaper than multiplying: the
schoolbook square computes each cross product once, and the Karatsuba square has three smaller
squares instead of three products.

* below `cfg.sqrBasecase` limbs: `mulBasecase a a`, since the extra passes of the schoolbook
  square cost more than they save on small numbers;
* below `cfg.sqrKaratsuba` limbs: the schoolbook `sqrBasecase`;
* below `cfg.sqrToom3` limbs: `karatsubaSqr`, which squares its three smaller numbers with
  `sqrLimbsWith` again;
* otherwise: `toom3Sqr`, which squares its five smaller numbers with `sqrLimbsWith` again.
-/

open ScalarArray

namespace Bignum

/--
The square `a * a` by one step of Karatsuba, splitting at `k = a.size / 2`, for `4 ≤ a.size`. It
computes the three squares with `sqrRec`, which only receives inputs shorter than `a`.
-/
public def karatsubaSqr (a : UInt32Array.Slice) (ha : 4 ≤ a.size)
    (sqrRec : (x : UInt32Array.Slice) → x.size < a.size → UInt32Array) : UInt32Array :=
  let k := a.size / 2
  let a₀ := a.slice 0 k
  let a₁ := a.slice k a.size
  karatsubaCombine k
    (sqrRec a₀ (by simp only [a₀, UInt32Array.Slice.size_slice]; omega))
    (sqrRec (addLimbs a₀ a₁)
      (by
        simp only [a₀, a₁, UInt32Array.size_toSlice, size_addLimbs, UInt32Array.Slice.size_slice]
        omega))
    (sqrRec a₁ (by simp only [a₁, UInt32Array.Slice.size_slice]; omega))

public theorem karatsubaSqr_spec (a : UInt32Array.Slice) (ha : 4 ≤ a.size)
    (sqrRec : (x : UInt32Array.Slice) → x.size < a.size → UInt32Array)
    (hrec : ∀ x h, (sqrRec x h).size = x.size + x.size ∧
      toNat (sqrRec x h) = toNat x * toNat x) :
    (karatsubaSqr a ha sqrRec).size = a.size + a.size ∧
      toNat (karatsubaSqr a ha sqrRec) = toNat a * toNat a := by
  have hk : a.size / 2 ≤ a.size := Nat.div_le_self _ _
  have hs₀ : (a.slice 0 (a.size / 2)).size = a.size / 2 := by simp; omega
  have hs₁ : (a.slice (a.size / 2) a.size).size = a.size - a.size / 2 := by simp
  obtain ⟨hz₀s, hz₀⟩ := hrec (a.slice 0 (a.size / 2)) (by omega)
  obtain ⟨hz₂s, hz₂⟩ := hrec (a.slice (a.size / 2) a.size) (by omega)
  obtain ⟨hz₁s, hz₁⟩ := hrec (addLimbs (a.slice 0 (a.size / 2)) (a.slice (a.size / 2) a.size))
    (by simp; omega)
  rw [toNat_addLimbs] at hz₁
  have hS : (addLimbs (a.slice 0 (a.size / 2)) (a.slice (a.size / 2) a.size)).toSlice.size =
      a.size - a.size / 2 + 1 := by
    simp only [UInt32Array.size_toSlice, size_addLimbs, hs₀, hs₁]
    omega
  simp only [hS] at hz₁s
  have hsplit := toNat_slice_add_toNat_slice a (a.size / 2) hk
  have hA₀ := toNat_lt (a.slice 0 (a.size / 2))
  have hA₁ := toNat_lt (a.slice (a.size / 2) a.size)
  rw [hs₀] at hA₀
  rw [hs₁] at hA₁
  have hA := toNat_lt a
  generalize toNat (a.slice 0 (a.size / 2)) = A₀ at *
  generalize toNat (a.slice (a.size / 2) a.size) = A₁ at *
  have hsum : (sqrRec (a.slice 0 (a.size / 2)) (by omega)).size +
      (sqrRec (a.slice (a.size / 2) a.size) (by omega)).size = a.size + a.size := by
    rw [hz₀s, hz₂s, hs₀, hs₁]
    omega
  have htot : toNat a * toNat a < 2 ^ (32 * (a.size + a.size)) := by
    rw [Nat.mul_add, Nat.pow_add]
    exact Nat.mul_lt_mul'' hA hA
  have key := karatsubaCombine_spec (a.size / 2) _ _ _ A₀ A₁ A₀ A₁ hz₀ hz₁ hz₂
    (by rw [hz₀s, hs₀]; omega) (by rw [hz₀s, hz₁s, hs₀]; omega) (by rw [hz₂s, hz₁s, hs₁]; omega)
    (by rw [hsum, hz₁s]; omega) (by rw [hsum, hsplit]; exact htot)
  rw [hsplit, hsum] at key
  exact key

/-- All `2 * a.size` limbs of `a * a`, untrimmed, with the thresholds of `cfg`. -/
public def sqrLimbsWith (cfg : Config) (a : UInt32Array.Slice) : UInt32Array :=
  if h : cfg.sqrToom3 ≤ a.size then
    toom3Sqr a (Nat.le_trans cfg.twelve_le_sqrToom3 h) fun x _ => sqrLimbsWith cfg x
  else if h : cfg.sqrKaratsuba ≤ a.size then
    karatsubaSqr a (Nat.le_trans cfg.four_le_sqrKaratsuba h) fun x _ => sqrLimbsWith cfg x
  else if cfg.sqrBasecase ≤ a.size then
    sqrBasecase a
  else
    mulBasecase a a
termination_by a.size

public theorem sqrLimbsWith_spec (cfg : Config) (a : UInt32Array.Slice) :
    (sqrLimbsWith cfg a).size = a.size + a.size ∧
      toNat (sqrLimbsWith cfg a) = toNat a * toNat a := by
  induction a using sqrLimbsWith.induct cfg with
  | case1 a h ih =>
    rw [toNat_toSlice, sqrLimbsWith]
    simp only [h, ↓reduceDIte]
    rw [← toNat_toSlice]
    exact toom3Sqr_spec a _ _ fun x hx => ih x hx
  | case2 a h' h ih =>
    rw [toNat_toSlice, sqrLimbsWith]
    simp only [h, h', ↓reduceDIte]
    rw [← toNat_toSlice]
    exact karatsubaSqr_spec a _ _ fun x hx => ih x hx
  | case3 a h₁ h h' =>
    rw [toNat_toSlice, sqrLimbsWith]
    simp only [h₁, h, h', ↓reduceDIte, ↓reduceIte]
    rw [← toNat_toSlice]
    exact sqrBasecase_spec a
  | case4 a h₁ h h' =>
    rw [toNat_toSlice, sqrLimbsWith]
    simp only [h₁, h, h', ↓reduceDIte, ↓reduceIte]
    rw [← toNat_toSlice]
    exact ⟨size_mulBasecase a a, toNat_mulBasecase a a⟩

/-- All `2 * a.size` limbs of `a * a`, untrimmed, like GMP's `mpn_sqr`. -/
public def sqrLimbs (a : UInt32Array.Slice) : UInt32Array := sqrLimbsWith config a

/-- Squares a number. -/
public def sqr (a : UInt32Array.Slice) : UInt32Array := trim (sqrLimbs a)

@[simp] public theorem toNat_sqr (a : UInt32Array.Slice) : toNat (sqr a) = toNat a * toNat a := by
  rw [sqr, toNat_trim, sqrLimbs, (sqrLimbsWith_spec config a).2]

public theorem isTrimmed_sqr (a : UInt32Array.Slice) : isTrimmed (sqr a) = true :=
  isTrimmed_trim _

end Bignum
