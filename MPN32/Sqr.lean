/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import MPN32.Arch.SqrBasecase
public import MPN32.Mul

/-!
# Squaring

`sqrLimbs` computes all `2 * a.size` limbs of `a * a` by choosing an algorithm from the size of
`a`, like GMP's `mpn_sqr`, and `sqr` trims its result. Squaring is cheaper than multiplying: the
schoolbook square computes each cross product once, and the Karatsuba and Toom squares have
smaller squares instead of products.

* below `cfg.sqrBasecase` limbs: `mulBasecase a a`, since the extra passes of the schoolbook
  square cost more than they save on small numbers;
* below `cfg.sqrKaratsuba` limbs: the schoolbook `sqrBasecase`;
* otherwise: `MPN`'s `Dispatch.sqr` into a new array, the FFT from `cfg.sqrFFT` limbs and the Toom
  squares and Karatsuba below, from the thresholds `cfg.sqrKaratsuba`, `cfg.sqrToom3`,
  `cfg.sqrToom4` and `cfg.sqrToom6`.
-/

open ScalarArray

namespace MPN.W32

/-- All `2 * a.size` limbs of `a * a`, untrimmed, with the thresholds of `cfg`. -/
public def sqrLimbsWith (cfg : Config) (a : UInt32Array.Slice) : UInt32Array :=
  if cfg.sqrKaratsuba ≤ a.size then
    Dispatch.sqr cfg.mul (UInt32Array.replicate (a.size + a.size) 0) 0 a.array a.start a.size
  else if cfg.sqrBasecase ≤ a.size then
    sqrBasecase a
  else
    mulBasecase a a

public theorem sqrLimbsWith_spec (cfg : Config) (a : UInt32Array.Slice) :
    (sqrLimbsWith cfg a).size = a.size + a.size ∧
      toNat (sqrLimbsWith cfg a) = toNat a * toNat a := by
  by_cases h₁ : cfg.sqrKaratsuba ≤ a.size
  · have e : sqrLimbsWith cfg a = Dispatch.sqr cfg.mul (UInt32Array.replicate (a.size + a.size) 0)
        0 a.array a.start a.size := by simp only [sqrLimbsWith, h₁, ↓reduceIte]
    obtain ⟨⟨s₁, -⟩, s₂⟩ := Dispatch.sqr_spec cfg.mul (UInt32Array.replicate (a.size + a.size) 0)
      0 a.array a.start a.size (by simp [LimbArray.size])
    have hs : (Dispatch.sqr cfg.mul (UInt32Array.replicate (a.size + a.size) 0) 0 a.array a.start
        a.size).size = a.size + a.size := s₁.trans (by simp [LimbArray.size])
    rw [e]
    refine ⟨hs, ?_⟩
    rw [toNat_array_eq_valAt, hs, toNat_eq_valAt a]
    exact s₂
  · by_cases h₂ : cfg.sqrBasecase ≤ a.size
    · have e : sqrLimbsWith cfg a = sqrBasecase a := by
        simp only [sqrLimbsWith, h₁, h₂, ↓reduceIte]
      rw [e]; exact sqrBasecase_spec a
    · have e : sqrLimbsWith cfg a = mulBasecase a a := by
        simp only [sqrLimbsWith, h₁, h₂, ↓reduceIte]
      rw [e]; exact ⟨size_mulBasecase a a, toNat_mulBasecase a a⟩

/-- All `2 * a.size` limbs of `a * a`, untrimmed, like GMP's `mpn_sqr`. -/
public def sqrLimbs (a : UInt32Array.Slice) : UInt32Array := sqrLimbsWith config a

public theorem toNat_sqrLimbs (a : UInt32Array.Slice) :
    toNat (sqrLimbs a).toSlice = toNat a * toNat a := by
  rw [sqrLimbs]; exact (sqrLimbsWith_spec config a).2

/-- Squares a number. -/
public def sqr (a : UInt32Array.Slice) : UInt32Array := trim (sqrLimbs a)

@[simp] public theorem toNat_sqr (a : UInt32Array.Slice) : toNat (sqr a) = toNat a * toNat a := by
  rw [sqr, toNat_trim, sqrLimbs, (sqrLimbsWith_spec config a).2]

public theorem isTrimmed_sqr (a : UInt32Array.Slice) : isTrimmed (sqr a) = true :=
  isTrimmed_trim _

end MPN.W32
