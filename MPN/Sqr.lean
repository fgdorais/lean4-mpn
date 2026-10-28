/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import MPN.Sqr.Basecase
public import MPN.Mul

/-!
# Squaring

`sqrLimbs` computes all `2 * a.size` limbs of `a * a` by choosing an algorithm from the size of
`a`, like GMP's `mpn_sqr`, and `sqr` trims its result. Squaring is cheaper than multiplying: the
schoolbook square computes each cross product once, and the Karatsuba and Toom squares have
smaller squares instead of products.

* below `cfg.sqrBasecase` limbs: `mulBasecase a a`, since the extra passes of the schoolbook
  square cost more than they save on small numbers;
* below `cfg.sqrKaratsuba` limbs: the schoolbook `sqrBasecase`;
* below `cfg.sqrFFT` limbs: `sqrToomL`, `main`'s Toom squares and Karatsuba, from the thresholds
  `cfg.sqrKaratsuba`, `cfg.sqrToom3`, `cfg.sqrToom4` and `cfg.sqrToom6`;
* otherwise: `fftSqr`, with one forward transform and squares for the pointwise products.
-/

open ScalarArray

namespace MPN

/-- All `2 * a.size` limbs of `a * a`, untrimmed, with the thresholds of `cfg`. -/
public def sqrLimbsWith (cfg : Config) (a : UInt32Array.Slice) : UInt32Array :=
  if cfg.sqrFFT ≤ a.size then
    FFT.fftSqr a (FFT.fftK (a.size + a.size)) fun x _ => sqrLimbsWith cfg x
  else if cfg.sqrKaratsuba ≤ a.size then
    sqrToomL cfg a
  else if cfg.sqrBasecase ≤ a.size then
    sqrBasecase a
  else
    mulBasecase a a
termination_by a.size

public theorem sqrLimbsWith_spec (cfg : Config) (a : UInt32Array.Slice) :
    (sqrLimbsWith cfg a).size = a.size + a.size ∧
      toNat (sqrLimbsWith cfg a) = toNat a * toNat a := by
  induction a using sqrLimbsWith.induct cfg with
  | case1 a hf ih =>
    rw [toNat_toSlice, sqrLimbsWith]
    simp only [hf, ↓reduceIte]
    rw [← toNat_toSlice]
    exact FFT.fftSqr_spec a _ _ fun x hx => ih x hx
  | case2 a hf h =>
    rw [toNat_toSlice, sqrLimbsWith]
    simp only [hf, h, ↓reduceIte]
    rw [← toNat_toSlice]
    exact sqrToomL_spec cfg a
  | case3 a hf h₁ h =>
    rw [toNat_toSlice, sqrLimbsWith]
    simp only [hf, h₁, h, ↓reduceIte]
    rw [← toNat_toSlice]
    exact sqrBasecase_spec a
  | case4 a hf h₁ h =>
    rw [toNat_toSlice, sqrLimbsWith]
    simp only [hf, h₁, h, ↓reduceIte]
    rw [← toNat_toSlice]
    exact ⟨size_mulBasecase a a, toNat_mulBasecase a a⟩

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

end MPN
