/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import MPN32.Mul.Basecase
public import MPN.Dispatch
public import MPN32.Mul.ToomOps
public import MPN32.Settings
public import MPN32.Basic

/-!
# Multiplication

`mulLimbs` computes all `a.size + b.size` limbs of a product by choosing an algorithm from the
operand sizes, like GMP's `mpn_mul`, and `mul` trims its result. Below `cfg.mulKaratsuba` limbs in
the shorter operand it multiplies here: no limbs give zero, one limb `mulRow`, and more the
schoolbook `mulBasecase` with its rows over the shorter operand. From there it is `MPN`'s choice
(`MPN.Dispatch.mul`) into a new array: chunked products for a longer operand at least twice as
long as a shorter one of `cfg.mulUnbalanced` limbs, the FFT from `cfg.mulFFT` limbs in the shorter
operand, and the Toom methods and Karatsuba otherwise. The thresholds come from a `Config`, and
`mulLimbs` uses the library's `config`.
-/

open ScalarArray

namespace MPN.W32

/-- An algorithm that computes all `a.size + b.size` limbs of `a * b`, without trimming. -/
public structure IsMul (f : UInt32Array.Slice → UInt32Array.Slice → UInt32Array) : Prop where
  size_eq (a b : UInt32Array.Slice) : (f a b).size = a.size + b.size
  toNat_eq (a b : UInt32Array.Slice) : toNat (f a b) = toNat a * toNat b

public theorem isMul_mulBasecase : IsMul mulBasecase := ⟨size_mulBasecase, toNat_mulBasecase⟩

/-- All the limbs of `a * b` for `b` shorter than `a` and below the threshold of Karatsuba. -/
def mulSmall (a b : UInt32Array.Slice) : UInt32Array :=
  if b.size = 0 then
    .replicate a.size 0
  else if h : b.size = 1 then
    mulRow a b[0]
  else
    mulBasecase b a

/-- `MPN.Dispatch.mul` into a new array. -/
def mulBig (cfg : Config) (a b : UInt32Array.Slice) : UInt32Array :=
  Dispatch.mul cfg.mul (UInt32Array.replicate (a.size + b.size) 0) 0 a.array a.start a.size b.array
    b.start b.size

/-- All `a.size + b.size` limbs of `a * b`, untrimmed, with the thresholds of `cfg`. -/
public def mulLimbsWith (cfg : Config) (a b : UInt32Array.Slice) : UInt32Array :=
  if b.size ≤ a.size then
    if b.size < cfg.mulKaratsuba then mulSmall a b else mulBig cfg a b
  else
    if a.size < cfg.mulKaratsuba then mulSmall b a else mulBig cfg a b

private def MulOK (a b : UInt32Array.Slice) (r : UInt32Array) : Prop :=
  r.size = a.size + b.size ∧ toNat r = toNat a * toNat b

private theorem MulOK.swap {a b : UInt32Array.Slice} {r : UInt32Array} (h : MulOK b a r) :
    MulOK a b r :=
  ⟨by rw [h.1, Nat.add_comm], by rw [h.2, Nat.mul_comm]⟩

private theorem mulSmall_ok (a b : UInt32Array.Slice) : MulOK a b (mulSmall a b) := by
  rw [mulSmall]
  split
  · rename_i h
    refine ⟨by simp [h], ?_⟩
    rw [toNat_toSlice, toNat_of_size_eq_zero h]
    simp
  · split
    · rename_i h
      refine ⟨by simp [h], ?_⟩
      rw [toNat_mulRow, toNat_of_size_eq_one h]
    · exact (show MulOK b a (mulBasecase b a) from ⟨size_mulBasecase b a,
        toNat_mulBasecase b a⟩).swap

private theorem mulBig_ok (cfg : Config) (a b : UInt32Array.Slice) :
    MulOK a b (mulBig cfg a b) := by
  obtain ⟨⟨s₁, -⟩, s₂⟩ := Dispatch.mul_spec cfg.mul (UInt32Array.replicate (a.size + b.size) 0) 0
    a.array a.start a.size b.array b.start b.size (by simp [LimbArray.size])
  have hs : (mulBig cfg a b).size = a.size + b.size := s₁.trans (by simp [LimbArray.size])
  refine ⟨hs, ?_⟩
  rw [toNat_array_eq_valAt, hs, toNat_eq_valAt a, toNat_eq_valAt b]
  exact s₂

private theorem mulLimbsWith_ok (cfg : Config) (a b : UInt32Array.Slice) :
    MulOK a b (mulLimbsWith cfg a b) := by
  rw [mulLimbsWith]
  split
  · split
    · exact mulSmall_ok a b
    · exact mulBig_ok cfg a b
  · split
    · exact (mulSmall_ok b a).swap
    · exact mulBig_ok cfg a b

/-- Multiplication is correct whatever the thresholds. -/
public theorem isMul_mulLimbsWith (cfg : Config) : IsMul (mulLimbsWith cfg) where
  size_eq a b := (mulLimbsWith_ok cfg a b).1
  toNat_eq a b := (mulLimbsWith_ok cfg a b).2

/-- All `a.size + b.size` limbs of `a * b`, untrimmed, like GMP's `mpn_mul`. -/
public def mulLimbs (a b : UInt32Array.Slice) : UInt32Array := mulLimbsWith config a b

public theorem isMul_mulLimbs : IsMul mulLimbs := isMul_mulLimbsWith config

/-- Multiplies two numbers. -/
public def mul (a b : UInt32Array.Slice) : UInt32Array := trim (mulLimbs a b)

@[simp] public theorem toNat_mul (a b : UInt32Array.Slice) :
    toNat (mul a b) = toNat a * toNat b := by
  rw [mul, toNat_trim, isMul_mulLimbs.toNat_eq]

public theorem isTrimmed_mul (a b : UInt32Array.Slice) : isTrimmed (mul a b) = true :=
  isTrimmed_trim _

end MPN.W32
