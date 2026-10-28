/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import MPN.Mul.Basecase
public import MPN.Mul.Unbalanced
public import MPN.Mul.Toom
public import MPN.FFT.Mul
public import MPN.Config

/-!
# Multiplication

`mulLimbs` computes all `a.size + b.size` limbs of a product by choosing an algorithm from the
operand sizes, like GMP's `mpn_mul`, and `mul` trims its result.

Every algorithm computes the full untrimmed product and proves `IsMul`, so the dispatcher is
correct by case analysis whichever algorithm each case picks. The dispatcher first puts the
longer operand first, then `mulLongShort` chooses by the size of the shorter one:

* no limbs: the product is zero;
* one limb: `mulRow`;
* at least `cfg.mulKaratsuba` and `cfg.mulUnbalanced` limbs, with the longer operand at least
  twice as long: `mulUnbalanced`, which halves the longer operand;
* at least `cfg.mulFFT` limbs otherwise: `fftMul`, Schönhage–Strassen modulo `2ᴺ + 1` with
  `2ᵏ` pieces, `k` from `fftK`;
* at least `cfg.mulKaratsuba` limbs otherwise: `mulToomL`, `main`'s Toom methods and Karatsuba,
  which choose by the sizes and the shape and recurse among themselves;
* otherwise: the schoolbook `mulBasecase`, with its rows over the shorter operand.

`mulUnbalanced` and the FFT take the multiplier as a parameter and prove their result assuming it
is correct on smaller inputs, and the induction in `mulLimbsWith_ok` supplies that. The thresholds
come from a `Config`, and `mulLimbs` uses the library's `config`.
-/

open ScalarArray

namespace MPN

/-- An algorithm that computes all `a.size + b.size` limbs of `a * b`, without trimming. -/
public structure IsMul (f : UInt32Array.Slice → UInt32Array.Slice → UInt32Array) : Prop where
  size_eq (a b : UInt32Array.Slice) : (f a b).size = a.size + b.size
  toNat_eq (a b : UInt32Array.Slice) : toNat (f a b) = toNat a * toNat b

public theorem isMul_mulBasecase : IsMul mulBasecase := ⟨size_mulBasecase, toNat_mulBasecase⟩

/-- The thresholds of the library, from the `mpn.*` options set when it is compiled. -/
public def config : Config := mpn_config%

mutual

/-- All the limbs of `a * b` when `b` is no longer than `a`, chosen by the size of `b`. -/
def mulLongShort (cfg : Config) (a b : UInt32Array.Slice) (_hab : b.size ≤ a.size) :
    UInt32Array :=
  if b.size = 0 then
    .replicate a.size 0
  else if h : b.size = 1 then
    mulRow a b[0]
  else if h : cfg.mulKaratsuba ≤ b.size then
    if h' : 2 * b.size ≤ a.size then
      if cfg.mulUnbalanced ≤ b.size then
        mulUnbalanced a b (by have := cfg.four_le_mulKaratsuba; lia) h' fun x y _ =>
          mulLimbsWith cfg x y
      else
        mulBasecase b a
    else if cfg.mulFFT ≤ b.size then
      FFT.fftMul a b (FFT.fftK (a.size + b.size)) fun x y _ => mulLimbsWith cfg x y
    else
      mulToomL cfg a b
  else
    mulBasecase b a
termination_by (a.size + b.size, 0)

/-- All `a.size + b.size` limbs of `a * b`, untrimmed, with the thresholds of `cfg`. -/
public def mulLimbsWith (cfg : Config) (a b : UInt32Array.Slice) : UInt32Array :=
  if h : b.size ≤ a.size then mulLongShort cfg a b h else mulLongShort cfg b a (by lia)
termination_by (a.size + b.size, 1)
decreasing_by
  all_goals first
    | exact Prod.Lex.right _ Nat.zero_lt_one
    | (rw [Nat.add_comm (Std.Slice.size b)]; exact Prod.Lex.right _ Nat.zero_lt_one)

end

/-- All `a.size + b.size` limbs of `a * b`, untrimmed, like GMP's `mpn_mul`. -/
public def mulLimbs (a b : UInt32Array.Slice) : UInt32Array := mulLimbsWith config a b

/-- `r` is all the limbs of `a * b`. -/
private def MulOK (a b : UInt32Array.Slice) (r : UInt32Array) : Prop :=
  r.size = a.size + b.size ∧ toNat r = toNat a * toNat b

private theorem MulOK.swap {a b : UInt32Array.Slice} {r : UInt32Array} (h : MulOK b a r) :
    MulOK a b r :=
  ⟨by rw [h.1, Nat.add_comm], by rw [h.2, Nat.mul_comm]⟩

private theorem mulLongShort_ok (cfg : Config) (a b : UInt32Array.Slice) (hab : b.size ≤ a.size)
    (ih : ∀ x y : UInt32Array.Slice, x.size + y.size < a.size + b.size →
      MulOK x y (mulLimbsWith cfg x y)) :
    MulOK a b (mulLongShort cfg a b hab) := by
  rw [mulLongShort]
  split
  · rename_i h
    refine ⟨by simp [h], ?_⟩
    rw [toNat_toSlice, toNat_of_size_eq_zero h]
    simp
  · split
    · rename_i h
      refine ⟨by simp [h], ?_⟩
      rw [toNat_mulRow, toNat_of_size_eq_one h]
    · split
      · split
        · split
          · exact mulUnbalanced_spec a b _ _ _ fun x y hxy => ih x y hxy
          · exact (show MulOK b a (mulBasecase b a) from ⟨size_mulBasecase b a,
              toNat_mulBasecase b a⟩).swap
        · split
          · exact FFT.fftMul_spec a b _ _ fun x y hxy => ih x y hxy
          · exact mulToomL_spec cfg a b
      · exact (show MulOK b a (mulBasecase b a) from ⟨size_mulBasecase b a,
          toNat_mulBasecase b a⟩).swap

private theorem mulLimbsWith_ok (cfg : Config) (n : Nat) :
    ∀ a b : UInt32Array.Slice, a.size + b.size = n → MulOK a b (mulLimbsWith cfg a b) := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro a b hn
    rw [mulLimbsWith]
    split
    · exact mulLongShort_ok cfg a b _ fun x y hxy => ih _ (by lia) x y rfl
    · exact (mulLongShort_ok cfg b a _ fun x y hxy => ih _ (by lia) x y rfl).swap

/-- Multiplication is correct whatever the thresholds. -/
public theorem isMul_mulLimbsWith (cfg : Config) : IsMul (mulLimbsWith cfg) where
  size_eq a b := (mulLimbsWith_ok cfg _ a b rfl).1
  toNat_eq a b := (mulLimbsWith_ok cfg _ a b rfl).2

public theorem isMul_mulLimbs : IsMul mulLimbs := isMul_mulLimbsWith config

/-- Multiplies two numbers. -/
public def mul (a b : UInt32Array.Slice) : UInt32Array := trim (mulLimbs a b)

@[simp] public theorem toNat_mul (a b : UInt32Array.Slice) :
    toNat (mul a b) = toNat a * toNat b := by
  rw [mul, toNat_trim, isMul_mulLimbs.toNat_eq]

public theorem isTrimmed_mul (a b : UInt32Array.Slice) : isTrimmed (mul a b) = true :=
  isTrimmed_trim _

end MPN
