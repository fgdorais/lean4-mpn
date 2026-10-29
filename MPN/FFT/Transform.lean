/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import MPN.FFT.Fermat
public import MPN.UIntArray
public import MPN.FFT.Windows

/-!
# The transforms

The transforms of length `2ᵐ` modulo `F = 2ᴺ + 1`, on `2ᵐ` residues in consecutive windows of
one array, in place, with one scratch window. The root of unity is `2^σ` with `σ 2ᵐ = 2 N`, so
that `2^(σ 2ᵐ⁻¹) = 2ᴺ ≡ -1`.

* The forward transform, by decimation in frequency, replaces each pair `(x, y)` of the two
  halves by `(x + y, (x - y) 2^(σ j))`, then transforms each half with the root `2^(2 σ)`. It
  leaves `Σᵢ xᵢ 2^(σ i rev p)` at position `p`, where `rev` reverses the `m` bits of `p`.
* The inverse transform, by decimation in time, takes its input in that order: it transforms
  each half, then replaces each pair `(x, y)` by `(x + y 2^(-σ j), x - y 2^(-σ j))`. Since
  `2^(-σ j) ≡ -2^(N - σ j)`, the multiplications are by powers less than `2ᴺ`, with the signs
  swapped. It leaves `Σₚ uₚ 2^((2 N - σ) rev p l)` at position `l`.

Composed, with the pointwise products in between, the bit reversals cancel.
-/

open ScalarArray UInt64Array

namespace MPN.FFT

/-- The Fermat modulus `2^(64 n) + 1`. -/
@[expose] public def fermat (n : Nat) : Nat := 2 ^ (64 * n) + 1

/-- The value of the window of `n + 1` limbs at `o`. -/
public abbrev win (arr : UInt64Array) (n o : Nat) : Nat := arr.valAt o (n + 1)

/-- A window whose limbs are unchanged keeps its value. -/
public theorem win_congr {a a' : UInt64Array} {n o : Nat}
    (h : ∀ i, o ≤ i → i < o + n + 1 → a'[i]! = a[i]!) : win a' n o = win a n o :=
  UInt64Array.valAt_congr _ fun i h₁ h₂ => h i h₁ (by lia)

/-- A window disjoint from the one an operation writes keeps its value. -/
public theorem win_of_untouched {a a' : UInt64Array} {n d o : Nat}
    (u : ∀ i, (i < d ∨ d + n + 1 ≤ i) → a'[i]! = a[i]!) (h : o + n + 1 ≤ d ∨ d + n + 1 ≤ o) :
    win a' n o = win a n o :=
  UInt64Array.valAt_congr _ fun i h₁ h₂ => u i (by lia)

/-! ## The transforms -/

/-- The residue operations of `main`'s `MPN.FFT.Fermat`, guarded, for the transforms of `WinOps`. -/
public instance winOps64 : WinOps UInt64Array UInt64 where
  subMod := subModG
  addMod := addModG
  mulPow2 := mulPow2G
  subMod_spec := subModG_spec
  addMod_spec := addModG_spec
  mulPow2_spec := mulPow2G_spec

/-- The value of window `p` of the block at `o`, the windows of `n + 1` limbs one after another. -/
public abbrev coef (arr : UInt64Array) (n o p : Nat) : Nat := win arr n (o + p * (n + 1))

/-- The bounds of a block of `L` windows at `o` and of a scratch window at `t`, disjoint from it. -/
public abbrev Block (arr : UInt64Array) (n o L t : Nat) : Prop :=
  arr.size < USize.size ∧ o + L * (n + 1) ≤ arr.size ∧ t + n + 1 ≤ arr.size ∧
    (t + n + 1 ≤ o ∨ o + L * (n + 1) ≤ t)

/--
The forward transform of the block of `2ᵐ` windows at `o`, with the root `2^σ`: `WinOps.fwd` on
`winOps64`.
-/
public def fwd (n t m : Nat) (arr : UInt64Array) (o σ : Nat) : UInt64Array :=
  WinOps.fwd n t m arr o σ

public theorem fwd_spec (n t : Nat) (hn : 1 ≤ n) (h64 : 64 * n < USize.size) (m : Nat) :
    ∀ arr o σ, σ * 2 ^ m = 2 * (64 * n) → Block arr n o (2 ^ m) t →
      (∀ p < 2 ^ m, coef arr n o p < fermat n) →
      (fwd n t m arr o σ).size = arr.size ∧
      (∀ i, (i < o ∨ o + 2 ^ m * (n + 1) ≤ i) → (i < t ∨ t + n + 1 ≤ i) →
        (fwd n t m arr o σ)[i]! = arr[i]!) ∧
      (∀ p < 2 ^ m, coef (fwd n t m arr o σ) n o p =
        sumRange (fun i => coef arr n o i * 2 ^ (σ * i * rev m p)) (2 ^ m) % fermat n) :=
  winOps64.fwd_spec n t hn h64 m

/--
The inverse transform of the block of `2ᵐ` windows at `o`, with the root `2^(2 N - σ)`:
`WinOps.inv` on `winOps64`.
-/
public def inv (n t m : Nat) (arr : UInt64Array) (o σ : Nat) : UInt64Array :=
  WinOps.inv n t m arr o σ

public theorem inv_spec (n t : Nat) (hn : 1 ≤ n) (h64 : 64 * n < USize.size) (m : Nat) :
    ∀ arr o σ, σ * 2 ^ m = 2 * (64 * n) → Block arr n o (2 ^ m) t →
      (∀ p < 2 ^ m, coef arr n o p < fermat n) →
      (inv n t m arr o σ).size = arr.size ∧
      (∀ i, (i < o ∨ o + 2 ^ m * (n + 1) ≤ i) → (i < t ∨ t + n + 1 ≤ i) →
        (inv n t m arr o σ)[i]! = arr[i]!) ∧
      (∀ l < 2 ^ m, coef (inv n t m arr o σ) n o l =
        sumRange (fun p => coef arr n o p * 2 ^ ((2 * (64 * n) - σ) * rev m p * l)) (2 ^ m) %
          fermat n) :=
  winOps64.inv_spec n t hn h64 m

end MPN.FFT
