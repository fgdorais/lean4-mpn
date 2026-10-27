/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import MPN.FFT.Fermat
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

/-! ## Guarded residue operations

The operations of `MPN.FFT.Fermat` with `Nat` offsets, which check their bounds: the transforms
call these, so that their definitions carry no proofs, and the theorems show that the checks
pass.
-/

/-- `(x - y) % F` into the window at `d`. -/
public def subModG (arr : UInt64Array) (n d x y : Nat) : UInt64Array :=
  if h : Win arr n.toUSize d.toUSize ∧ Win arr n.toUSize x.toUSize ∧ Win arr n.toUSize y.toUSize
  then subModAt arr n.toUSize d.toUSize x.toUSize y.toUSize h.1 h.2.1 h.2.2 else arr

/-- `(x + y) % F` into the window at `d`. -/
public def addModG (arr : UInt64Array) (n d x y : Nat) : UInt64Array :=
  if h : Win arr n.toUSize d.toUSize ∧ Win arr n.toUSize x.toUSize ∧ Win arr n.toUSize y.toUSize
  then addModAt arr n.toUSize d.toUSize x.toUSize y.toUSize h.1 h.2.1 h.2.2 else arr

/-- `t 2ᵉ % F` into the window at `d`. -/
public def mulPow2G (arr : UInt64Array) (n d t e : Nat) : UInt64Array :=
  if h : Win arr n.toUSize d.toUSize ∧ Win arr n.toUSize t.toUSize ∧
      e.toUSize.toNat < 64 * n.toUSize.toNat
  then mulPow2At arr n.toUSize d.toUSize t.toUSize e.toUSize h.1 h.2.1 h.2.2 else arr

/-- The value of the window of `n + 1` limbs at `o`. -/
public abbrev win (arr : UInt64Array) (n o : Nat) : Nat := arr.valAt o (n + 1)

private theorem toNat_toUSize {a : Nat} (h : a < USize.size) : a.toUSize.toNat = a := by
  rw [USize.toNat_ofNat', Nat.mod_eq_of_lt h]

private theorem win_of {arr : UInt64Array} {n o : Nat} (hS : arr.size < USize.size)
    (h : o + n + 1 ≤ arr.size) :
    Win arr n.toUSize o.toUSize ∧ n.toUSize.toNat = n ∧ o.toUSize.toNat = o := by
  have hn := toNat_toUSize (a := n) (by lia)
  have ho := toNat_toUSize (a := o) (by lia)
  exact ⟨⟨by rw [hn, ho]; exact h, hS⟩, hn, ho⟩

public theorem subModG_spec (arr : UInt64Array) (n d x y : Nat) (hS : arr.size < USize.size)
    (hd : d + n + 1 ≤ arr.size) (hx : x + n + 1 ≤ arr.size) (hy : y + n + 1 ≤ arr.size)
    (hn : 1 ≤ n) (hdx : d ≤ x ∨ x + n + 1 ≤ d) (hdy : d ≤ y ∨ y + n + 1 ≤ d)
    (hX : win arr n x < fermat n) (hY : win arr n y < fermat n) :
    (subModG arr n d x y).size = arr.size ∧
      (∀ i, (i < d ∨ d + n + 1 ≤ i) → (subModG arr n d x y)[i]! = arr[i]!) ∧
      win (subModG arr n d x y) n d = (win arr n x + fermat n - win arr n y) % fermat n := by
  obtain ⟨wd, hn', hd'⟩ := win_of hS hd
  obtain ⟨wx, -, hx'⟩ := win_of hS hx
  obtain ⟨wy, -, hy'⟩ := win_of hS hy
  rw [subModG, dite_eq_left ⟨wd, wx, wy⟩]
  have := subModAt_spec arr n.toUSize d.toUSize x.toUSize y.toUSize wd wx wy (by lia)
    (by rw [hd', hx', hn']; lia) (by rw [hd', hy', hn']; lia) (by rw [hx', hn']; exact hX)
    (by rw [hy', hn']; exact hY)
  simp only [hn', hd', hx', hy'] at this
  exact this

public theorem addModG_spec (arr : UInt64Array) (n d x y : Nat) (hS : arr.size < USize.size)
    (hd : d + n + 1 ≤ arr.size) (hx : x + n + 1 ≤ arr.size) (hy : y + n + 1 ≤ arr.size)
    (hn : 1 ≤ n) (hdx : d ≤ x ∨ x + n + 1 ≤ d) (hdy : d ≤ y ∨ y + n + 1 ≤ d)
    (hX : win arr n x < fermat n) (hY : win arr n y < fermat n) :
    (addModG arr n d x y).size = arr.size ∧
      (∀ i, (i < d ∨ d + n + 1 ≤ i) → (addModG arr n d x y)[i]! = arr[i]!) ∧
      win (addModG arr n d x y) n d = (win arr n x + win arr n y) % fermat n := by
  obtain ⟨wd, hn', hd'⟩ := win_of hS hd
  obtain ⟨wx, -, hx'⟩ := win_of hS hx
  obtain ⟨wy, -, hy'⟩ := win_of hS hy
  rw [addModG, dite_eq_left ⟨wd, wx, wy⟩]
  have := addModAt_spec arr n.toUSize d.toUSize x.toUSize y.toUSize wd wx wy (by lia)
    (by rw [hd', hx', hn']; lia) (by rw [hd', hy', hn']; lia) (by rw [hx', hn']; exact hX)
    (by rw [hy', hn']; exact hY)
  simp only [hn', hd', hx', hy'] at this
  exact this

public theorem mulPow2G_spec (arr : UInt64Array) (n d t e : Nat) (hS : arr.size < USize.size)
    (hd : d + n + 1 ≤ arr.size) (ht : t + n + 1 ≤ arr.size) (hn : 1 ≤ n) (he : e < 64 * n)
    (heS : e < USize.size) (hdt : d + n + 1 ≤ t ∨ t + n + 1 ≤ d) (hT : win arr n t < fermat n) :
    (mulPow2G arr n d t e).size = arr.size ∧
      (∀ i, (i < d ∨ d + n + 1 ≤ i) → (mulPow2G arr n d t e)[i]! = arr[i]!) ∧
      win (mulPow2G arr n d t e) n d = win arr n t * 2 ^ e % fermat n := by
  obtain ⟨wd, hn', hd'⟩ := win_of hS hd
  obtain ⟨wt, -, ht'⟩ := win_of hS ht
  have he' : e.toUSize.toNat = e := toNat_toUSize heS
  rw [mulPow2G, dite_eq_left ⟨wd, wt, by rw [he', hn']; exact he⟩]
  have := mulPow2At_spec arr n.toUSize d.toUSize t.toUSize e.toUSize wd wt
    (by rw [he', hn']; exact he) (by lia) (by rw [hd', ht', hn']; lia) (by rw [ht', hn']; exact hT)
  simp only [hn', hd', ht', he'] at this
  exact this

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

/-- The residue operations of `MPN.FFT.Fermat`, guarded, for the transforms of `WinOps`. -/
public instance winOps64 : WinOps UInt64Array UInt64 where
  w := 64
  w_pos := by decide
  size a := a.size
  get a i := a[i]!
  win a n o := a.valAt o (n + 1)
  subMod := subModG
  addMod := addModG
  mulPow2 := mulPow2G
  win_congr h := win_congr h
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
