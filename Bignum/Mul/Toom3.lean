/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bignum.Add
public import Bignum.Sub
public import Bignum.Div.Limb
public import Bignum.Mul.Limb

/-!
# Toom-3 multiplication

Splitting `a = a₀ + a₁ x + a₂ x²` and `b = b₀ + b₁ x + b₂ x²` at `x = βᵏ` makes `a * b` the value at
`x` of `c(t) = c₀ + c₁ t + c₂ t² + c₃ t³ + c₄ t⁴`, the product of the two polynomials. Its five
coefficients are recovered from five products of about a third of the size: `c₀ = a₀ b₀`,
`c₄ = a₂ b₂`, and the values `w₁ = c(1)`, `w₂ = c(2)` and `w₃ = c(3)` as products of the values
of the two polynomials at `1`, `2` and `3`.

GMP evaluates at `-1` instead of `3`, which makes the evaluations smaller but some intermediate
values negative. The points `0, 1, 2, 3, ∞` keep every intermediate value a natural number, since
the coefficients are, and each step of the interpolation

* `r₁ = w₁ - c₀ - c₄ = c₁ + c₂ + c₃`,
* `s₂ = (w₂ - c₀ - 16 c₄) / 2 = c₁ + 2 c₂ + 4 c₃`,
* `s₃ = (w₃ - c₀ - 81 c₄) / 3 = c₁ + 3 c₂ + 9 c₃`,
* `t₂ = s₂ - r₁ = c₂ + 3 c₃`,
* `t₃ = (s₃ - r₁) / 2 = c₂ + 4 c₃`,
* `c₃ = t₃ - t₂`, `c₂ = t₂ - 3 c₃`, `c₁ = r₁ - c₂ - c₃`

subtracts a part of what it subtracts from and divides exactly. Like `karatsuba`, `toom3` takes
the multiplier for the five products as a parameter.
-/

open ScalarArray

namespace Bignum

/-! ## Building blocks -/

/-- `x / d`, which is exact when `d` divides `x`. -/
def divExact (x : UInt32Array) (d : UInt32) : UInt32Array := (divRem1 x d).1

private theorem toNat_divExact (x : UInt32Array) (d : UInt32) (hd : d ≠ 0) (X : Nat)
    (hx : toNat x = d.toNat * X) : toNat (divExact x d) = X := by
  have hd' : 0 < d.toNat := by
    rcases Nat.eq_zero_or_pos d.toNat with h | h
    · exact absurd (UInt32.toNat_inj.1 (by simpa using h)) hd
    · exact h
  obtain ⟨h₁, h₂⟩ := divRem1_spec x d hd
  rw [hx] at h₁
  have := (Nat.div_mod_unique (a := d.toNat * X) (b := d.toNat) (d := toNat (divRem1 x d).1)
    (c := (divRem1 x d).2.toNat) hd').2 ⟨by rw [Nat.mul_comm d.toNat]; omega, h₂⟩
  rw [divExact, ← this.1, Nat.mul_div_cancel_left _ hd']

/-- `x₀ + x₁ + x₂`. -/
def eval1 (x₀ x₁ x₂ : UInt32Array.Slice) : UInt32Array := addLimbs (addLimbs x₀ x₁) x₂

/-- `x₀ + 2 x₁ + 4 x₂`. -/
def eval2 (x₀ x₁ x₂ : UInt32Array.Slice) : UInt32Array :=
  addLimbs (addLimbs x₀ (mulRow x₁ 2)) (mulRow x₂ 4)

/-- `x₀ + 3 x₁ + 9 x₂`. -/
def eval3 (x₀ x₁ x₂ : UInt32Array.Slice) : UInt32Array :=
  addLimbs (addLimbs x₀ (mulRow x₁ 3)) (mulRow x₂ 9)

private theorem size_eval1 (x₀ x₁ x₂ : UInt32Array.Slice) :
    (eval1 x₀ x₁ x₂).size = max (max x₀.size x₁.size + 1) x₂.size + 1 := by
  simp [eval1]

private theorem size_eval2 (x₀ x₁ x₂ : UInt32Array.Slice) :
    (eval2 x₀ x₁ x₂).size = max (max x₀.size (x₁.size + 1) + 1) (x₂.size + 1) + 1 := by
  simp [eval2]

private theorem size_eval3 (x₀ x₁ x₂ : UInt32Array.Slice) :
    (eval3 x₀ x₁ x₂).size = max (max x₀.size (x₁.size + 1) + 1) (x₂.size + 1) + 1 := by
  simp [eval3]

private theorem toNat_eval1 (x₀ x₁ x₂ : UInt32Array.Slice) :
    toNat (eval1 x₀ x₁ x₂) = toNat x₀ + toNat x₁ + toNat x₂ := by
  rw [eval1, toNat_addLimbs, toNat_addLimbs]

private theorem toNat_eval2 (x₀ x₁ x₂ : UInt32Array.Slice) :
    toNat (eval2 x₀ x₁ x₂) = toNat x₀ + 2 * toNat x₁ + 4 * toNat x₂ := by
  rw [eval2, toNat_addLimbs, toNat_addLimbs, toNat_mulRow, toNat_mulRow]
  simp only [UInt32.reduceToNat]
  omega

private theorem toNat_eval3 (x₀ x₁ x₂ : UInt32Array.Slice) :
    toNat (eval3 x₀ x₁ x₂) = toNat x₀ + 3 * toNat x₁ + 9 * toNat x₂ := by
  rw [eval3, toNat_addLimbs, toNat_addLimbs, toNat_mulRow, toNat_mulRow]
  simp only [UInt32.reduceToNat]
  omega

/-- Splitting a slice at `k` and `2 k` splits its value in three. -/
private theorem toNat_slice_three (s : UInt32Array.Slice) (k : Nat) (hk : 2 * k ≤ s.size) :
    toNat s = toNat (s.slice 0 k) + 2 ^ (32 * k) * toNat (s.slice k (2 * k)) +
      2 ^ (32 * k) * 2 ^ (32 * k) * toNat (s.slice (2 * k) s.size) := by
  have h₁ := toNat_slice_add_toNat_slice s k (by omega)
  have h₂ := toNat_slice_add_toNat_slice (s.slice k s.size) k (by simp; omega)
  have e₁ : toNat ((s.slice k s.size).slice 0 k) = toNat (s.slice k (2 * k)) := by
    simp only [toNat, UInt32Array.Slice.copy_slice, UInt32Array.extract_extract]
    rw [show k + 0 = k by omega, show min (k + k) s.size = 2 * k by omega]
  have e₂ : toNat ((s.slice k s.size).slice k (s.slice k s.size).size) =
      toNat (s.slice (2 * k) s.size) := by
    simp only [toNat, UInt32Array.Slice.copy_slice, UInt32Array.extract_extract,
      UInt32Array.Slice.size_slice]
    rw [show k + k = 2 * k by omega,
      show min (k + (min s.size s.size - k)) s.size = s.size by omega]
  rw [e₁, e₂] at h₂
  rw [← h₁, ← h₂]
  rw [Nat.mul_add, Nat.mul_assoc]
  omega

/-! ## Interpolation -/

/-- `c₁`, `c₂` and `c₃` from `c₀`, `w₁ = c(1)`, `w₂ = c(2)`, `w₃ = c(3)` and `c₄`. -/
def toom3Interp (c₀ w₁ w₂ w₃ c₄ : UInt32Array) : UInt32Array × UInt32Array × UInt32Array :=
  let r₁ := subVal (subVal w₁ c₀) c₄
  let s₂ := divExact (subVal (subVal w₂ c₀) (mulRow c₄ 16)) 2
  let s₃ := divExact (subVal (subVal w₃ c₀) (mulRow c₄ 81)) 3
  let t₂ := subVal s₂ r₁
  let t₃ := divExact (subVal s₃ r₁) 2
  let c₃ := subVal t₃ t₂
  let c₂ := subVal t₂ (mulRow c₃ 3)
  (subVal (subVal r₁ c₂) c₃, c₂, c₃)

private theorem toom3Interp_spec (c₀ w₁ w₂ w₃ c₄ : UInt32Array) (C₀ C₁ C₂ C₃ C₄ : Nat)
    (h₀ : toNat c₀ = C₀) (h₄ : toNat c₄ = C₄) (h₁ : toNat w₁ = C₀ + C₁ + C₂ + C₃ + C₄)
    (h₂ : toNat w₂ = C₀ + 2 * C₁ + 4 * C₂ + 8 * C₃ + 16 * C₄)
    (h₃ : toNat w₃ = C₀ + 3 * C₁ + 9 * C₂ + 27 * C₃ + 81 * C₄) :
    toNat (toom3Interp c₀ w₁ w₂ w₃ c₄).1 = C₁ ∧ toNat (toom3Interp c₀ w₁ w₂ w₃ c₄).2.1 = C₂ ∧
      toNat (toom3Interp c₀ w₁ w₂ w₃ c₄).2.2 = C₃ := by
  simp only [toom3Interp]
  have m16 : toNat (mulRow c₄ 16) = 16 * C₄ := by
    rw [toNat_mulRow, h₄]; simp only [UInt32.reduceToNat]; omega
  have m81 : toNat (mulRow c₄ 81) = 81 * C₄ := by
    rw [toNat_mulRow, h₄]; simp only [UInt32.reduceToNat]; omega
  -- `r₁ = c₁ + c₂ + c₃`.
  have hr₁a : toNat (subVal w₁ c₀) = C₁ + C₂ + C₃ + C₄ := by
    rw [toNat_subVal _ _ (by omega)]; omega
  have hr₁ : toNat (subVal (subVal w₁ c₀) c₄) = C₁ + C₂ + C₃ := by
    rw [toNat_subVal _ _ (by omega)]; omega
  -- `s₂ = c₁ + 2 c₂ + 4 c₃` and `s₃ = c₁ + 3 c₂ + 9 c₃`.
  have hs₂a : toNat (subVal (subVal w₂ c₀) (mulRow c₄ 16)) = 2 * (C₁ + 2 * C₂ + 4 * C₃) := by
    rw [toNat_subVal _ _ (by rw [toNat_subVal _ _ (by omega)]; omega),
      toNat_subVal _ _ (by omega)]
    omega
  have hs₂ : toNat (divExact (subVal (subVal w₂ c₀) (mulRow c₄ 16)) 2) = C₁ + 2 * C₂ + 4 * C₃ :=
    toNat_divExact _ 2 (by decide) _ hs₂a
  have hs₃a : toNat (subVal (subVal w₃ c₀) (mulRow c₄ 81)) = 3 * (C₁ + 3 * C₂ + 9 * C₃) := by
    rw [toNat_subVal _ _ (by rw [toNat_subVal _ _ (by omega)]; omega),
      toNat_subVal _ _ (by omega)]
    omega
  have hs₃ : toNat (divExact (subVal (subVal w₃ c₀) (mulRow c₄ 81)) 3) = C₁ + 3 * C₂ + 9 * C₃ :=
    toNat_divExact _ 3 (by decide) _ hs₃a
  generalize subVal (subVal w₁ c₀) c₄ = r₁ at *
  generalize divExact (subVal (subVal w₂ c₀) (mulRow c₄ 16)) 2 = s₂ at *
  generalize divExact (subVal (subVal w₃ c₀) (mulRow c₄ 81)) 3 = s₃ at *
  clear hr₁a hs₂a hs₃a m16 m81 h₀ h₁ h₂ h₃ h₄
  -- `t₂ = c₂ + 3 c₃` and `t₃ = c₂ + 4 c₃`.
  have ht₂ : toNat (subVal s₂ r₁) = C₂ + 3 * C₃ := by
    rw [toNat_subVal _ _ (by omega)]; omega
  have ht₃ : toNat (divExact (subVal s₃ r₁) 2) = C₂ + 4 * C₃ :=
    toNat_divExact _ 2 (by decide) _
      (by rw [toNat_subVal _ _ (by omega)]; simp only [UInt32.reduceToNat]; omega)
  generalize subVal s₂ r₁ = t₂ at *
  generalize divExact (subVal s₃ r₁) 2 = t₃ at *
  clear hs₂ hs₃
  -- `c₃ = t₃ - t₂`, `c₂ = t₂ - 3 c₃` and `c₁ = r₁ - c₂ - c₃`.
  have hc₃ : toNat (subVal t₃ t₂) = C₃ := by
    rw [toNat_subVal _ _ (by omega)]; omega
  have m3 : toNat (mulRow (subVal t₃ t₂) 3) = 3 * C₃ := by
    rw [toNat_mulRow, hc₃]; simp only [UInt32.reduceToNat]; omega
  have hc₂ : toNat (subVal t₂ (mulRow (subVal t₃ t₂) 3)) = C₂ := by
    rw [toNat_subVal _ _ (by omega)]; omega
  generalize subVal t₃ t₂ = c₃ at *
  generalize subVal t₂ (mulRow c₃ 3) = c₂ at *
  clear ht₂ ht₃ m3
  have hc₁a : toNat (subVal r₁ c₂) = C₁ + C₃ := by
    rw [toNat_subVal r₁ c₂ (by omega)]
    omega
  have hc₁ : toNat (subVal (subVal r₁ c₂) c₃) = C₁ := by
    rw [toNat_subVal (subVal r₁ c₂) c₃ (by omega)]
    omega
  exact ⟨hc₁, hc₂, hc₃⟩

/-! ## Assembly -/

/-- Adding a term `c βᵒᶠᶠ` that fits under a bound `S < βⁿ` on the whole sum. -/
private theorem addAt_term (r c : UInt32Array) (n off P C S : Nat) (hn : r.size = n)
    (hoff : off ≤ n) (hr : toNat r = P) (hc : toNat c = C) (hS : P + 2 ^ (32 * off) * C ≤ S)
    (hlt : S < 2 ^ (32 * n)) :
    (addInto r off (c.toSlice 0 (n - off))).size = n ∧
      toNat (addInto r off (c.toSlice 0 (n - off))) = P + 2 ^ (32 * off) * C := by
  have hpow : 2 ^ (32 * n) = 2 ^ (32 * off) * 2 ^ (32 * (n - off)) := by
    rw [← Nat.pow_add]; congr 1; omega
  have hC : C < 2 ^ (32 * (n - off)) := by
    have : 2 ^ (32 * off) * C < 2 ^ (32 * off) * 2 ^ (32 * (n - off)) := by omega
    exact Nat.lt_of_mul_lt_mul_left this
  have hcut : toNat (c.toSlice 0 (n - off)) = C := by
    rw [toNat_toSlice_of_lt _ _ (by rw [hc]; exact hC), hc]
  have hfit : off + (c.toSlice 0 (n - off)).size ≤ r.size := by
    rw [UInt32Array.size_toSlice]; omega
  refine ⟨by rw [size_addInto _ _ _ hfit, hn], ?_⟩
  rw [toNat_addInto_of_lt _ _ _ hfit (by rw [hr, hcut, hn]; omega), hr, hcut]

/-- `c₀ + c₁ x + c₂ x² + c₃ x³ + c₄ x⁴` as `n` limbs, where `x = βᵏ`. -/
def toom3Assemble (n k : Nat) (c₀ c₁ c₂ c₃ c₄ : UInt32Array) : UInt32Array :=
  let r₀ := addInto (.replicate n 0) 0 (c₀.toSlice 0 (n - 0))
  let r₁ := addInto r₀ k (c₁.toSlice 0 (n - k))
  let r₂ := addInto r₁ (2 * k) (c₂.toSlice 0 (n - 2 * k))
  let r₃ := addInto r₂ (3 * k) (c₃.toSlice 0 (n - 3 * k))
  addInto r₃ (4 * k) (c₄.toSlice 0 (n - 4 * k))

private theorem toom3Assemble_spec (n k : Nat) (c₀ c₁ c₂ c₃ c₄ : UInt32Array)
    (C₀ C₁ C₂ C₃ C₄ : Nat) (hk : 4 * k ≤ n) (h₀ : toNat c₀ = C₀) (h₁ : toNat c₁ = C₁)
    (h₂ : toNat c₂ = C₂) (h₃ : toNat c₃ = C₃) (h₄ : toNat c₄ = C₄)
    (hlt : C₀ + 2 ^ (32 * k) * C₁ + 2 ^ (32 * (2 * k)) * C₂ + 2 ^ (32 * (3 * k)) * C₃ +
      2 ^ (32 * (4 * k)) * C₄ < 2 ^ (32 * n)) :
    (toom3Assemble n k c₀ c₁ c₂ c₃ c₄).size = n ∧
      toNat (toom3Assemble n k c₀ c₁ c₂ c₃ c₄) = C₀ + 2 ^ (32 * k) * C₁ +
        2 ^ (32 * (2 * k)) * C₂ + 2 ^ (32 * (3 * k)) * C₃ + 2 ^ (32 * (4 * k)) * C₄ := by
  generalize hS : C₀ + 2 ^ (32 * k) * C₁ + 2 ^ (32 * (2 * k)) * C₂ + 2 ^ (32 * (3 * k)) * C₃ +
    2 ^ (32 * (4 * k)) * C₄ = S at hlt
  obtain ⟨s₀, v₀⟩ := addAt_term (.replicate n 0) c₀ n 0 0 C₀ S (by simp) (by omega)
    (by rw [toNat_toSlice]; simp) h₀ (by simp; omega) hlt
  obtain ⟨s₁, v₁⟩ := addAt_term _ c₁ n k _ C₁ S s₀ (by omega) v₀ h₁ (by
    simp only [Nat.mul_zero, Nat.pow_zero, Nat.one_mul]; omega) hlt
  obtain ⟨s₂, v₂⟩ := addAt_term _ c₂ n (2 * k) _ C₂ S s₁ (by omega) v₁ h₂ (by
    simp only [Nat.mul_zero, Nat.pow_zero, Nat.one_mul]; omega) hlt
  obtain ⟨s₃, v₃⟩ := addAt_term _ c₃ n (3 * k) _ C₃ S s₂ (by omega) v₂ h₃ (by
    simp only [Nat.mul_zero, Nat.pow_zero, Nat.one_mul]; omega) hlt
  obtain ⟨s₄, v₄⟩ := addAt_term _ c₄ n (4 * k) _ C₄ S s₃ (by omega) v₃ h₄ (by
    simp only [Nat.mul_zero, Nat.pow_zero, Nat.one_mul]; omega) hlt
  refine ⟨s₄, ?_⟩
  rw [toom3Assemble, v₄, ← hS]
  simp only [Nat.mul_zero, Nat.pow_zero, Nat.one_mul, Nat.zero_add]

/-! ## Toom-3 -/

/--
The product `a * b` by one step of Toom-3, splitting at `k = ⌈b.size / 3⌉` limbs, for
`12 ≤ b.size ≤ a.size`. It computes the five products with `mulRec`, which only receives inputs
smaller than `a` and `b` together.
-/
public def toom3 (a b : UInt32Array.Slice) (hb : 12 ≤ b.size) (hab : b.size ≤ a.size)
    (mulRec : (x y : UInt32Array.Slice) → x.size + y.size < a.size + b.size → UInt32Array) :
    UInt32Array :=
  let k := (b.size + 2) / 3
  let a₀ := a.slice 0 k
  let a₁ := a.slice k (2 * k)
  let a₂ := a.slice (2 * k) a.size
  let b₀ := b.slice 0 k
  let b₁ := b.slice k (2 * k)
  let b₂ := b.slice (2 * k) b.size
  let c₀ := mulRec a₀ b₀ (by simp only [a₀, b₀, UInt32Array.Slice.size_slice]; omega)
  let c₄ := mulRec a₂ b₂ (by simp only [a₂, b₂, UInt32Array.Slice.size_slice]; omega)
  let w₁ := mulRec (eval1 a₀ a₁ a₂) (eval1 b₀ b₁ b₂) (by
    simp only [UInt32Array.size_toSlice, size_eval1, a₀, a₁, a₂, b₀, b₁, b₂,
      UInt32Array.Slice.size_slice]
    omega)
  let w₂ := mulRec (eval2 a₀ a₁ a₂) (eval2 b₀ b₁ b₂) (by
    simp only [UInt32Array.size_toSlice, size_eval2, a₀, a₁, a₂, b₀, b₁, b₂,
      UInt32Array.Slice.size_slice]
    omega)
  let w₃ := mulRec (eval3 a₀ a₁ a₂) (eval3 b₀ b₁ b₂) (by
    simp only [UInt32Array.size_toSlice, size_eval3, a₀, a₁, a₂, b₀, b₁, b₂,
      UInt32Array.Slice.size_slice]
    omega)
  let i := toom3Interp c₀ w₁ w₂ w₃ c₄
  toom3Assemble (a.size + b.size) k c₀ i.1 i.2.1 i.2.2 c₄

private theorem toom3_w₁ (A₀ A₁ A₂ B₀ B₁ B₂ : Nat) :
    (A₀ + A₁ + A₂) * (B₀ + B₁ + B₂) = A₀ * B₀ + (A₀ * B₁ + A₁ * B₀) +
      (A₀ * B₂ + A₁ * B₁ + A₂ * B₀) + (A₁ * B₂ + A₂ * B₁) + A₂ * B₂ := by
  grind

private theorem toom3_w₂ (A₀ A₁ A₂ B₀ B₁ B₂ : Nat) :
    (A₀ + 2 * A₁ + 4 * A₂) * (B₀ + 2 * B₁ + 4 * B₂) = A₀ * B₀ + 2 * (A₀ * B₁ + A₁ * B₀) +
      4 * (A₀ * B₂ + A₁ * B₁ + A₂ * B₀) + 8 * (A₁ * B₂ + A₂ * B₁) + 16 * (A₂ * B₂) := by
  grind

private theorem toom3_w₃ (A₀ A₁ A₂ B₀ B₁ B₂ : Nat) :
    (A₀ + 3 * A₁ + 9 * A₂) * (B₀ + 3 * B₁ + 9 * B₂) = A₀ * B₀ + 3 * (A₀ * B₁ + A₁ * B₀) +
      9 * (A₀ * B₂ + A₁ * B₁ + A₂ * B₀) + 27 * (A₁ * B₂ + A₂ * B₁) + 81 * (A₂ * B₂) := by
  grind

private theorem toom3_sum (A₀ A₁ A₂ B₀ B₁ B₂ x : Nat) :
    A₀ * B₀ + x * (A₀ * B₁ + A₁ * B₀) + x * x * (A₀ * B₂ + A₁ * B₁ + A₂ * B₀) +
      x * x * x * (A₁ * B₂ + A₂ * B₁) + x * x * x * x * (A₂ * B₂) =
      (A₀ + x * A₁ + x * x * A₂) * (B₀ + x * B₁ + x * x * B₂) := by
  grind

public theorem toom3_spec (a b : UInt32Array.Slice) (hb : 12 ≤ b.size) (hab : b.size ≤ a.size)
    (mulRec : (x y : UInt32Array.Slice) → x.size + y.size < a.size + b.size → UInt32Array)
    (hrec : ∀ x y h, (mulRec x y h).size = x.size + y.size ∧
      toNat (mulRec x y h) = toNat x * toNat y) :
    (toom3 a b hb hab mulRec).size = a.size + b.size ∧
      toNat (toom3 a b hb hab mulRec) = toNat a * toNat b := by
  have hk₁ : 2 * ((b.size + 2) / 3) ≤ b.size := by omega
  have ha := toNat_slice_three a ((b.size + 2) / 3) (by omega)
  have hb' := toNat_slice_three b ((b.size + 2) / 3) hk₁
  have hA := toNat_lt a
  have hB := toNat_lt b
  -- The five products.
  obtain ⟨-, hv₀⟩ := hrec (a.slice 0 ((b.size + 2) / 3)) (b.slice 0 ((b.size + 2) / 3))
    (by simp only [UInt32Array.Slice.size_slice]; omega)
  obtain ⟨-, hv₄⟩ := hrec (a.slice (2 * ((b.size + 2) / 3)) a.size)
    (b.slice (2 * ((b.size + 2) / 3)) b.size) (by simp only [UInt32Array.Slice.size_slice]; omega)
  obtain ⟨-, hw₁⟩ := hrec
    (eval1 (a.slice 0 ((b.size + 2) / 3)) (a.slice ((b.size + 2) / 3) (2 * ((b.size + 2) / 3)))
      (a.slice (2 * ((b.size + 2) / 3)) a.size))
    (eval1 (b.slice 0 ((b.size + 2) / 3)) (b.slice ((b.size + 2) / 3) (2 * ((b.size + 2) / 3)))
      (b.slice (2 * ((b.size + 2) / 3)) b.size))
    (by simp only [UInt32Array.size_toSlice, size_eval1, UInt32Array.Slice.size_slice]; omega)
  obtain ⟨-, hw₂⟩ := hrec
    (eval2 (a.slice 0 ((b.size + 2) / 3)) (a.slice ((b.size + 2) / 3) (2 * ((b.size + 2) / 3)))
      (a.slice (2 * ((b.size + 2) / 3)) a.size))
    (eval2 (b.slice 0 ((b.size + 2) / 3)) (b.slice ((b.size + 2) / 3) (2 * ((b.size + 2) / 3)))
      (b.slice (2 * ((b.size + 2) / 3)) b.size))
    (by simp only [UInt32Array.size_toSlice, size_eval2, UInt32Array.Slice.size_slice]; omega)
  obtain ⟨-, hw₃⟩ := hrec
    (eval3 (a.slice 0 ((b.size + 2) / 3)) (a.slice ((b.size + 2) / 3) (2 * ((b.size + 2) / 3)))
      (a.slice (2 * ((b.size + 2) / 3)) a.size))
    (eval3 (b.slice 0 ((b.size + 2) / 3)) (b.slice ((b.size + 2) / 3) (2 * ((b.size + 2) / 3)))
      (b.slice (2 * ((b.size + 2) / 3)) b.size))
    (by simp only [UInt32Array.size_toSlice, size_eval3, UInt32Array.Slice.size_slice]; omega)
  rw [toNat_eval1, toNat_eval1] at hw₁
  rw [toNat_eval2, toNat_eval2] at hw₂
  rw [toNat_eval3, toNat_eval3] at hw₃
  generalize toNat (a.slice 0 ((b.size + 2) / 3)) = A₀ at *
  generalize toNat (a.slice ((b.size + 2) / 3) (2 * ((b.size + 2) / 3))) = A₁ at *
  generalize toNat (a.slice (2 * ((b.size + 2) / 3)) a.size) = A₂ at *
  generalize toNat (b.slice 0 ((b.size + 2) / 3)) = B₀ at *
  generalize toNat (b.slice ((b.size + 2) / 3) (2 * ((b.size + 2) / 3))) = B₁ at *
  generalize toNat (b.slice (2 * ((b.size + 2) / 3)) b.size) = B₂ at *
  -- Interpolation recovers the middle coefficients.
  have hi := toom3Interp_spec _ _ _ _ _ (A₀ * B₀) (A₀ * B₁ + A₁ * B₀)
    (A₀ * B₂ + A₁ * B₁ + A₂ * B₀) (A₁ * B₂ + A₂ * B₁) (A₂ * B₂) hv₀ hv₄
    (by rw [hw₁, toom3_w₁]) (by rw [hw₂, toom3_w₂]) (by rw [hw₃, toom3_w₃])
  -- The coefficients at `x = βᵏ` give the product.
  have hx₂ : 2 ^ (32 * (2 * ((b.size + 2) / 3))) =
      2 ^ (32 * ((b.size + 2) / 3)) * 2 ^ (32 * ((b.size + 2) / 3)) := by
    rw [← Nat.pow_add]; congr 1; omega
  have hx₃ : 2 ^ (32 * (3 * ((b.size + 2) / 3))) =
      2 ^ (32 * ((b.size + 2) / 3)) * 2 ^ (32 * ((b.size + 2) / 3)) *
        2 ^ (32 * ((b.size + 2) / 3)) := by
    rw [← Nat.pow_add, ← Nat.pow_add]; congr 1; omega
  have hx₄ : 2 ^ (32 * (4 * ((b.size + 2) / 3))) =
      2 ^ (32 * ((b.size + 2) / 3)) * 2 ^ (32 * ((b.size + 2) / 3)) *
        2 ^ (32 * ((b.size + 2) / 3)) * 2 ^ (32 * ((b.size + 2) / 3)) := by
    rw [← Nat.pow_add, ← Nat.pow_add, ← Nat.pow_add]; congr 1; omega
  have hS : A₀ * B₀ + 2 ^ (32 * ((b.size + 2) / 3)) * (A₀ * B₁ + A₁ * B₀) +
      2 ^ (32 * (2 * ((b.size + 2) / 3))) * (A₀ * B₂ + A₁ * B₁ + A₂ * B₀) +
      2 ^ (32 * (3 * ((b.size + 2) / 3))) * (A₁ * B₂ + A₂ * B₁) +
      2 ^ (32 * (4 * ((b.size + 2) / 3))) * (A₂ * B₂) = toNat a * toNat b := by
    rw [hx₂, hx₃, hx₄, ha, hb', toom3_sum]
  have hlt : toNat a * toNat b < 2 ^ (32 * (a.size + b.size)) := by
    rw [Nat.mul_add, Nat.pow_add]
    exact Nat.mul_lt_mul'' hA hB
  have key := toom3Assemble_spec (a.size + b.size) ((b.size + 2) / 3) _ _ _ _ _ _ _ _ _ _
    (by omega) hv₀ hi.1 hi.2.1 hi.2.2 hv₄ (by rw [hS]; exact hlt)
  rw [hS] at key
  exact key

end Bignum
