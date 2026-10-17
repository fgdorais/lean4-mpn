/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import MPN.Add
public import MPN.Sub
public import MPN.Mul.Limb
public import MPN.Mul.DivExact
public import MPN.Mul.Toom3

/-!
# Toom-4 and Toom-4 by 3

Splitting `a` in four and `b` in four (`toom44`) or three (`toom43`) parts at `x = βᵏ` makes
`a * b` the value at `x` of a polynomial `c(t)` of degree six or five, recovered from as many
products of about a quarter of the size, like GMP's `mpn_toom44_mul` and `mpn_toom43_mul`.

As in `toom3`, the points are natural numbers, `0, 1, …, d - 1, ∞` for degree `d`, so that every
intermediate value of the interpolation is a natural number. With `c₀` and `c_d` known, the values
`r_j = (c(j) - c₀ - jᵈ c_d) / j = c₁ + c₂ j + ⋯ + c_{d-1} j^{d-2}` are those of a polynomial with
natural coefficients at `1, …, d - 1`. Its divided differences at those points are natural
numbers, and so are those that Horner's rule passes through to bring its Newton form back to its
coefficients: each step subtracts a part of what it subtracts from and divides exactly, by `2`,
`3`, `4` or `5`.

The interpolation is mostly passes `r - a v` for a word `v`, which `subMulVal` does in one pass
with `subMul1`, and the evaluations are passes `r + a v`, in one pass with `addMul1`: with a
separate product by a word for each, Toom-4 was no faster than Toom-3.
-/

open ScalarArray

namespace MPN

/-! ## Fused passes -/

/-- One limb as an array. -/
def limbArray (c : UInt32) : UInt32Array := .replicate 1 c

private theorem size_limbArray (c : UInt32) : (limbArray c).toSlice.size = 1 := by
  simp [limbArray]

private theorem toNat_limbArray (c : UInt32) : toNat (limbArray c) = c.toNat := by
  rw [toNat_toSlice]
  simp [limbArray, UInt32Array.toList_replicate]

/--
`r - a v` in one pass, like GMP's `mpn_submul_1`, as `r.size` limbs: exact when `a v ≤ r`. The
borrow limb of `subMul1` is subtracted above `a`'s limbs.
-/
def subMulVal (r a : UInt32Array) (v : UInt32) : UInt32Array :=
  let a' := a.toSlice 0 r.size
  let p := subMul1 r 0 a' v (by simp [a']; lia)
  if a'.size < r.size then subInto p.1 a'.size (limbArray p.2) else p.1

@[simp] private theorem size_subMulVal (r a : UInt32Array) (v : UInt32) :
    (subMulVal r a v).size = r.size := by
  simp only [subMulVal]
  split
  · rw [size_subInto _ _ _ (by rw [size_subMul1, size_limbArray]; lia), size_subMul1]
  · rw [size_subMul1]

/-- The last step of `subMulVal`: the borrow out of `m` limbs subtracted above them. -/
private theorem toNat_subMulVal_aux (r : UInt32Array) (p : UInt32Array × UInt32) (m R A : Nat)
    (hp : p.1.size = r.size) (hm : m ≤ r.size) (hle : A ≤ R)
    (hsub : toNat p.1 + A = R + 2 ^ (32 * m) * p.2.toNat) :
    toNat (if m < r.size then subInto p.1 m (limbArray p.2) else p.1 : UInt32Array).toSlice =
      R - A := by
  have hP := toNat_lt p.1.toSlice
  simp only [UInt32Array.size_toSlice, Nat.min_self, Nat.sub_zero, hp] at hP
  by_cases h : m < r.size
  · rw [ite_eq_left h]
    have hpow : 2 ^ (32 * m) * toNat (limbArray p.2) ≤ toNat p.1 := by
      rw [toNat_limbArray]; lia
    rw [toNat_subInto_of_le _ _ _ (by rw [size_limbArray, hp]; lia) hpow, toNat_limbArray]
    lia
  · rw [ite_eq_right h]
    -- With no limb above, the borrow is zero.
    have hmr : 2 ^ (32 * r.size) ≤ 2 ^ (32 * m) := Nat.pow_le_pow_right (by decide) (by lia)
    have hc : p.2.toNat = 0 := by
      rcases Nat.eq_zero_or_pos p.2.toNat with h | h
      · exact h
      · have : 2 ^ (32 * m) ≤ 2 ^ (32 * m) * p.2.toNat := Nat.le_mul_of_pos_right _ h
        lia
    rw [hc, Nat.mul_zero, Nat.add_zero] at hsub
    lia

private theorem toNat_subMulVal (r a : UInt32Array) (v : UInt32)
    (hle : toNat a * v.toNat ≤ toNat r) :
    toNat (subMulVal r a v) = toNat r - toNat a * v.toNat := by
  have hR := toNat_lt r.toSlice
  simp only [UInt32Array.size_toSlice, Nat.min_self, Nat.sub_zero] at hR
  -- Cutting `a` to `r.size` limbs keeps its product.
  have ha' : toNat (a.toSlice 0 r.size) * v.toNat = toNat a * v.toNat := by
    rcases Nat.eq_zero_or_pos v.toNat with h | h
    · rw [h, Nat.mul_zero, Nat.mul_zero]
    · rw [toNat_toSlice_of_lt _ _ (by
        have : toNat a ≤ toNat a * v.toNat := Nat.le_mul_of_pos_right _ h
        lia)]
  have hsub := toNat_subMul1 r 0 (a.toSlice 0 r.size) v (by simp; lia)
  rw [ha'] at hsub
  simp only [Nat.mul_zero, Nat.pow_zero, Nat.one_mul, Nat.zero_add] at hsub
  simp only [subMulVal]
  exact toNat_subMulVal_aux r _ _ _ _ (size_subMul1 _ _ _ _ _)
    (by simp only [UInt32Array.size_toSlice]; lia) hle hsub

/--
`r + a v` in one pass, like GMP's `mpn_addmul_1`, as `r.size` limbs, for `a` shorter than `r` (and
`r` otherwise, which does not happen).
-/
def addMulVal (r : UInt32Array) (a : UInt32Array.Slice) (v : UInt32) : UInt32Array :=
  if h : a.size < r.size then
    let p := addMul1 r 0 a v (by lia)
    addInto p.1 a.size (limbArray p.2)
  else r

@[simp] private theorem size_addMulVal (r : UInt32Array) (a : UInt32Array.Slice) (v : UInt32) :
    (addMulVal r a v).size = r.size := by
  simp only [addMulVal]
  split
  · rw [size_addInto _ _ _ (by rw [size_addMul1, size_limbArray]; lia), size_addMul1]
  · rfl

/-- The last step of `addMulVal`: the carry out of `m` limbs added above them. -/
private theorem toNat_addMulVal_aux (r : UInt32Array) (p : UInt32Array × UInt32) (m S : Nat)
    (hp : p.1.size = r.size) (hm : m < r.size) (hlt : S < 2 ^ (32 * r.size))
    (hadd : toNat p.1 + 2 ^ (32 * m) * p.2.toNat = S) :
    toNat (addInto p.1 m (limbArray p.2)) = S := by
  rw [toNat_addInto_of_lt _ _ _ (by rw [size_limbArray, hp]; lia)
    (by rw [toNat_limbArray, hp]; lia), toNat_limbArray, hadd]

/-- When `a` is shorter than `r` and the sum fits in `r`, `addMulVal` adds. -/
private theorem toNat_addMulVal (r : UInt32Array) (a : UInt32Array.Slice) (v : UInt32)
    (h : a.size < r.size) (hlt : toNat r + toNat a * v.toNat < 2 ^ (32 * r.size)) :
    toNat (addMulVal r a v) = toNat r + toNat a * v.toNat := by
  have hadd := toNat_addMul1 r 0 a v (by lia)
  simp only [Nat.mul_zero, Nat.pow_zero, Nat.one_mul, Nat.zero_add] at hadd
  have e : addMulVal r a v = addInto (addMul1 r 0 a v (by lia)).1 a.size
      (limbArray (addMul1 r 0 a v (by lia)).2) := by
    simp [addMulVal, h]
  rw [e]
  exact toNat_addMulVal_aux r _ _ _ (size_addMul1 _ _ _ _ _) h hlt hadd

/-! ## Evaluation -/

/-- `x₀ + v₁ x₁ + v₂ x₂ + v₃ x₃`, the value of a polynomial in four parts, with room for it. -/
def eval4At (x₀ x₁ x₂ x₃ : UInt32Array.Slice) (v₁ v₂ v₃ : UInt32) : UInt32Array :=
  let n := max (max x₀.size x₁.size) (max x₂.size x₃.size) + 1
  addMulVal (addMulVal (addMulVal (copyPadded x₀ n) x₁ v₁) x₂ v₂) x₃ v₃

/-- `x₀ + v₁ x₁ + v₂ x₂`, the value of a polynomial in three parts, with room for it. -/
def eval3At (x₀ x₁ x₂ : UInt32Array.Slice) (v₁ v₂ : UInt32) : UInt32Array :=
  let n := max (max x₀.size x₁.size) x₂.size + 1
  addMulVal (addMulVal (copyPadded x₀ n) x₁ v₁) x₂ v₂

private theorem size_eval4At (x₀ x₁ x₂ x₃ : UInt32Array.Slice) (v₁ v₂ v₃ : UInt32) :
    (eval4At x₀ x₁ x₂ x₃ v₁ v₂ v₃).size =
      max (max x₀.size x₁.size) (max x₂.size x₃.size) + 1 := by
  simp only [eval4At, size_addMulVal]
  exact size_copyPadded _ _ (by lia)

private theorem size_eval3At (x₀ x₁ x₂ : UInt32Array.Slice) (v₁ v₂ : UInt32) :
    (eval3At x₀ x₁ x₂ v₁ v₂).size = max (max x₀.size x₁.size) x₂.size + 1 := by
  simp only [eval3At, size_addMulVal]
  exact size_copyPadded _ _ (by lia)

/-- Each part below `βᵐ` and `1 + v₁ + v₂ + v₃ ≤ β` keep the value below `βᵐ⁺¹`. -/
private theorem eval_lt (X₀ X₁ X₂ X₃ v₁ v₂ v₃ P : Nat) (h₀ : X₀ < P) (h₁ : X₁ < P) (h₂ : X₂ < P)
    (h₃ : X₃ < P) (hv : 1 + v₁ + v₂ + v₃ ≤ 2 ^ 32) :
    X₀ + X₁ * v₁ + X₂ * v₂ + X₃ * v₃ < 2 ^ 32 * P := by
  have e₁ := Nat.mul_le_mul_right v₁ (Nat.le_of_lt h₁)
  have e₂ := Nat.mul_le_mul_right v₂ (Nat.le_of_lt h₂)
  have e₃ := Nat.mul_le_mul_right v₃ (Nat.le_of_lt h₃)
  have e := Nat.mul_le_mul_right P hv
  rw [Nat.add_mul, Nat.add_mul, Nat.add_mul, Nat.one_mul] at e
  rw [Nat.mul_comm v₁ P, Nat.mul_comm v₂ P, Nat.mul_comm v₃ P] at e
  lia

private theorem toNat_eval4At (x₀ x₁ x₂ x₃ : UInt32Array.Slice) (v₁ v₂ v₃ : UInt32)
    (hv : 1 + v₁.toNat + v₂.toNat + v₃.toNat ≤ 2 ^ 32) :
    toNat (eval4At x₀ x₁ x₂ x₃ v₁ v₂ v₃) =
      toNat x₀ + toNat x₁ * v₁.toNat + toNat x₂ * v₂.toNat + toNat x₃ * v₃.toNat := by
  simp only [eval4At]
  generalize hn : max (max x₀.size x₁.size) (max x₂.size x₃.size) = m
  -- Each part is below `βᵐ`, so every partial sum is below `βᵐ⁺¹`.
  have hM : ∀ s : UInt32Array.Slice, s.size ≤ m → toNat s < 2 ^ (32 * m) := fun s hs =>
    Nat.lt_of_lt_of_le (toNat_lt s) (Nat.pow_le_pow_right (by decide) (by lia))
  have hpow : 2 ^ (32 * (m + 1)) = 2 ^ 32 * 2 ^ (32 * m) := by
    rw [← Nat.pow_add]; congr 1; lia
  have hsum := eval_lt _ _ _ _ _ _ _ _ (hM x₀ (by lia)) (hM x₁ (by lia)) (hM x₂ (by lia))
    (hM x₃ (by lia)) hv
  rw [← hpow] at hsum
  have s₀ : (copyPadded x₀ (m + 1)).size = m + 1 := size_copyPadded _ _ (by lia)
  have t₀ := toNat_copyPadded x₀ (m + 1)
  generalize copyPadded x₀ (m + 1) = r₀ at *
  have t₁ := toNat_addMulVal r₀ x₁ v₁ (by lia) (by rw [t₀, s₀]; lia)
  have s₁ : (addMulVal r₀ x₁ v₁).size = m + 1 := by rw [size_addMulVal, s₀]
  generalize addMulVal r₀ x₁ v₁ = r₁ at *
  have t₂ := toNat_addMulVal r₁ x₂ v₂ (by lia) (by rw [t₁, s₁, t₀]; lia)
  have s₂ : (addMulVal r₁ x₂ v₂).size = m + 1 := by rw [size_addMulVal, s₁]
  generalize addMulVal r₁ x₂ v₂ = r₂ at *
  rw [toNat_addMulVal r₂ x₃ v₃ (by lia) (by rw [t₂, s₂, t₁, t₀]; lia), t₂, t₁, t₀]

private theorem toNat_eval3At (x₀ x₁ x₂ : UInt32Array.Slice) (v₁ v₂ : UInt32)
    (hv : 1 + v₁.toNat + v₂.toNat ≤ 2 ^ 32) :
    toNat (eval3At x₀ x₁ x₂ v₁ v₂) = toNat x₀ + toNat x₁ * v₁.toNat + toNat x₂ * v₂.toNat := by
  simp only [eval3At]
  generalize hn : max (max x₀.size x₁.size) x₂.size = m
  have hM : ∀ s : UInt32Array.Slice, s.size ≤ m → toNat s < 2 ^ (32 * m) := fun s hs =>
    Nat.lt_of_lt_of_le (toNat_lt s) (Nat.pow_le_pow_right (by decide) (by lia))
  have hpow : 2 ^ (32 * (m + 1)) = 2 ^ 32 * 2 ^ (32 * m) := by
    rw [← Nat.pow_add]; congr 1; lia
  have hsum := eval_lt (toNat x₀) (toNat x₁) (toNat x₂) 0 v₁.toNat v₂.toNat 0 (2 ^ (32 * m))
    (hM x₀ (by lia)) (hM x₁ (by lia)) (hM x₂ (by lia))
    (Nat.lt_of_le_of_lt (Nat.zero_le _) (hM x₀ (by lia))) (by lia)
  rw [← hpow, Nat.zero_mul, Nat.add_zero] at hsum
  have s₀ : (copyPadded x₀ (m + 1)).size = m + 1 := size_copyPadded _ _ (by lia)
  have t₀ := toNat_copyPadded x₀ (m + 1)
  generalize copyPadded x₀ (m + 1) = r₀ at *
  have t₁ := toNat_addMulVal r₀ x₁ v₁ (by lia) (by rw [t₀, s₀]; lia)
  have s₁ : (addMulVal r₀ x₁ v₁).size = m + 1 := by rw [size_addMulVal, s₀]
  generalize addMulVal r₀ x₁ v₁ = r₁ at *
  rw [toNat_addMulVal r₁ x₂ v₂ (by lia) (by rw [t₁, s₁, t₀]; lia), t₁, t₀]

/-! ## Assembly -/

/-- `c₀ + x c₁ + x² c₂ + ⋯`. -/
def polyVal (x : Nat) : List Nat → Nat
  | [] => 0
  | c :: cs => c + x * polyVal x cs

/-- Adds `Σ cᵢ βᵏ⁽ᵒᶠᶠ ⁺ ⁱ⁾`... the coefficients `cs` at limbs `off`, `off + k`, `off + 2 k`, …. -/
def assembleFrom (r : UInt32Array) (off k : Nat) : List UInt32Array → UInt32Array
  | [] => r
  | c :: cs => assembleFrom (addInto r off (c.toSlice 0 (r.size - off))) (off + k) k cs

private theorem assembleFrom_spec (r : UInt32Array) (off k : Nat) (cs : List UInt32Array)
    (hk : off + k * cs.length ≤ r.size + k)
    (hlt : toNat r + 2 ^ (32 * off) *
      polyVal (2 ^ (32 * k)) (cs.map fun c : UInt32Array => toNat c) < 2 ^ (32 * r.size)) :
    (assembleFrom r off k cs).size = r.size ∧ toNat (assembleFrom r off k cs) =
      toNat r + 2 ^ (32 * off) *
        polyVal (2 ^ (32 * k)) (cs.map fun c : UInt32Array => toNat c) := by
  induction cs generalizing r off with
  | nil => simp [assembleFrom, polyVal]
  | cons c cs ih =>
    simp only [List.map_cons, polyVal, List.length_cons] at hk hlt ⊢
    have hoff : off ≤ r.size := by
      rcases Nat.lt_or_ge off (r.size + 1) with h | h
      · lia
      · -- Past the end, the remaining terms would not fit.
        lia
    have hpow : 2 ^ (32 * r.size) = 2 ^ (32 * off) * 2 ^ (32 * (r.size - off)) := by
      rw [← Nat.pow_add]; congr 1; lia
    have hpk : 2 ^ (32 * (off + k)) = 2 ^ (32 * off) * 2 ^ (32 * k) := by
      rw [← Nat.pow_add]; congr 1; lia
    -- `c` alone fits above `off`.
    have hC : toNat c < 2 ^ (32 * (r.size - off)) := by
      have : 2 ^ (32 * off) * toNat c < 2 ^ (32 * off) * 2 ^ (32 * (r.size - off)) := by
        rw [← hpow, Nat.mul_add] at *; lia
      exact Nat.lt_of_mul_lt_mul_left this
    have hcut : toNat (c.toSlice 0 (r.size - off)) = toNat c := toNat_toSlice_of_lt _ _ hC
    have hfit : off + (c.toSlice 0 (r.size - off)).size ≤ r.size := by
      rw [UInt32Array.size_toSlice]; lia
    have hs := size_addInto r off _ hfit
    have hv := toNat_addInto_of_lt r off _ hfit (by rw [hcut, Nat.mul_add] at *; lia)
    rw [hcut] at hv
    obtain ⟨ih₁, ih₂⟩ := ih (addInto r off (c.toSlice 0 (r.size - off))) (off + k)
      (by rw [hs]; lia) (by rw [hv, hs, hpk, Nat.mul_assoc]; rw [Nat.mul_add] at hlt; lia)
    refine ⟨by rw [assembleFrom, ih₁, hs], ?_⟩
    rw [assembleFrom, ih₂, hv, hpk, Nat.mul_assoc, Nat.mul_add]
    lia

/-! ## Interpolation steps -/

/-- `r_j = (w - c₀ - v c) / j`, the first step for the point `j`, with `v = jᵈ`. -/
private theorem toNat_rStep (w c₀ c : UInt32Array) (v : UInt32) (div : UInt32Array → UInt32Array)
    (j : Nat) (hdiv : ∀ (x : UInt32Array) X, toNat x = j * X → toNat (div x) = X) (C₀ C R : Nat)
    (h₀ : toNat c₀ = C₀) (hc : toNat c = C) (hw : toNat w = C₀ + C * v.toNat + j * R) :
    toNat (div (subMulVal (subVal w c₀) c v)) = R := by
  apply hdiv
  rw [toNat_subMulVal _ _ _ (by rw [toNat_subVal _ _ (by lia), hc]; lia),
    toNat_subVal _ _ (by lia), hc]
  lia

/-- A divided difference `(x - y) / l`. -/
private theorem toNat_ddStep (x y : UInt32Array) (div : UInt32Array → UInt32Array) (l : Nat)
    (hdiv : ∀ (x : UInt32Array) X, toNat x = l * X → toNat (div x) = X) (X Y Z : Nat)
    (hx : toNat x = X) (hy : toNat y = Y) (h : X = Y + l * Z) : toNat (div (subVal x y)) = Z := by
  apply hdiv
  rw [toNat_subVal _ _ (by lia)]
  lia

/-- A step of Horner's rule, `x - y v`. -/
private theorem toNat_hStep (x y : UInt32Array) (v : UInt32) (X Y Z : Nat) (hx : toNat x = X)
    (hy : toNat y = Y) (h : X = Y * v.toNat + Z) : toNat (subMulVal x y v) = Z := by
  rw [toNat_subMulVal _ _ _ (by lia)]
  lia

/-- A difference `x - y`. -/
private theorem toNat_sStep (x y : UInt32Array) (X Y Z : Nat) (hx : toNat x = X)
    (hy : toNat y = Y) (h : X = Y + Z) : toNat (subVal x y) = Z := by
  rw [toNat_subVal _ _ (by lia)]
  lia

/-! ## Interpolation in degree six -/

/--
`c₁, …, c₅` from `c₀`, `c₆` and `w_j = c(j)` for `j = 1, …, 5`: the values `r_j`, their divided
differences at `1, …, 5` (`e`, `f`, `g` and `c₅`), and Horner's rule at `4`, `3`, `2` and `1`.
-/
def toom44Interp (c₀ w₁ w₂ w₃ w₄ w₅ c₆ : UInt32Array) :
    UInt32Array × UInt32Array × UInt32Array × UInt32Array × UInt32Array :=
  let r₁ := subVal (subVal w₁ c₀) c₆
  let r₂ := divExact2 (subMulVal (subVal w₂ c₀) c₆ 64)
  let r₃ := divExact3 (subMulVal (subVal w₃ c₀) c₆ 729)
  let r₄ := divExact4 (subMulVal (subVal w₄ c₀) c₆ 4096)
  let r₅ := divExact5 (subMulVal (subVal w₅ c₀) c₆ 15625)
  let e₁ := subVal r₂ r₁
  let e₂ := subVal r₃ r₂
  let e₃ := subVal r₄ r₃
  let e₄ := subVal r₅ r₄
  let f₁ := divExact2 (subVal e₂ e₁)
  let f₂ := divExact2 (subVal e₃ e₂)
  let f₃ := divExact2 (subVal e₄ e₃)
  let g₁ := divExact3 (subVal f₂ f₁)
  let g₂ := divExact3 (subVal f₃ f₂)
  let c₅ := divExact4 (subVal g₂ g₁)
  let h₄ := subMulVal g₁ c₅ 4
  let p₃ := subMulVal f₁ h₄ 3
  let p₄ := subMulVal h₄ c₅ 3
  let q₂ := subMulVal e₁ p₃ 2
  let q₃ := subMulVal p₃ p₄ 2
  let q₄ := subMulVal p₄ c₅ 2
  (subVal r₁ q₂, subVal q₂ q₃, subVal q₃ q₄, subVal q₄ c₅, c₅)

private theorem toom44Interp_spec (c₀ w₁ w₂ w₃ w₄ w₅ c₆ : UInt32Array)
    (C₀ C₁ C₂ C₃ C₄ C₅ C₆ : Nat) (h₀ : toNat c₀ = C₀) (h₆ : toNat c₆ = C₆)
    (h₁ : toNat w₁ = C₀ + C₁ + C₂ + C₃ + C₄ + C₅ + C₆)
    (h₂ : toNat w₂ = C₀ + 2 * C₁ + 4 * C₂ + 8 * C₃ + 16 * C₄ + 32 * C₅ + 64 * C₆)
    (h₃ : toNat w₃ = C₀ + 3 * C₁ + 9 * C₂ + 27 * C₃ + 81 * C₄ + 243 * C₅ + 729 * C₆)
    (h₄ : toNat w₄ = C₀ + 4 * C₁ + 16 * C₂ + 64 * C₃ + 256 * C₄ + 1024 * C₅ + 4096 * C₆)
    (h₅ : toNat w₅ = C₀ + 5 * C₁ + 25 * C₂ + 125 * C₃ + 625 * C₄ + 3125 * C₅ + 15625 * C₆) :
    toNat (toom44Interp c₀ w₁ w₂ w₃ w₄ w₅ c₆).1 = C₁ ∧
      toNat (toom44Interp c₀ w₁ w₂ w₃ w₄ w₅ c₆).2.1 = C₂ ∧
      toNat (toom44Interp c₀ w₁ w₂ w₃ w₄ w₅ c₆).2.2.1 = C₃ ∧
      toNat (toom44Interp c₀ w₁ w₂ w₃ w₄ w₅ c₆).2.2.2.1 = C₄ ∧
      toNat (toom44Interp c₀ w₁ w₂ w₃ w₄ w₅ c₆).2.2.2.2 = C₅ := by
  simp only [toom44Interp]
  -- `r_j = c₁ + c₂ j + c₃ j² + c₄ j³ + c₅ j⁴`.
  have hr₁ : toNat (subVal (subVal w₁ c₀) c₆) = C₁ + C₂ + C₃ + C₄ + C₅ := by
    rw [toNat_subVal _ _ (by rw [toNat_subVal _ _ (by lia)]; lia), toNat_subVal _ _ (by lia)]
    lia
  have hr₂ := toNat_rStep w₂ c₀ c₆ 64 divExact2 2 toNat_divExact2 C₀ C₆
    (C₁ + 2 * C₂ + 4 * C₃ + 8 * C₄ + 16 * C₅) h₀ h₆
    (by rw [h₂]; simp only [UInt32.reduceToNat]; lia)
  have hr₃ := toNat_rStep w₃ c₀ c₆ 729 divExact3 3 toNat_divExact3 C₀ C₆
    (C₁ + 3 * C₂ + 9 * C₃ + 27 * C₄ + 81 * C₅) h₀ h₆
    (by rw [h₃]; simp only [UInt32.reduceToNat]; lia)
  have hr₄ := toNat_rStep w₄ c₀ c₆ 4096 divExact4 4 toNat_divExact4 C₀ C₆
    (C₁ + 4 * C₂ + 16 * C₃ + 64 * C₄ + 256 * C₅) h₀ h₆
    (by rw [h₄]; simp only [UInt32.reduceToNat]; lia)
  have hr₅ := toNat_rStep w₅ c₀ c₆ 15625 divExact5 5 toNat_divExact5 C₀ C₆
    (C₁ + 5 * C₂ + 25 * C₃ + 125 * C₄ + 625 * C₅) h₀ h₆
    (by rw [h₅]; simp only [UInt32.reduceToNat]; lia)
  generalize subVal (subVal w₁ c₀) c₆ = r₁ at *
  generalize divExact2 (subMulVal (subVal w₂ c₀) c₆ 64) = r₂ at *
  generalize divExact3 (subMulVal (subVal w₃ c₀) c₆ 729) = r₃ at *
  generalize divExact4 (subMulVal (subVal w₄ c₀) c₆ 4096) = r₄ at *
  generalize divExact5 (subMulVal (subVal w₅ c₀) c₆ 15625) = r₅ at *
  -- The divided differences.
  have he₁ := toNat_sStep r₂ r₁ _ _ (C₂ + 3 * C₃ + 7 * C₄ + 15 * C₅) hr₂ hr₁ (by lia)
  have he₂ := toNat_sStep r₃ r₂ _ _ (C₂ + 5 * C₃ + 19 * C₄ + 65 * C₅) hr₃ hr₂ (by lia)
  have he₃ := toNat_sStep r₄ r₃ _ _ (C₂ + 7 * C₃ + 37 * C₄ + 175 * C₅) hr₄ hr₃ (by lia)
  have he₄ := toNat_sStep r₅ r₄ _ _ (C₂ + 9 * C₃ + 61 * C₄ + 369 * C₅) hr₅ hr₄ (by lia)
  generalize subVal r₂ r₁ = e₁ at *
  generalize subVal r₃ r₂ = e₂ at *
  generalize subVal r₄ r₃ = e₃ at *
  generalize subVal r₅ r₄ = e₄ at *
  have hf₁ := toNat_ddStep e₂ e₁ divExact2 2 toNat_divExact2 _ _ (C₃ + 6 * C₄ + 25 * C₅) he₂ he₁
    (by lia)
  have hf₂ := toNat_ddStep e₃ e₂ divExact2 2 toNat_divExact2 _ _ (C₃ + 9 * C₄ + 55 * C₅) he₃ he₂
    (by lia)
  have hf₃ := toNat_ddStep e₄ e₃ divExact2 2 toNat_divExact2 _ _ (C₃ + 12 * C₄ + 97 * C₅) he₄ he₃
    (by lia)
  generalize divExact2 (subVal e₂ e₁) = f₁ at *
  generalize divExact2 (subVal e₃ e₂) = f₂ at *
  generalize divExact2 (subVal e₄ e₃) = f₃ at *
  have hg₁ := toNat_ddStep f₂ f₁ divExact3 3 toNat_divExact3 _ _ (C₄ + 10 * C₅) hf₂ hf₁ (by lia)
  have hg₂ := toNat_ddStep f₃ f₂ divExact3 3 toNat_divExact3 _ _ (C₄ + 14 * C₅) hf₃ hf₂ (by lia)
  generalize divExact3 (subVal f₂ f₁) = g₁ at *
  generalize divExact3 (subVal f₃ f₂) = g₂ at *
  have hc₅ := toNat_ddStep g₂ g₁ divExact4 4 toNat_divExact4 _ _ C₅ hg₂ hg₁ (by lia)
  generalize divExact4 (subVal g₂ g₁) = c₅ at *
  -- Horner's rule at `4`, `3`, `2`, then `1`.
  have hh₄ := toNat_hStep g₁ c₅ 4 _ _ (C₄ + 6 * C₅) hg₁ hc₅ (by simp only [UInt32.reduceToNat]; lia)
  generalize subMulVal g₁ c₅ 4 = h₄ at *
  have hp₃ := toNat_hStep f₁ h₄ 3 _ _ (C₃ + 3 * C₄ + 7 * C₅) hf₁ hh₄
    (by simp only [UInt32.reduceToNat]; lia)
  have hp₄ := toNat_hStep h₄ c₅ 3 _ _ (C₄ + 3 * C₅) hh₄ hc₅ (by simp only [UInt32.reduceToNat]; lia)
  generalize subMulVal f₁ h₄ 3 = p₃ at *
  generalize subMulVal h₄ c₅ 3 = p₄ at *
  have hq₂ := toNat_hStep e₁ p₃ 2 _ _ (C₂ + C₃ + C₄ + C₅) he₁ hp₃
    (by simp only [UInt32.reduceToNat]; lia)
  have hq₃ := toNat_hStep p₃ p₄ 2 _ _ (C₃ + C₄ + C₅) hp₃ hp₄
    (by simp only [UInt32.reduceToNat]; lia)
  have hq₄ := toNat_hStep p₄ c₅ 2 _ _ (C₄ + C₅) hp₄ hc₅ (by simp only [UInt32.reduceToNat]; lia)
  generalize subMulVal e₁ p₃ 2 = q₂ at *
  generalize subMulVal p₃ p₄ 2 = q₃ at *
  generalize subMulVal p₄ c₅ 2 = q₄ at *
  exact ⟨toNat_sStep _ _ _ _ _ hr₁ hq₂ (by lia), toNat_sStep _ _ _ _ _ hq₂ hq₃ (by lia),
    toNat_sStep _ _ _ _ _ hq₃ hq₄ (by lia), toNat_sStep _ _ _ _ _ hq₄ hc₅ (by lia), hc₅⟩

/-! ## Interpolation in degree five -/

/--
`c₁, …, c₄` from `c₀`, `c₅` and `w_j = c(j)` for `j = 1, …, 4`: the values `r_j`, their divided
differences at `1, …, 4` (`e`, `f` and `c₄`), and Horner's rule at `3`, `2` and `1`.
-/
def toom43Interp (c₀ w₁ w₂ w₃ w₄ c₅ : UInt32Array) :
    UInt32Array × UInt32Array × UInt32Array × UInt32Array :=
  let r₁ := subVal (subVal w₁ c₀) c₅
  let r₂ := divExact2 (subMulVal (subVal w₂ c₀) c₅ 32)
  let r₃ := divExact3 (subMulVal (subVal w₃ c₀) c₅ 243)
  let r₄ := divExact4 (subMulVal (subVal w₄ c₀) c₅ 1024)
  let e₁ := subVal r₂ r₁
  let e₂ := subVal r₃ r₂
  let e₃ := subVal r₄ r₃
  let f₁ := divExact2 (subVal e₂ e₁)
  let f₂ := divExact2 (subVal e₃ e₂)
  let c₄ := divExact3 (subVal f₂ f₁)
  let p₃ := subMulVal f₁ c₄ 3
  let q₂ := subMulVal e₁ p₃ 2
  let q₃ := subMulVal p₃ c₄ 2
  (subVal r₁ q₂, subVal q₂ q₃, subVal q₃ c₄, c₄)

private theorem toom43Interp_spec (c₀ w₁ w₂ w₃ w₄ c₅ : UInt32Array)
    (C₀ C₁ C₂ C₃ C₄ C₅ : Nat) (h₀ : toNat c₀ = C₀) (h₅ : toNat c₅ = C₅)
    (h₁ : toNat w₁ = C₀ + C₁ + C₂ + C₃ + C₄ + C₅)
    (h₂ : toNat w₂ = C₀ + 2 * C₁ + 4 * C₂ + 8 * C₃ + 16 * C₄ + 32 * C₅)
    (h₃ : toNat w₃ = C₀ + 3 * C₁ + 9 * C₂ + 27 * C₃ + 81 * C₄ + 243 * C₅)
    (h₄ : toNat w₄ = C₀ + 4 * C₁ + 16 * C₂ + 64 * C₃ + 256 * C₄ + 1024 * C₅) :
    toNat (toom43Interp c₀ w₁ w₂ w₃ w₄ c₅).1 = C₁ ∧
      toNat (toom43Interp c₀ w₁ w₂ w₃ w₄ c₅).2.1 = C₂ ∧
      toNat (toom43Interp c₀ w₁ w₂ w₃ w₄ c₅).2.2.1 = C₃ ∧
      toNat (toom43Interp c₀ w₁ w₂ w₃ w₄ c₅).2.2.2 = C₄ := by
  simp only [toom43Interp]
  -- `r_j = c₁ + c₂ j + c₃ j² + c₄ j³`.
  have hr₁ : toNat (subVal (subVal w₁ c₀) c₅) = C₁ + C₂ + C₃ + C₄ := by
    rw [toNat_subVal _ _ (by rw [toNat_subVal _ _ (by lia)]; lia), toNat_subVal _ _ (by lia)]
    lia
  have hr₂ := toNat_rStep w₂ c₀ c₅ 32 divExact2 2 toNat_divExact2 C₀ C₅
    (C₁ + 2 * C₂ + 4 * C₃ + 8 * C₄) h₀ h₅ (by rw [h₂]; simp only [UInt32.reduceToNat]; lia)
  have hr₃ := toNat_rStep w₃ c₀ c₅ 243 divExact3 3 toNat_divExact3 C₀ C₅
    (C₁ + 3 * C₂ + 9 * C₃ + 27 * C₄) h₀ h₅ (by rw [h₃]; simp only [UInt32.reduceToNat]; lia)
  have hr₄ := toNat_rStep w₄ c₀ c₅ 1024 divExact4 4 toNat_divExact4 C₀ C₅
    (C₁ + 4 * C₂ + 16 * C₃ + 64 * C₄) h₀ h₅ (by rw [h₄]; simp only [UInt32.reduceToNat]; lia)
  generalize subVal (subVal w₁ c₀) c₅ = r₁ at *
  generalize divExact2 (subMulVal (subVal w₂ c₀) c₅ 32) = r₂ at *
  generalize divExact3 (subMulVal (subVal w₃ c₀) c₅ 243) = r₃ at *
  generalize divExact4 (subMulVal (subVal w₄ c₀) c₅ 1024) = r₄ at *
  -- The divided differences.
  have he₁ := toNat_sStep r₂ r₁ _ _ (C₂ + 3 * C₃ + 7 * C₄) hr₂ hr₁ (by lia)
  have he₂ := toNat_sStep r₃ r₂ _ _ (C₂ + 5 * C₃ + 19 * C₄) hr₃ hr₂ (by lia)
  have he₃ := toNat_sStep r₄ r₃ _ _ (C₂ + 7 * C₃ + 37 * C₄) hr₄ hr₃ (by lia)
  generalize subVal r₂ r₁ = e₁ at *
  generalize subVal r₃ r₂ = e₂ at *
  generalize subVal r₄ r₃ = e₃ at *
  have hf₁ := toNat_ddStep e₂ e₁ divExact2 2 toNat_divExact2 _ _ (C₃ + 6 * C₄) he₂ he₁ (by lia)
  have hf₂ := toNat_ddStep e₃ e₂ divExact2 2 toNat_divExact2 _ _ (C₃ + 9 * C₄) he₃ he₂ (by lia)
  generalize divExact2 (subVal e₂ e₁) = f₁ at *
  generalize divExact2 (subVal e₃ e₂) = f₂ at *
  have hc₄ := toNat_ddStep f₂ f₁ divExact3 3 toNat_divExact3 _ _ C₄ hf₂ hf₁ (by lia)
  generalize divExact3 (subVal f₂ f₁) = c₄ at *
  -- Horner's rule at `3`, `2`, then `1`.
  have hp₃ := toNat_hStep f₁ c₄ 3 _ _ (C₃ + 3 * C₄) hf₁ hc₄ (by simp only [UInt32.reduceToNat]; lia)
  generalize subMulVal f₁ c₄ 3 = p₃ at *
  have hq₂ := toNat_hStep e₁ p₃ 2 _ _ (C₂ + C₃ + C₄) he₁ hp₃
    (by simp only [UInt32.reduceToNat]; lia)
  have hq₃ := toNat_hStep p₃ c₄ 2 _ _ (C₃ + C₄) hp₃ hc₄ (by simp only [UInt32.reduceToNat]; lia)
  generalize subMulVal e₁ p₃ 2 = q₂ at *
  generalize subMulVal p₃ c₄ 2 = q₃ at *
  exact ⟨toNat_sStep _ _ _ _ _ hr₁ hq₂ (by lia), toNat_sStep _ _ _ _ _ hq₂ hq₃ (by lia),
    toNat_sStep _ _ _ _ _ hq₃ hc₄ (by lia), hc₄⟩

/-! ## Products -/

private theorem toNat_zeros (n : Nat) : toNat (UInt32Array.replicate n 0) = 0 := by
  rw [toNat_toSlice]
  simp [UInt32Array.toList_replicate]

/--
`n` limbs of `C₀ + C₁ x + ⋯` at `x = βᵏ` from arrays `cs` whose values are `Cs`, when the sum fits:
the assembly of every Toom product.
-/
private theorem assemble_spec (n k : Nat) (cs : List UInt32Array) (Cs : List Nat)
    (hk : k * cs.length ≤ n + k) (hcs : cs.map (fun c : UInt32Array => toNat c) = Cs)
    (hlt : polyVal (2 ^ (32 * k)) Cs < 2 ^ (32 * n)) :
    (assembleFrom (.replicate n 0) 0 k cs).size = n ∧
      toNat (assembleFrom (.replicate n 0) 0 k cs) = polyVal (2 ^ (32 * k)) Cs := by
  have h := assembleFrom_spec (.replicate n 0) 0 k cs (by simp; lia)
    (by rw [toNat_zeros, hcs]; simpa using hlt)
  rw [toNat_zeros, hcs] at h
  simpa using h

private theorem polyVal7 (x C₀ C₁ C₂ C₃ C₄ C₅ C₆ : Nat) :
    polyVal x [C₀, C₁, C₂, C₃, C₄, C₅, C₆] =
      C₀ + x * (C₁ + x * (C₂ + x * (C₃ + x * (C₄ + x * (C₅ + x * C₆))))) := by
  simp [polyVal]

private theorem polyVal6 (x C₀ C₁ C₂ C₃ C₄ C₅ : Nat) :
    polyVal x [C₀, C₁, C₂, C₃, C₄, C₅] =
      C₀ + x * (C₁ + x * (C₂ + x * (C₃ + x * (C₄ + x * C₅)))) := by
  simp [polyVal]

/--
The product `a * b` by one step of Toom-4, splitting both in four at `k` limbs, for `4 ≤ k`,
`3 k ≤ b.size ≤ a.size`. It computes the seven products with `mulRec`, which only receives inputs
smaller than `a` and `b` together.
-/
public def toom44At (a b : UInt32Array.Slice) (k : Nat) (hk : 4 ≤ k) (hkb : 3 * k ≤ b.size)
    (hab : b.size ≤ a.size)
    (mulRec : (x y : UInt32Array.Slice) → x.size + y.size < a.size + b.size → UInt32Array) :
    UInt32Array :=
  let a₀ := a.slice 0 k
  let a₁ := a.slice k (2 * k)
  let a₂ := a.slice (2 * k) (3 * k)
  let a₃ := a.slice (3 * k) a.size
  let b₀ := b.slice 0 k
  let b₁ := b.slice k (2 * k)
  let b₂ := b.slice (2 * k) (3 * k)
  let b₃ := b.slice (3 * k) b.size
  let c₀ := mulRec a₀ b₀ (by simp only [a₀, b₀, UInt32Array.Slice.size_slice]; lia)
  let c₆ := mulRec a₃ b₃ (by simp only [a₃, b₃, UInt32Array.Slice.size_slice]; lia)
  let w₁ := mulRec (eval4At a₀ a₁ a₂ a₃ 1 1 1) (eval4At b₀ b₁ b₂ b₃ 1 1 1) (by
    simp only [UInt32Array.size_toSlice, size_eval4At, a₀, a₁, a₂, a₃, b₀, b₁, b₂, b₃,
      UInt32Array.Slice.size_slice]
    lia)
  let w₂ := mulRec (eval4At a₀ a₁ a₂ a₃ 2 4 8) (eval4At b₀ b₁ b₂ b₃ 2 4 8) (by
    simp only [UInt32Array.size_toSlice, size_eval4At, a₀, a₁, a₂, a₃, b₀, b₁, b₂, b₃,
      UInt32Array.Slice.size_slice]
    lia)
  let w₃ := mulRec (eval4At a₀ a₁ a₂ a₃ 3 9 27) (eval4At b₀ b₁ b₂ b₃ 3 9 27) (by
    simp only [UInt32Array.size_toSlice, size_eval4At, a₀, a₁, a₂, a₃, b₀, b₁, b₂, b₃,
      UInt32Array.Slice.size_slice]
    lia)
  let w₄ := mulRec (eval4At a₀ a₁ a₂ a₃ 4 16 64) (eval4At b₀ b₁ b₂ b₃ 4 16 64) (by
    simp only [UInt32Array.size_toSlice, size_eval4At, a₀, a₁, a₂, a₃, b₀, b₁, b₂, b₃,
      UInt32Array.Slice.size_slice]
    lia)
  let w₅ := mulRec (eval4At a₀ a₁ a₂ a₃ 5 25 125) (eval4At b₀ b₁ b₂ b₃ 5 25 125) (by
    simp only [UInt32Array.size_toSlice, size_eval4At, a₀, a₁, a₂, a₃, b₀, b₁, b₂, b₃,
      UInt32Array.Slice.size_slice]
    lia)
  let i := toom44Interp c₀ w₁ w₂ w₃ w₄ w₅ c₆
  assembleFrom (.replicate (a.size + b.size) 0) 0 k
    [c₀, i.1, i.2.1, i.2.2.1, i.2.2.2.1, i.2.2.2.2, c₆]

private theorem toom44_w (A₀ A₁ A₂ A₃ B₀ B₁ B₂ B₃ j : Nat) :
    (A₀ + A₁ * j + A₂ * (j * j) + A₃ * (j * j * j)) *
        (B₀ + B₁ * j + B₂ * (j * j) + B₃ * (j * j * j)) =
      A₀ * B₀ + j * (A₀ * B₁ + A₁ * B₀) + j * j * (A₀ * B₂ + A₁ * B₁ + A₂ * B₀) +
        j * j * j * (A₀ * B₃ + A₁ * B₂ + A₂ * B₁ + A₃ * B₀) +
        j * j * j * j * (A₁ * B₃ + A₂ * B₂ + A₃ * B₁) + j * j * j * j * j * (A₂ * B₃ + A₃ * B₂) +
        j * j * j * j * j * j * (A₃ * B₃) := by
  grind

private theorem toom44_sum (A₀ A₁ A₂ A₃ B₀ B₁ B₂ B₃ x : Nat) :
    A₀ * B₀ + x * ((A₀ * B₁ + A₁ * B₀) + x * ((A₀ * B₂ + A₁ * B₁ + A₂ * B₀) +
      x * ((A₀ * B₃ + A₁ * B₂ + A₂ * B₁ + A₃ * B₀) + x * ((A₁ * B₃ + A₂ * B₂ + A₃ * B₁) +
      x * ((A₂ * B₃ + A₃ * B₂) + x * (A₃ * B₃)))))) =
      (A₀ + x * A₁ + x * x * A₂ + x * x * x * A₃) *
        (B₀ + x * B₁ + x * x * B₂ + x * x * x * B₃) := by
  grind

public theorem toom44At_spec (a b : UInt32Array.Slice) (k : Nat) (hk : 4 ≤ k)
    (hkb : 3 * k ≤ b.size) (hab : b.size ≤ a.size)
    (mulRec : (x y : UInt32Array.Slice) → x.size + y.size < a.size + b.size → UInt32Array)
    (hrec : ∀ x y h, (mulRec x y h).size = x.size + y.size ∧
      toNat (mulRec x y h) = toNat x * toNat y) :
    (toom44At a b k hk hkb hab mulRec).size = a.size + b.size ∧
      toNat (toom44At a b k hk hkb hab mulRec) = toNat a * toNat b := by
  have ha := toNat_slice_four a k (by lia)
  have hb := toNat_slice_four b k hkb
  have hA := toNat_lt a
  have hB := toNat_lt b
  -- The seven products.
  obtain ⟨-, hv₀⟩ := hrec (a.slice 0 k) (b.slice 0 k)
    (by simp only [UInt32Array.Slice.size_slice]; lia)
  obtain ⟨-, hv₆⟩ := hrec (a.slice (3 * k) a.size) (b.slice (3 * k) b.size)
    (by simp only [UInt32Array.Slice.size_slice]; lia)
  have hw : ∀ (v₁ v₂ v₃ : UInt32), 1 + v₁.toNat + v₂.toNat + v₃.toNat ≤ 2 ^ 32 → ∀ h,
      toNat (mulRec
        (eval4At (a.slice 0 k) (a.slice k (2 * k)) (a.slice (2 * k) (3 * k))
          (a.slice (3 * k) a.size) v₁ v₂ v₃)
        (eval4At (b.slice 0 k) (b.slice k (2 * k)) (b.slice (2 * k) (3 * k))
          (b.slice (3 * k) b.size) v₁ v₂ v₃) h) =
      (toNat (a.slice 0 k) + toNat (a.slice k (2 * k)) * v₁.toNat +
          toNat (a.slice (2 * k) (3 * k)) * v₂.toNat + toNat (a.slice (3 * k) a.size) * v₃.toNat) *
        (toNat (b.slice 0 k) + toNat (b.slice k (2 * k)) * v₁.toNat +
          toNat (b.slice (2 * k) (3 * k)) * v₂.toNat + toNat (b.slice (3 * k) b.size) * v₃.toNat) :=
    fun v₁ v₂ v₃ hv h => by rw [(hrec _ _ h).2, toNat_eval4At _ _ _ _ _ _ _ hv,
      toNat_eval4At _ _ _ _ _ _ _ hv]
  simp only [toom44At]
  generalize hW₁ : mulRec (eval4At (a.slice 0 k) _ _ _ 1 1 1) _ _ = w₁
  generalize hW₂ : mulRec (eval4At (a.slice 0 k) _ _ _ 2 4 8) _ _ = w₂
  generalize hW₃ : mulRec (eval4At (a.slice 0 k) _ _ _ 3 9 27) _ _ = w₃
  generalize hW₄ : mulRec (eval4At (a.slice 0 k) _ _ _ 4 16 64) _ _ = w₄
  generalize hW₅ : mulRec (eval4At (a.slice 0 k) _ _ _ 5 25 125) _ _ = w₅
  have hw₁ := hW₁ ▸ hw 1 1 1 (by decide) _
  have hw₂ := hW₂ ▸ hw 2 4 8 (by decide) _
  have hw₃ := hW₃ ▸ hw 3 9 27 (by decide) _
  have hw₄ := hW₄ ▸ hw 4 16 64 (by decide) _
  have hw₅ := hW₅ ▸ hw 5 25 125 (by decide) _
  simp only [UInt32.reduceToNat] at hw₁ hw₂ hw₃ hw₄ hw₅
  clear hw hW₁ hW₂ hW₃ hW₄ hW₅
  generalize mulRec (a.slice 0 k) _ _ = c₀ at *
  generalize mulRec (a.slice (3 * k) a.size) _ _ = c₆ at *
  generalize toNat (a.slice 0 k) = A₀ at *
  generalize toNat (a.slice k (2 * k)) = A₁ at *
  generalize toNat (a.slice (2 * k) (3 * k)) = A₂ at *
  generalize toNat (a.slice (3 * k) a.size) = A₃ at *
  generalize toNat (b.slice 0 k) = B₀ at *
  generalize toNat (b.slice k (2 * k)) = B₁ at *
  generalize toNat (b.slice (2 * k) (3 * k)) = B₂ at *
  generalize toNat (b.slice (3 * k) b.size) = B₃ at *
  have hlt : toNat a * toNat b < 2 ^ (32 * (a.size + b.size)) := by
    rw [Nat.mul_add, Nat.pow_add]
    exact Nat.mul_lt_mul'' hA hB
  -- Interpolation recovers the middle coefficients.
  have hi := toom44Interp_spec c₀ w₁ w₂ w₃ w₄ w₅ c₆ (A₀ * B₀) (A₀ * B₁ + A₁ * B₀)
    (A₀ * B₂ + A₁ * B₁ + A₂ * B₀) (A₀ * B₃ + A₁ * B₂ + A₂ * B₁ + A₃ * B₀)
    (A₁ * B₃ + A₂ * B₂ + A₃ * B₁) (A₂ * B₃ + A₃ * B₂) (A₃ * B₃) hv₀ hv₆
    (by rw [hw₁]; grind) (by rw [hw₂, toom44_w _ _ _ _ _ _ _ _ 2])
    (by rw [hw₃, toom44_w _ _ _ _ _ _ _ _ 3]) (by rw [hw₄, toom44_w _ _ _ _ _ _ _ _ 4])
    (by rw [hw₅, toom44_w _ _ _ _ _ _ _ _ 5])
  generalize toom44Interp c₀ w₁ w₂ w₃ w₄ w₅ c₆ = i at *
  rw [ha, hb] at hlt ⊢
  have key := assemble_spec (a.size + b.size) k [c₀, i.1, i.2.1, i.2.2.1, i.2.2.2.1, i.2.2.2.2, c₆]
    _ (by simp; lia) (by simp only [List.map_cons, List.map_nil, hv₀, hi.1, hi.2.1, hi.2.2.1,
      hi.2.2.2.1, hi.2.2.2.2, hv₆]; rfl)
    (by rw [polyVal7, toom44_sum]; exact hlt)
  rw [polyVal7, toom44_sum] at key
  exact key

/--
The product `a * b` by one step of Toom-4, for `32 ≤ b.size ≤ a.size < 4 b.size / 3`: it splits
both at a quarter of `a` when three such parts fit in `b`, and at a quarter of `b` otherwise.
-/
public def toom44 (a b : UInt32Array.Slice) (hb : 32 ≤ b.size) (hab : b.size ≤ a.size)
    (_h43 : 3 * a.size < 4 * b.size)
    (mulRec : (x y : UInt32Array.Slice) → x.size + y.size < a.size + b.size → UInt32Array) :
    UInt32Array :=
  if h : 3 * ((a.size + 3) / 4) ≤ b.size then
    toom44At a b ((a.size + 3) / 4) (by lia) h hab mulRec
  else
    toom44At a b ((b.size + 3) / 4) (by lia) (by lia) hab mulRec

public theorem toom44_spec (a b : UInt32Array.Slice) (hb : 32 ≤ b.size) (hab : b.size ≤ a.size)
    (h43 : 3 * a.size < 4 * b.size)
    (mulRec : (x y : UInt32Array.Slice) → x.size + y.size < a.size + b.size → UInt32Array)
    (hrec : ∀ x y h, (mulRec x y h).size = x.size + y.size ∧
      toNat (mulRec x y h) = toNat x * toNat y) :
    (toom44 a b hb hab h43 mulRec).size = a.size + b.size ∧
      toNat (toom44 a b hb hab h43 mulRec) = toNat a * toNat b := by
  by_cases h : 3 * ((a.size + 3) / 4) ≤ b.size
  · have e : toom44 a b hb hab h43 mulRec =
        toom44At a b ((a.size + 3) / 4) (by lia) h hab mulRec := by
      unfold toom44
      rw [dite_eq_left h]
    rw [e]
    exact toom44At_spec _ _ _ _ _ _ _ hrec
  · have e : toom44 a b hb hab h43 mulRec =
        toom44At a b ((b.size + 3) / 4) (by lia) (by lia) hab mulRec := by
      unfold toom44
      rw [dite_eq_right h]
    rw [e]
    exact toom44At_spec _ _ _ _ _ _ _ hrec

/--
The product `a * b` by one step of Toom-4 by 3, splitting `a` in four and `b` in three at `k`
limbs, for `4 ≤ k`, `3 k ≤ a.size` and `2 k ≤ b.size`. It computes the six products with
`mulRec`, which only receives inputs smaller than `a` and `b` together.
-/
public def toom43At (a b : UInt32Array.Slice) (k : Nat) (hk : 4 ≤ k) (hka : 3 * k ≤ a.size)
    (hkb : 2 * k ≤ b.size)
    (mulRec : (x y : UInt32Array.Slice) → x.size + y.size < a.size + b.size → UInt32Array) :
    UInt32Array :=
  let a₀ := a.slice 0 k
  let a₁ := a.slice k (2 * k)
  let a₂ := a.slice (2 * k) (3 * k)
  let a₃ := a.slice (3 * k) a.size
  let b₀ := b.slice 0 k
  let b₁ := b.slice k (2 * k)
  let b₂ := b.slice (2 * k) b.size
  let c₀ := mulRec a₀ b₀ (by simp only [a₀, b₀, UInt32Array.Slice.size_slice]; lia)
  let c₅ := mulRec a₃ b₂ (by simp only [a₃, b₂, UInt32Array.Slice.size_slice]; lia)
  let w₁ := mulRec (eval4At a₀ a₁ a₂ a₃ 1 1 1) (eval3At b₀ b₁ b₂ 1 1) (by
    simp only [UInt32Array.size_toSlice, size_eval4At, size_eval3At, a₀, a₁, a₂, a₃, b₀, b₁, b₂,
      UInt32Array.Slice.size_slice]
    lia)
  let w₂ := mulRec (eval4At a₀ a₁ a₂ a₃ 2 4 8) (eval3At b₀ b₁ b₂ 2 4) (by
    simp only [UInt32Array.size_toSlice, size_eval4At, size_eval3At, a₀, a₁, a₂, a₃, b₀, b₁, b₂,
      UInt32Array.Slice.size_slice]
    lia)
  let w₃ := mulRec (eval4At a₀ a₁ a₂ a₃ 3 9 27) (eval3At b₀ b₁ b₂ 3 9) (by
    simp only [UInt32Array.size_toSlice, size_eval4At, size_eval3At, a₀, a₁, a₂, a₃, b₀, b₁, b₂,
      UInt32Array.Slice.size_slice]
    lia)
  let w₄ := mulRec (eval4At a₀ a₁ a₂ a₃ 4 16 64) (eval3At b₀ b₁ b₂ 4 16) (by
    simp only [UInt32Array.size_toSlice, size_eval4At, size_eval3At, a₀, a₁, a₂, a₃, b₀, b₁, b₂,
      UInt32Array.Slice.size_slice]
    lia)
  let i := toom43Interp c₀ w₁ w₂ w₃ w₄ c₅
  assembleFrom (.replicate (a.size + b.size) 0) 0 k [c₀, i.1, i.2.1, i.2.2.1, i.2.2.2, c₅]

private theorem toom43_w (A₀ A₁ A₂ A₃ B₀ B₁ B₂ j : Nat) :
    (A₀ + A₁ * j + A₂ * (j * j) + A₃ * (j * j * j)) * (B₀ + B₁ * j + B₂ * (j * j)) =
      A₀ * B₀ + j * (A₀ * B₁ + A₁ * B₀) + j * j * (A₀ * B₂ + A₁ * B₁ + A₂ * B₀) +
        j * j * j * (A₁ * B₂ + A₂ * B₁ + A₃ * B₀) + j * j * j * j * (A₂ * B₂ + A₃ * B₁) +
        j * j * j * j * j * (A₃ * B₂) := by
  grind

private theorem toom43_sum (A₀ A₁ A₂ A₃ B₀ B₁ B₂ x : Nat) :
    A₀ * B₀ + x * ((A₀ * B₁ + A₁ * B₀) + x * ((A₀ * B₂ + A₁ * B₁ + A₂ * B₀) +
      x * ((A₁ * B₂ + A₂ * B₁ + A₃ * B₀) + x * ((A₂ * B₂ + A₃ * B₁) + x * (A₃ * B₂))))) =
      (A₀ + x * A₁ + x * x * A₂ + x * x * x * A₃) * (B₀ + x * B₁ + x * x * B₂) := by
  grind

public theorem toom43At_spec (a b : UInt32Array.Slice) (k : Nat) (hk : 4 ≤ k)
    (hka : 3 * k ≤ a.size) (hkb : 2 * k ≤ b.size)
    (mulRec : (x y : UInt32Array.Slice) → x.size + y.size < a.size + b.size → UInt32Array)
    (hrec : ∀ x y h, (mulRec x y h).size = x.size + y.size ∧
      toNat (mulRec x y h) = toNat x * toNat y) :
    (toom43At a b k hk hka hkb mulRec).size = a.size + b.size ∧
      toNat (toom43At a b k hk hka hkb mulRec) = toNat a * toNat b := by
  have ha := toNat_slice_four a k hka
  have hb := toNat_slice_three b k hkb
  have hA := toNat_lt a
  have hB := toNat_lt b
  -- The six products.
  obtain ⟨-, hv₀⟩ := hrec (a.slice 0 k) (b.slice 0 k)
    (by simp only [UInt32Array.Slice.size_slice]; lia)
  obtain ⟨-, hv₅⟩ := hrec (a.slice (3 * k) a.size) (b.slice (2 * k) b.size)
    (by simp only [UInt32Array.Slice.size_slice]; lia)
  have hw : ∀ (v₁ v₂ v₃ : UInt32), 1 + v₁.toNat + v₂.toNat + v₃.toNat ≤ 2 ^ 32 → ∀ h,
      toNat (mulRec
        (eval4At (a.slice 0 k) (a.slice k (2 * k)) (a.slice (2 * k) (3 * k))
          (a.slice (3 * k) a.size) v₁ v₂ v₃)
        (eval3At (b.slice 0 k) (b.slice k (2 * k)) (b.slice (2 * k) b.size) v₁ v₂) h) =
      (toNat (a.slice 0 k) + toNat (a.slice k (2 * k)) * v₁.toNat +
          toNat (a.slice (2 * k) (3 * k)) * v₂.toNat + toNat (a.slice (3 * k) a.size) * v₃.toNat) *
        (toNat (b.slice 0 k) + toNat (b.slice k (2 * k)) * v₁.toNat +
          toNat (b.slice (2 * k) b.size) * v₂.toNat) :=
    fun v₁ v₂ v₃ hv h => by rw [(hrec _ _ h).2, toNat_eval4At _ _ _ _ _ _ _ hv,
      toNat_eval3At _ _ _ _ _ (by lia)]
  simp only [toom43At]
  generalize hW₁ : mulRec (eval4At (a.slice 0 k) _ _ _ 1 1 1) _ _ = w₁
  generalize hW₂ : mulRec (eval4At (a.slice 0 k) _ _ _ 2 4 8) _ _ = w₂
  generalize hW₃ : mulRec (eval4At (a.slice 0 k) _ _ _ 3 9 27) _ _ = w₃
  generalize hW₄ : mulRec (eval4At (a.slice 0 k) _ _ _ 4 16 64) _ _ = w₄
  have hw₁ := hW₁ ▸ hw 1 1 1 (by decide) _
  have hw₂ := hW₂ ▸ hw 2 4 8 (by decide) _
  have hw₃ := hW₃ ▸ hw 3 9 27 (by decide) _
  have hw₄ := hW₄ ▸ hw 4 16 64 (by decide) _
  simp only [UInt32.reduceToNat] at hw₁ hw₂ hw₃ hw₄
  clear hw hW₁ hW₂ hW₃ hW₄
  generalize mulRec (a.slice 0 k) _ _ = c₀ at *
  generalize mulRec (a.slice (3 * k) a.size) _ _ = c₅ at *
  generalize toNat (a.slice 0 k) = A₀ at *
  generalize toNat (a.slice k (2 * k)) = A₁ at *
  generalize toNat (a.slice (2 * k) (3 * k)) = A₂ at *
  generalize toNat (a.slice (3 * k) a.size) = A₃ at *
  generalize toNat (b.slice 0 k) = B₀ at *
  generalize toNat (b.slice k (2 * k)) = B₁ at *
  generalize toNat (b.slice (2 * k) b.size) = B₂ at *
  have hlt : toNat a * toNat b < 2 ^ (32 * (a.size + b.size)) := by
    rw [Nat.mul_add, Nat.pow_add]
    exact Nat.mul_lt_mul'' hA hB
  -- Interpolation recovers the middle coefficients.
  have hi := toom43Interp_spec c₀ w₁ w₂ w₃ w₄ c₅ (A₀ * B₀) (A₀ * B₁ + A₁ * B₀)
    (A₀ * B₂ + A₁ * B₁ + A₂ * B₀) (A₁ * B₂ + A₂ * B₁ + A₃ * B₀) (A₂ * B₂ + A₃ * B₁) (A₃ * B₂)
    hv₀ hv₅ (by rw [hw₁]; grind) (by rw [hw₂, toom43_w _ _ _ _ _ _ _ 2])
    (by rw [hw₃, toom43_w _ _ _ _ _ _ _ 3]) (by rw [hw₄, toom43_w _ _ _ _ _ _ _ 4])
  generalize toom43Interp c₀ w₁ w₂ w₃ w₄ c₅ = i at *
  obtain ⟨hi₁, hi₂, hi₃, hi₄⟩ := hi
  rw [ha, hb] at hlt ⊢
  have key := assemble_spec (a.size + b.size) k [c₀, i.1, i.2.1, i.2.2.1, i.2.2.2, c₅]
    _ (by simp; lia) (by simp only [List.map_cons, List.map_nil, hv₀, hi₁, hi₂, hi₃, hi₄, hv₅]; rfl)
    (by rw [polyVal6, toom43_sum]; exact hlt)
  rw [polyVal6, toom43_sum] at key
  exact key

/--
The product `a * b` by one step of Toom-4 by 3, for `32 ≤ b.size` and `a.size` between six fifths
and fifteen eighths of `b.size`: it splits at a quarter of `a` or a third of `b`, whichever is
longer.
-/
public def toom43 (a b : UInt32Array.Slice) (hb : 32 ≤ b.size) (h65 : 6 * b.size ≤ 5 * a.size)
    (h158 : 8 * a.size < 15 * b.size)
    (mulRec : (x y : UInt32Array.Slice) → x.size + y.size < a.size + b.size → UInt32Array) :
    UInt32Array :=
  toom43At a b (max ((a.size + 3) / 4) ((b.size + 2) / 3)) (by lia) (by lia) (by lia) mulRec

public theorem toom43_spec (a b : UInt32Array.Slice) (hb : 32 ≤ b.size)
    (h65 : 6 * b.size ≤ 5 * a.size) (h158 : 8 * a.size < 15 * b.size)
    (mulRec : (x y : UInt32Array.Slice) → x.size + y.size < a.size + b.size → UInt32Array)
    (hrec : ∀ x y h, (mulRec x y h).size = x.size + y.size ∧
      toNat (mulRec x y h) = toNat x * toNat y) :
    (toom43 a b hb h65 h158 mulRec).size = a.size + b.size ∧
      toNat (toom43 a b hb h65 h158 mulRec) = toNat a * toNat b :=
  toom43At_spec _ _ _ _ _ _ _ hrec

end MPN
