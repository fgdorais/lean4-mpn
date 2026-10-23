/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import MPN.FFT.Fermat
public import MPN.Sum

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

/-! ## Bit reversal -/

/-- The reversal of the `m` low bits of `p`, splitting at the top bit, as the transforms do. -/
@[expose] public def rev : Nat → Nat → Nat
  | 0, _ => 0
  | m + 1, p => if p < 2 ^ m then 2 * rev m p else 2 * rev m (p - 2 ^ m) + 1

public theorem rev_lt (m p : Nat) : rev m p < 2 ^ m := by
  induction m generalizing p with
  | zero => simp [rev]
  | succ m ih =>
    rw [rev, Nat.pow_succ]
    have := ih p; have := ih (p - 2 ^ m)
    split <;> lia

public theorem rev_succ_lo (m p : Nat) (hp : p < 2 ^ m) : rev (m + 1) p = 2 * rev m p := by
  simp only [rev, hp, ↓reduceIte]

public theorem rev_succ_hi (m p : Nat) : rev (m + 1) (2 ^ m + p) = 2 * rev m p + 1 := by
  simp only [rev, show ¬2 ^ m + p < 2 ^ m by lia, ↓reduceIte, Nat.add_sub_cancel_left]

/-- `rev` permutes `0, …, 2ᵐ - 1`, so it does not change sums over them. -/
public theorem sumRange_rev (f : Nat → Nat) (m : Nat) :
    sumRange (fun p => f (rev m p)) (2 ^ m) = sumRange f (2 ^ m) := by
  induction m generalizing f with
  | zero => simp [rev, sumRange]
  | succ m ih =>
    have h2 : 2 ^ (m + 1) = 2 ^ m + 2 ^ m := by rw [Nat.pow_succ]; lia
    have e₁ : sumRange (fun p => f (rev (m + 1) p)) (2 ^ m) =
        sumRange (fun p => f (2 * rev m p)) (2 ^ m) :=
      sumRange_congr fun p hp => by rw [rev_succ_lo m p hp]
    have e₂ : sumRange (fun p => f (rev (m + 1) (2 ^ m + p))) (2 ^ m) =
        sumRange (fun p => f (2 * rev m p + 1)) (2 ^ m) :=
      sumRange_congr fun p hp => by rw [rev_succ_hi m p]
    rw [h2, sumRange_append, e₁, e₂, ih (fun q => f (2 * q)), ih (fun q => f (2 * q + 1)),
      ← sumRange_add]
    -- The evens and the odds.
    clear ih h2 e₁ e₂
    generalize 2 ^ m = h
    induction h with
    | zero => rfl
    | succ h ih =>
      rw [sumRange_succ, ih, show h + 1 + (h + 1) = h + h + 1 + 1 by lia, sumRange_succ,
        sumRange_succ, show h + h = 2 * h by lia]
      lia

/-! ## Congruences -/

/-- Congruence modulo `F`. -/
public abbrev MEq (F a b : Nat) : Prop := a % F = b % F

public theorem MEq.refl (F a : Nat) : MEq F a a := rfl

public theorem MEq.symm {F a b : Nat} (h : MEq F a b) : MEq F b a := Eq.symm h

public theorem MEq.trans {F a b c : Nat} (h₁ : MEq F a b) (h₂ : MEq F b c) : MEq F a c :=
  Eq.trans h₁ h₂

public instance (F : Nat) : Trans (MEq F) (MEq F) (MEq F) := ⟨MEq.trans⟩

public theorem MEq.add {F a b c d : Nat} (h₁ : MEq F a b) (h₂ : MEq F c d) :
    MEq F (a + c) (b + d) := by
  unfold MEq at *; rw [Nat.add_mod, h₁, h₂, ← Nat.add_mod]

public theorem MEq.mul {F a b c d : Nat} (h₁ : MEq F a b) (h₂ : MEq F c d) :
    MEq F (a * c) (b * d) := by
  unfold MEq at *; rw [Nat.mul_mod, h₁, h₂, ← Nat.mul_mod]

public theorem MEq.mod (F a : Nat) : MEq F (a % F) a := Nat.mod_mod _ _

public theorem MEq.sum {F n : Nat} {f g : Nat → Nat} (h : ∀ i < n, MEq F (f i) (g i)) :
    MEq F (sumRange f n) (sumRange g n) := sumRange_mod h

public theorem MEq.of_eq {F a b : Nat} (h : a = b) : MEq F a b := by rw [h]

section
variable {N F : Nat} (hF : F = 2 ^ N + 1)
include hF

/-- `2^(2 N) ≡ 1`. -/
public theorem pow_two_N : MEq F (2 ^ (2 * N)) 1 := by
  have := sq_of_neg_one (y := 2 ^ N) (F := F) (by rw [hF]; simp)
  rw [← Nat.pow_add, show N + N = 2 * N by lia] at this
  exact this

/-- Powers of two modulo `F` have period `2 N`. -/
public theorem pow_period (a q : Nat) : MEq F (2 ^ (a + 2 * N * q)) (2 ^ a) := by
  rw [Nat.pow_add, Nat.pow_mul]
  have : MEq F ((2 ^ (2 * N)) ^ q) 1 := by
    unfold MEq; rw [Nat.pow_mod, pow_two_N hF, ← Nat.pow_mod, Nat.one_pow]
  have := MEq.mul (MEq.refl F (2 ^ a)) this
  rwa [Nat.mul_one] at this

/-- `-y ≡ 2ᴺ y`. -/
public theorem neg_eq (x y : Nat) (hy : y ≤ F) : MEq F (x + F - y) (x + y * 2 ^ N) := by
  unfold MEq
  have e : x + F - y + F * y = x + y * 2 ^ N + F := by rw [hF]; grind
  have := congrArg (· % F) e
  simp only [Nat.add_mul_mod_self_left, Nat.add_mod_right] at this
  exact this

/-- `2ᴺ 2ᴺ ≡ 1`, as a congruence of products. -/
public theorem pow_N_pow_N (x : Nat) : MEq F (x * 2 ^ N * 2 ^ N) x := by
  have := MEq.mul (MEq.refl F x) (pow_two_N hF)
  rw [Nat.mul_one, Nat.two_mul, Nat.pow_add, ← Nat.mul_assoc] at this
  exact this

/-! ### The forward step -/

/-- The first half after the butterflies, transformed by `2^(2 σ)`: the even outputs. -/
public theorem fwd_even (x : Nat → Nat) (σ h r : Nat) (hσ : σ * h = N) :
    MEq F (sumRange (fun i => (x i + x (h + i)) % F * 2 ^ (2 * σ * i * r)) h)
      (sumRange (fun i => x i * 2 ^ (σ * i * (2 * r))) (h + h)) := by
  rw [sumRange_append, ← sumRange_add]
  refine MEq.sum fun i _ => ?_
  have e₁ : σ * (h + i) * (2 * r) = σ * i * (2 * r) + 2 * N * r := by rw [← hσ]; grind
  have e₂ : 2 * σ * i * r = σ * i * (2 * r) := by grind
  rw [e₁, e₂]
  calc (x i + x (h + i)) % F * 2 ^ (σ * i * (2 * r))
      MEq F _ ((x i + x (h + i)) * 2 ^ (σ * i * (2 * r))) := MEq.mul (MEq.mod _ _) (MEq.refl _ _)
      _ = x i * 2 ^ (σ * i * (2 * r)) + x (h + i) * 2 ^ (σ * i * (2 * r)) := Nat.add_mul ..
      MEq F _ (x i * 2 ^ (σ * i * (2 * r)) + x (h + i) * 2 ^ (σ * i * (2 * r) + 2 * N * r)) :=
        MEq.add (MEq.refl _ _) (MEq.mul (MEq.refl _ _) (pow_period hF _ _).symm)

/-- The second half after the butterflies, transformed by `2^(2 σ)`: the odd outputs. -/
public theorem fwd_odd (x : Nat → Nat) (σ h r : Nat) (hσ : σ * h = N)
    (hx : ∀ i < h, x (h + i) ≤ F) :
    MEq F (sumRange (fun i => (x i + F - x (h + i)) % F * 2 ^ (σ * i) % F * 2 ^ (2 * σ * i * r)) h)
      (sumRange (fun i => x i * 2 ^ (σ * i * (2 * r + 1))) (h + h)) := by
  rw [sumRange_append, ← sumRange_add]
  refine MEq.sum fun i hi => ?_
  have e₁ : σ * (h + i) * (2 * r + 1) = σ * i * (2 * r + 1) + N + 2 * N * r := by
    rw [← hσ]; grind
  have e₂ : 2 ^ (σ * i) * 2 ^ (2 * σ * i * r) = 2 ^ (σ * i * (2 * r + 1)) := by
    rw [← Nat.pow_add]; congr 1; grind
  rw [e₁]
  calc (x i + F - x (h + i)) % F * 2 ^ (σ * i) % F * 2 ^ (2 * σ * i * r)
      MEq F _ ((x i + F - x (h + i)) * 2 ^ (σ * i) * 2 ^ (2 * σ * i * r)) :=
        MEq.mul ((MEq.mod _ _).trans (MEq.mul (MEq.mod _ _) (MEq.refl _ _))) (MEq.refl _ _)
      _ = (x i + F - x (h + i)) * 2 ^ (σ * i * (2 * r + 1)) := by rw [Nat.mul_assoc, e₂]
      MEq F _ ((x i + x (h + i) * 2 ^ N) * 2 ^ (σ * i * (2 * r + 1))) :=
        MEq.mul (neg_eq hF _ _ (hx i hi)) (MEq.refl _ _)
      _ = x i * 2 ^ (σ * i * (2 * r + 1)) + x (h + i) * 2 ^ (σ * i * (2 * r + 1) + N) := by
        rw [Nat.add_mul, Nat.pow_add]; grind
      MEq F _ (x i * 2 ^ (σ * i * (2 * r + 1)) +
          x (h + i) * 2 ^ (σ * i * (2 * r + 1) + N + 2 * N * r)) :=
        MEq.add (MEq.refl _ _) (MEq.mul (MEq.refl _ _) (pow_period hF _ _).symm)

/-! ### The inverse step -/

/--
The outputs `l` of the inverse step, from the transforms `A`, `B` of the two halves by
`2^(2 N - 2 σ)` at `l`: `A + B 2^((2 N - σ) l)`.
-/
public theorem inv_lo (u ρ : Nat → Nat) (σ τ τ' h l : Nat) (hτ : τ + σ = 2 * N)
    (hτ' : τ' + 2 * σ = 2 * N) :
    MEq F (sumRange (fun p => u p * 2 ^ (τ * (2 * ρ p) * l)) h +
        sumRange (fun p => u (h + p) * 2 ^ (τ * (2 * ρ p + 1) * l)) h)
      (sumRange (fun p => u p * 2 ^ (τ' * ρ p * l)) h +
        sumRange (fun p => u (h + p) * 2 ^ (τ' * ρ p * l)) h * 2 ^ (τ * l)) := by
  rw [sumRange_mul_right]
  refine MEq.add (MEq.sum fun p _ => ?_) (MEq.sum fun p _ => ?_)
  · have e : τ * (2 * ρ p) * l = τ' * ρ p * l + 2 * N * (ρ p * l) := by
      have : 2 * τ = τ' + 2 * N := by lia
      grind
    rw [e]
    exact MEq.mul (MEq.refl _ _) (pow_period hF _ _)
  · have e : τ * (2 * ρ p + 1) * l = τ' * ρ p * l + τ * l + 2 * N * (ρ p * l) := by
      have : 2 * τ = τ' + 2 * N := by lia
      grind
    rw [e]
    refine (MEq.mul (MEq.refl _ _) (pow_period hF _ _)).trans (MEq.of_eq ?_)
    simp only [Nat.pow_add, Nat.mul_assoc]

/-- The outputs `h + l` of the inverse step: `A + B 2^((2 N - σ) l) 2ᴺ`. -/
public theorem inv_hi (u ρ : Nat → Nat) (σ τ τ' h l : Nat) (hτ : τ + σ = 2 * N)
    (hτ' : τ' + 2 * σ = 2 * N) (hσ : σ * h = N) (hh : 1 ≤ h) :
    MEq F (sumRange (fun p => u p * 2 ^ (τ * (2 * ρ p) * (h + l))) h +
        sumRange (fun p => u (h + p) * 2 ^ (τ * (2 * ρ p + 1) * (h + l))) h)
      (sumRange (fun p => u p * 2 ^ (τ' * ρ p * l)) h +
        sumRange (fun p => u (h + p) * 2 ^ (τ' * ρ p * l)) h * 2 ^ (τ * l) * 2 ^ N) := by
  rw [Nat.mul_assoc, sumRange_mul_right]
  obtain ⟨h₁, rfl⟩ : ∃ h₁, h = h₁ + 1 := ⟨h - 1, by lia⟩
  have h2τ : 2 * τ = τ' + 2 * N := by lia
  have hτ'h : τ' * (h₁ + 1) = 2 * N * h₁ := by
    have : τ' * (h₁ + 1) + 2 * σ * (h₁ + 1) = 2 * N * (h₁ + 1) := by rw [← Nat.add_mul, hτ']
    grind
  have hτh : τ * (h₁ + 1) = N + 2 * N * h₁ := by
    have : τ * (h₁ + 1) + σ * (h₁ + 1) = 2 * N * (h₁ + 1) := by rw [← Nat.add_mul, hτ]
    grind
  refine MEq.add (MEq.sum fun p _ => ?_) (MEq.sum fun p _ => ?_)
  · have e : τ * (2 * ρ p) * (h₁ + 1 + l) =
        τ' * ρ p * l + 2 * N * (ρ p * h₁ + ρ p * (h₁ + 1 + l)) := by grind
    rw [e]
    exact MEq.mul (MEq.refl _ _) (pow_period hF _ _)
  · have e : τ * (2 * ρ p + 1) * (h₁ + 1 + l) = τ' * ρ p * l + (τ * l + N) +
        2 * N * (ρ p * h₁ + ρ p * (h₁ + 1 + l) + h₁) := by grind
    rw [e]
    refine (MEq.mul (MEq.refl _ _) (pow_period hF _ _)).trans (MEq.of_eq ?_)
    simp only [Nat.pow_add, Nat.mul_assoc]

end

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

/-! ## Butterflies -/

/-- The forward butterfly: `(x, y) ↦ (x + y, (x - y) 2ᵉ)`, through the scratch window `t`. -/
public def fwdBfly (arr : UInt64Array) (n x y t e : Nat) : UInt64Array :=
  mulPow2G (addModG (subModG arr n t x y) n x x y) n y t e

/-- Three disjoint windows of `n + 1` limbs within an array whose indices do not overflow. -/
public abbrev Three (arr : UInt64Array) (n x y t : Nat) : Prop :=
  arr.size < USize.size ∧ x + n + 1 ≤ arr.size ∧ y + n + 1 ≤ arr.size ∧ t + n + 1 ≤ arr.size ∧
    (x + n + 1 ≤ y ∨ y + n + 1 ≤ x) ∧ (x + n + 1 ≤ t ∨ t + n + 1 ≤ x) ∧
    (y + n + 1 ≤ t ∨ t + n + 1 ≤ y)

public theorem fwdBfly_spec (arr : UInt64Array) (n x y t e : Nat) (h : Three arr n x y t)
    (hn : 1 ≤ n) (he : e < 64 * n) (heS : e < USize.size)
    (hX : win arr n x < fermat n) (hY : win arr n y < fermat n) :
    (fwdBfly arr n x y t e).size = arr.size ∧
      (∀ i, (i < x ∨ x + n + 1 ≤ i) → (i < y ∨ y + n + 1 ≤ i) → (i < t ∨ t + n + 1 ≤ i) →
        (fwdBfly arr n x y t e)[i]! = arr[i]!) ∧
      win (fwdBfly arr n x y t e) n x = (win arr n x + win arr n y) % fermat n ∧
      win (fwdBfly arr n x y t e) n y =
        (win arr n x + fermat n - win arr n y) % fermat n * 2 ^ e % fermat n := by
  obtain ⟨hS, hx, hy, ht, hxy, hxt, hyt⟩ := h
  have hF : 0 < fermat n := by simp [fermat]
  rw [fwdBfly]
  obtain ⟨s₁, u₁, v₁⟩ := subModG_spec arr n t x y hS ht hx hy hn (by lia) (by lia) hX hY
  generalize subModG arr n t x y = a₁ at *
  have x₁ := win_of_untouched u₁ (o := x) (by lia)
  have y₁ := win_of_untouched u₁ (o := y) (by lia)
  obtain ⟨s₂, u₂, v₂⟩ := addModG_spec a₁ n x x y (by lia) (by lia) (by lia) (by lia) hn
    (by lia) (by lia) (by rw [x₁]; exact hX) (by rw [y₁]; exact hY)
  generalize addModG a₁ n x x y = a₂ at *
  have t₂ := win_of_untouched u₂ (o := t) (by lia)
  have y₂ := win_of_untouched u₂ (o := y) (by lia)
  obtain ⟨s₃, u₃, v₃⟩ := mulPow2G_spec a₂ n y t e (by lia) (by lia) (by lia) hn he heS (by lia)
    (by rw [t₂, v₁]; exact Nat.mod_lt _ hF)
  generalize mulPow2G a₂ n y t e = a₃ at *
  have x₃ := win_of_untouched u₃ (o := x) (by lia)
  refine ⟨by rw [s₃, s₂, s₁], fun i h₁ h₂ h₃ => by rw [u₃ i h₂, u₂ i h₁, u₁ i h₃], ?_, ?_⟩
  · rw [x₃, v₂, x₁, y₁]
  · rw [v₃, t₂, v₁]

/--
The inverse butterfly: `(x, y) ↦ (x + y, x - y)` for `j = 0`, and otherwise
`(x - y 2ᵉ, x + y 2ᵉ)`, with `2ᵉ ≡ -2^(-σ j)`, through the scratch window `t`.
-/
public def invBfly (arr : UInt64Array) (n x y t e : Nat) (first : Bool) : UInt64Array :=
  if first then addModG (subModG (mulPow2G arr n t y 0) n y x t) n x x t
  else subModG (addModG (mulPow2G arr n t y e) n y x t) n x x t

public theorem invBfly_spec (arr : UInt64Array) (n x y t e : Nat) (first : Bool)
    (h : Three arr n x y t) (hn : 1 ≤ n) (he : e < 64 * n) (heS : e < USize.size)
    (hX : win arr n x < fermat n) (hY : win arr n y < fermat n) :
    (invBfly arr n x y t e first).size = arr.size ∧
      (∀ i, (i < x ∨ x + n + 1 ≤ i) → (i < y ∨ y + n + 1 ≤ i) → (i < t ∨ t + n + 1 ≤ i) →
        (invBfly arr n x y t e first)[i]! = arr[i]!) ∧
      win (invBfly arr n x y t e first) n x =
        (if first then (win arr n x + win arr n y) % fermat n
        else (win arr n x + fermat n - win arr n y * 2 ^ e % fermat n) % fermat n) ∧
      win (invBfly arr n x y t e first) n y =
        (if first then (win arr n x + fermat n - win arr n y) % fermat n
        else (win arr n x + win arr n y * 2 ^ e % fermat n) % fermat n) := by
  obtain ⟨hS, hx, hy, ht, hxy, hxt, hyt⟩ := h
  have hF : 0 < fermat n := by simp [fermat]
  have hY' : win arr n y % fermat n = win arr n y := Nat.mod_eq_of_lt hY
  have e0 : 0 < 64 * n := by lia
  obtain ⟨s₁, u₁, v₁⟩ := mulPow2G_spec arr n t y (if first then 0 else e) hS ht hy hn
    (by split <;> lia) (by split <;> lia) (by lia) hY
  have hsplit : invBfly arr n x y t e first = if first
      then addModG (subModG (mulPow2G arr n t y (if first then 0 else e)) n y x t) n x x t
      else subModG (addModG (mulPow2G arr n t y (if first then 0 else e)) n y x t) n x x t := by
    rw [invBfly]; split <;> simp_all
  rw [hsplit]
  generalize mulPow2G arr n t y (if first then 0 else e) = a₁ at *
  have x₁ := win_of_untouched u₁ (o := x) (by lia)
  have hT : win a₁ n t < fermat n := by rw [v₁]; exact Nat.mod_lt _ hF
  cases first with
  | true =>
    simp only [↓reduceIte, Nat.pow_zero, Nat.mul_one, hY'] at v₁ ⊢
    obtain ⟨s₂, u₂, v₂⟩ := subModG_spec a₁ n y x t (by lia) (by lia) (by lia) (by lia) hn
      (by lia) (by lia) (by rw [x₁]; exact hX) hT
    generalize subModG a₁ n y x t = a₂ at *
    have x₂ := win_of_untouched u₂ (o := x) (by lia)
    have t₂ := win_of_untouched u₂ (o := t) (by lia)
    obtain ⟨s₃, u₃, v₃⟩ := addModG_spec a₂ n x x t (by lia) (by lia) (by lia) (by lia) hn
      (by lia) (by lia) (by rw [x₂, x₁]; exact hX) (by rw [t₂]; exact hT)
    generalize addModG a₂ n x x t = a₃ at *
    have y₃ := win_of_untouched u₃ (o := y) (by lia)
    refine ⟨by rw [s₃, s₂, s₁], fun i h₁ h₂ h₃ => by rw [u₃ i h₁, u₂ i h₂, u₁ i h₃], ?_, ?_⟩
    · rw [v₃, x₂, x₁, t₂, v₁]
    · rw [y₃, v₂, x₁, v₁]
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte] at v₁ ⊢
    obtain ⟨s₂, u₂, v₂⟩ := addModG_spec a₁ n y x t (by lia) (by lia) (by lia) (by lia) hn
      (by lia) (by lia) (by rw [x₁]; exact hX) hT
    generalize addModG a₁ n y x t = a₂ at *
    have x₂ := win_of_untouched u₂ (o := x) (by lia)
    have t₂ := win_of_untouched u₂ (o := t) (by lia)
    obtain ⟨s₃, u₃, v₃⟩ := subModG_spec a₂ n x x t (by lia) (by lia) (by lia) (by lia) hn
      (by lia) (by lia) (by rw [x₂, x₁]; exact hX) (by rw [t₂]; exact hT)
    generalize subModG a₂ n x x t = a₃ at *
    have y₃ := win_of_untouched u₃ (o := y) (by lia)
    refine ⟨by rw [s₃, s₂, s₁], fun i h₁ h₂ h₃ => by rw [u₃ i h₁, u₂ i h₂, u₁ i h₃], ?_, ?_⟩
    · rw [v₃, x₂, x₁, t₂, v₁]
    · rw [y₃, v₂, x₁, v₁]

/-! ## Blocks of windows -/

/-- The value of window `p` of the block at `o`, the windows of `n + 1` limbs one after another. -/
public abbrev coef (arr : UInt64Array) (n o p : Nat) : Nat := win arr n (o + p * (n + 1))

private theorem step_le {p q w : Nat} (h : p + 1 ≤ q) : p * w + w ≤ q * w := by
  have := Nat.mul_le_mul_right w h
  rw [Nat.add_mul, Nat.one_mul] at this
  exact this

/-- Distinct windows of a block are disjoint. -/
private theorem win_disj (o n p q : Nat) (h : p ≠ q) :
    o + p * (n + 1) + n + 1 ≤ o + q * (n + 1) ∨ o + q * (n + 1) + n + 1 ≤ o + p * (n + 1) := by
  rcases Nat.lt_or_gt_of_ne h with h | h
  · have := step_le (w := n + 1) h; lia
  · have := step_le (w := n + 1) h; lia

/-- A window of a block of `L` windows is within it. -/
private theorem win_in (o n p L : Nat) (h : p < L) : o + p * (n + 1) + n + 1 ≤ o + L * (n + 1) := by
  have := step_le (w := n + 1) h; lia

/-- The butterflies of the forward transform, from `j` on, `cnt` of them. -/
public def fwdLoop (n o h σ t : Nat) : UInt64Array → Nat → Nat → UInt64Array
  | arr, _, 0 => arr
  | arr, j, cnt + 1 =>
    fwdLoop n o h σ t (fwdBfly arr n (o + j * (n + 1)) (o + (h + j) * (n + 1)) t (σ * j)) (j + 1)
      cnt

/-- The bounds of a block of `L` windows at `o` and of a scratch window at `t`, disjoint from it. -/
public abbrev Block (arr : UInt64Array) (n o L t : Nat) : Prop :=
  arr.size < USize.size ∧ o + L * (n + 1) ≤ arr.size ∧ t + n + 1 ≤ arr.size ∧
    (t + n + 1 ≤ o ∨ o + L * (n + 1) ≤ t)

set_option maxHeartbeats 400000 in
public theorem fwdLoop_spec (n o h σ t : Nat) (hn : 1 ≤ n) (hσ : σ * h = 64 * n)
    (h64 : 64 * n < USize.size) (cnt : Nat) :
    ∀ arr j, j + cnt = h → Block arr n o (h + h) t →
      (∀ p < h + h, coef arr n o p < fermat n) →
      (fwdLoop n o h σ t arr j cnt).size = arr.size ∧
      (∀ i, (i < o ∨ o + (h + h) * (n + 1) ≤ i) → (i < t ∨ t + n + 1 ≤ i) →
        (fwdLoop n o h σ t arr j cnt)[i]! = arr[i]!) ∧
      (∀ p < h + h, (p < j ∨ (h ≤ p ∧ p < h + j)) →
        coef (fwdLoop n o h σ t arr j cnt) n o p = coef arr n o p) ∧
      (∀ p, j ≤ p → p < h →
        coef (fwdLoop n o h σ t arr j cnt) n o p =
            (coef arr n o p + coef arr n o (h + p)) % fermat n ∧
          coef (fwdLoop n o h σ t arr j cnt) n o (h + p) =
            (coef arr n o p + fermat n - coef arr n o (h + p)) % fermat n * 2 ^ (σ * p) %
              fermat n) := by
  induction cnt with
  | zero =>
    intro arr j hj _ _
    refine ⟨rfl, fun _ _ _ => rfl, fun _ _ _ => rfl, fun p h₁ h₂ => absurd h₂ (by lia)⟩
  | succ cnt ih =>
    intro arr j hj hb hv
    obtain ⟨hS, hB, ht, htd⟩ := hb
    have hF : 0 < fermat n := by simp [fermat]
    have hjh : j < h := by lia
    have hxy := step_le (w := n + 1) (show j + 1 ≤ h + j by lia)
    have hyB := win_in o n (h + j) (h + h) (by lia)
    have hσ₀ : 0 < σ := by
      rcases Nat.eq_zero_or_pos σ with e | e
      · rw [e, Nat.zero_mul] at hσ; lia
      · exact e
    have he : σ * j < 64 * n := by rw [← hσ]; exact Nat.mul_lt_mul_of_pos_left hjh hσ₀
    obtain ⟨b₁, b₂, b₃, b₄⟩ := fwdBfly_spec arr n (o + j * (n + 1)) (o + (h + j) * (n + 1)) t
      (σ * j) ⟨hS, by lia, by lia, ht, by lia, by lia, by lia⟩ hn he (by lia)
      (hv j (by lia)) (hv (h + j) (by lia))
    rw [fwdLoop]
    generalize fwdBfly arr n (o + j * (n + 1)) (o + (h + j) * (n + 1)) t (σ * j) = a₁ at *
    have hc : ∀ p < h + h, p ≠ j → p ≠ h + j → coef a₁ n o p = coef arr n o p := by
      intro p hp h₁ h₂
      have d₁ := win_disj o n p j h₁
      have d₂ := win_disj o n p (h + j) h₂
      have d₃ := win_in o n p (h + h) hp
      exact UInt64Array.valAt_congr _ fun i _ _ => b₂ i (by lia) (by lia) (by lia)
    have hv₁ : ∀ p < h + h, coef a₁ n o p < fermat n := by
      intro p hp
      by_cases e₁ : p = j
      · subst e₁; show win a₁ n _ < _; rw [b₃]; exact Nat.mod_lt _ hF
      by_cases e₂ : p = h + j
      · subst e₂; show win a₁ n _ < _; rw [b₄]; exact Nat.mod_lt _ hF
      rw [hc p hp e₁ e₂]; exact hv p hp
    obtain ⟨i₁, i₂, i₃, i₄⟩ := ih a₁ (j + 1) (by lia) ⟨by lia, by lia, by lia, htd⟩ hv₁
    refine ⟨i₁.trans b₁, fun i h₁ h₂ => ?_, fun p hp hpj => ?_, fun p h₁ h₂ => ?_⟩
    · have d₃ := win_in o n j (h + h) (by lia)
      rw [i₂ i h₁ h₂, b₂ i (by lia) (by lia) h₂]
    · rw [i₃ p hp (by lia), hc p hp (by lia) (by lia)]
    · by_cases e : p = j
      · subst e
        rw [i₃ p (by lia) (by lia), i₃ (h + p) (by lia) (by lia)]
        exact ⟨b₃, b₄⟩
      · obtain ⟨k₁, k₂⟩ := i₄ p (by lia) h₂
        have c₁ := hc p (by lia) e (by lia)
        have c₂ := hc (h + p) (by lia) (by lia) (by lia)
        rw [c₁, c₂] at k₁ k₂
        exact ⟨k₁, k₂⟩

/-! ## The forward transform -/

/--
The forward transform of the block of `2ᵐ` windows at `o`, with the root `2^σ`: the butterflies
of the two halves, then the transforms of each half with the root `2^(2 σ)`.
-/
public def fwd (n t : Nat) : Nat → UInt64Array → Nat → Nat → UInt64Array
  | 0, arr, _, _ => arr
  | m + 1, arr, o, σ =>
    let a := fwdLoop n o (2 ^ m) σ t arr 0 (2 ^ m)
    let a := fwd n t m a o (2 * σ)
    fwd n t m a (o + 2 ^ m * (n + 1)) (2 * σ)

public theorem fwd_spec (n t : Nat) (hn : 1 ≤ n) (h64 : 64 * n < USize.size) (m : Nat) :
    ∀ arr o σ, σ * 2 ^ m = 2 * (64 * n) → Block arr n o (2 ^ m) t →
      (∀ p < 2 ^ m, coef arr n o p < fermat n) →
      (fwd n t m arr o σ).size = arr.size ∧
      (∀ i, (i < o ∨ o + 2 ^ m * (n + 1) ≤ i) → (i < t ∨ t + n + 1 ≤ i) →
        (fwd n t m arr o σ)[i]! = arr[i]!) ∧
      (∀ p < 2 ^ m, coef (fwd n t m arr o σ) n o p =
        sumRange (fun i => coef arr n o i * 2 ^ (σ * i * rev m p)) (2 ^ m) % fermat n) := by
  induction m with
  | zero =>
    intro arr o σ _ _ hv
    refine ⟨rfl, fun _ _ _ => rfl, fun p hp => ?_⟩
    simp only [Nat.pow_zero] at hp
    have : p = 0 := by lia
    subst this
    simp only [fwd, sumRange, Nat.mul_zero, Nat.zero_mul, Nat.pow_zero, Nat.mul_one, Nat.zero_add]
    exact (Nat.mod_eq_of_lt (hv 0 (by simp))).symm
  | succ m ih =>
    intro arr o σ hσ hb hv
    obtain ⟨hS, hB, ht, htd⟩ := hb
    have hF : 0 < fermat n := by simp [fermat]
    have h2 : 2 ^ (m + 1) = 2 ^ m + 2 ^ m := by rw [Nat.pow_succ]; lia
    rw [h2] at hB htd hv ⊢
    have hσ' : σ * 2 ^ m = 64 * n := by rw [h2] at hσ; lia
    simp only [fwd]
    -- The butterflies.
    obtain ⟨l₁, l₂, -, l₄⟩ := fwdLoop_spec n o (2 ^ m) σ t hn hσ' h64 (2 ^ m) arr 0 (by lia)
      ⟨hS, hB, ht, htd⟩ hv
    generalize fwdLoop n o (2 ^ m) σ t arr 0 (2 ^ m) = a₁ at *
    have hv₁ : ∀ p < 2 ^ m + 2 ^ m, coef a₁ n o p < fermat n := by
      intro p hp
      rcases Nat.lt_or_ge p (2 ^ m) with e | e
      · rw [(l₄ p (by lia) e).1]; exact Nat.mod_lt _ hF
      · obtain ⟨p', rfl⟩ : ∃ p', p = 2 ^ m + p' := ⟨p - 2 ^ m, by lia⟩
        rw [(l₄ p' (by lia) (by lia)).2]; exact Nat.mod_lt _ hF
    -- The first half.
    have hmid := Nat.mul_le_mul_right (n + 1) (show 2 ^ m ≤ 2 ^ m + 2 ^ m by lia)
    obtain ⟨f₁, f₂, f₃⟩ := ih a₁ o (2 * σ) (by rw [Nat.mul_assoc, hσ']) ⟨by lia, by lia, by lia,
      by lia⟩ (fun p hp => hv₁ p (by lia))
    generalize fwd n t m a₁ o (2 * σ) = a₂ at *
    -- The second half.
    have hoff : ∀ p, o + 2 ^ m * (n + 1) + p * (n + 1) = o + (2 ^ m + p) * (n + 1) := by
      intro p; rw [Nat.add_mul]; lia
    have hv₂ : ∀ p < 2 ^ m, coef a₂ n (o + 2 ^ m * (n + 1)) p < fermat n := by
      intro p hp
      have d := win_in o n (2 ^ m + p) (2 ^ m + 2 ^ m) (by lia)
      show win a₂ n _ < _
      rw [hoff, win_congr fun i _ _ => f₂ i (by lia) (by lia)]
      exact hv₁ _ (by lia)
    obtain ⟨g₁, g₂, g₃⟩ := ih a₂ (o + 2 ^ m * (n + 1)) (2 * σ) (by rw [Nat.mul_assoc, hσ'])
      ⟨by lia, by lia, by lia, by lia⟩ hv₂
    generalize fwd n t m a₂ (o + 2 ^ m * (n + 1)) (2 * σ) = a₃ at *
    refine ⟨by rw [g₁, f₁, l₁], fun i h₁ h₂ => ?_, fun p hp => ?_⟩
    · rw [g₂ i (by lia) h₂, f₂ i (by lia) h₂, l₂ i h₁ h₂]
    · rcases Nat.lt_or_ge p (2 ^ m) with e | e
      · -- An even output, from the first half.
        have d := win_in o n p (2 ^ m) e
        show win a₃ n _ = _
        rw [win_congr fun i _ _ => g₂ i (by lia) (by lia)]
        show coef a₂ n o p = _
        rw [f₃ p e, rev_succ_lo m p e]
        rw [sumRange_congr (g := fun i => (coef arr n o i + coef arr n o (2 ^ m + i)) % fermat n *
          2 ^ (2 * σ * i * rev m p)) fun i hi => by rw [(l₄ i (by lia) hi).1]]
        exact fwd_even rfl _ σ (2 ^ m) (rev m p) hσ'
      · -- An odd output, from the second half.
        obtain ⟨p', rfl⟩ : ∃ p', p = 2 ^ m + p' := ⟨p - 2 ^ m, by lia⟩
        show win a₃ n _ = _
        rw [← hoff]
        show coef a₃ n (o + 2 ^ m * (n + 1)) p' = _
        rw [g₃ p' (by lia), rev_succ_hi m p']
        rw [sumRange_congr (g := fun i => (coef arr n o i + fermat n - coef arr n o (2 ^ m + i)) %
          fermat n * 2 ^ (σ * i) % fermat n * 2 ^ (2 * σ * i * rev m p')) fun i hi => by
            have d := win_in o n (2 ^ m + i) (2 ^ m + 2 ^ m) (by lia)
            show win a₂ n _ * _ = _
            rw [hoff, win_congr fun k _ _ => f₂ k (by lia) (by lia)]
            show coef a₁ n o (2 ^ m + i) * _ = _
            rw [(l₄ i (by lia) hi).2]]
        exact fwd_odd rfl _ σ (2 ^ m) (rev m p') hσ' fun i hi => Nat.le_of_lt (hv _ (by lia))

/-! ## The inverse transform -/

/-- The butterflies of the inverse transform, from `j` on, `cnt` of them. -/
public def invLoop (n o h σ t : Nat) : UInt64Array → Nat → Nat → UInt64Array
  | arr, _, 0 => arr
  | arr, j, cnt + 1 =>
    invLoop n o h σ t (invBfly arr n (o + j * (n + 1)) (o + (h + j) * (n + 1)) t
      (if j = 0 then 0 else 64 * n - σ * j) (j == 0)) (j + 1) cnt

set_option maxHeartbeats 400000 in
public theorem invLoop_spec (n o h σ t : Nat) (hn : 1 ≤ n) (hσ : σ * h = 64 * n)
    (h64 : 64 * n < USize.size) (cnt : Nat) :
    ∀ arr j, j + cnt = h → Block arr n o (h + h) t →
      (∀ p < h + h, coef arr n o p < fermat n) →
      (invLoop n o h σ t arr j cnt).size = arr.size ∧
      (∀ i, (i < o ∨ o + (h + h) * (n + 1) ≤ i) → (i < t ∨ t + n + 1 ≤ i) →
        (invLoop n o h σ t arr j cnt)[i]! = arr[i]!) ∧
      (∀ p < h + h, (p < j ∨ (h ≤ p ∧ p < h + j)) →
        coef (invLoop n o h σ t arr j cnt) n o p = coef arr n o p) ∧
      (∀ p, j ≤ p → p < h →
        coef (invLoop n o h σ t arr j cnt) n o p =
            (if (p == 0) = true then (coef arr n o p + coef arr n o (h + p)) % fermat n
            else (coef arr n o p + fermat n -
              coef arr n o (h + p) * 2 ^ (if p = 0 then 0 else 64 * n - σ * p) % fermat n) %
                fermat n) ∧
          coef (invLoop n o h σ t arr j cnt) n o (h + p) =
            (if (p == 0) = true then (coef arr n o p + fermat n - coef arr n o (h + p)) % fermat n
            else (coef arr n o p +
              coef arr n o (h + p) * 2 ^ (if p = 0 then 0 else 64 * n - σ * p) % fermat n) %
                fermat n)) := by
  induction cnt with
  | zero =>
    intro arr j hj _ _
    refine ⟨rfl, fun _ _ _ => rfl, fun _ _ _ => rfl, fun p h₁ h₂ => absurd h₂ (by lia)⟩
  | succ cnt ih =>
    intro arr j hj hb hv
    obtain ⟨hS, hB, ht, htd⟩ := hb
    have hF : 0 < fermat n := by simp [fermat]
    have hjh : j < h := by lia
    have hxy := step_le (w := n + 1) (show j + 1 ≤ h + j by lia)
    have hyB := win_in o n (h + j) (h + h) (by lia)
    have hσ₀ : 0 < σ := by
      rcases Nat.eq_zero_or_pos σ with e | e
      · rw [e, Nat.zero_mul] at hσ; lia
      · exact e
    have he : (if j = 0 then 0 else 64 * n - σ * j) < 64 * n := by
      split
      · lia
      · have : 0 < σ * j := Nat.mul_pos hσ₀ (by lia)
        lia
    obtain ⟨b₁, b₂, b₃, b₄⟩ := invBfly_spec arr n (o + j * (n + 1)) (o + (h + j) * (n + 1)) t
      (if j = 0 then 0 else 64 * n - σ * j) (j == 0)
      ⟨hS, by lia, by lia, ht, by lia, by lia, by lia⟩
      hn he (by lia) (hv j (by lia)) (hv (h + j) (by lia))
    rw [invLoop]
    generalize invBfly arr n (o + j * (n + 1)) (o + (h + j) * (n + 1)) t
      (if j = 0 then 0 else 64 * n - σ * j) (j == 0) = a₁ at *
    have hc : ∀ p < h + h, p ≠ j → p ≠ h + j → coef a₁ n o p = coef arr n o p := by
      intro p hp h₁ h₂
      have d₁ := win_disj o n p j h₁
      have d₂ := win_disj o n p (h + j) h₂
      have d₃ := win_in o n p (h + h) hp
      exact UInt64Array.valAt_congr _ fun i _ _ => b₂ i (by lia) (by lia) (by lia)
    have hv₁ : ∀ p < h + h, coef a₁ n o p < fermat n := by
      intro p hp
      by_cases e₁ : p = j
      · subst e₁; show win a₁ n _ < _; rw [b₃]; split <;> exact Nat.mod_lt _ hF
      by_cases e₂ : p = h + j
      · subst e₂; show win a₁ n _ < _; rw [b₄]; split <;> exact Nat.mod_lt _ hF
      rw [hc p hp e₁ e₂]; exact hv p hp
    obtain ⟨i₁, i₂, i₃, i₄⟩ := ih a₁ (j + 1) (by lia) ⟨by lia, by lia, by lia, htd⟩ hv₁
    refine ⟨i₁.trans b₁, fun i h₁ h₂ => ?_, fun p hp hpj => ?_, fun p h₁ h₂ => ?_⟩
    · have d₃ := win_in o n j (h + h) (by lia)
      rw [i₂ i h₁ h₂, b₂ i (by lia) (by lia) h₂]
    · rw [i₃ p hp (by lia), hc p hp (by lia) (by lia)]
    · by_cases e : p = j
      · subst e
        rw [i₃ p (by lia) (by lia), i₃ (h + p) (by lia) (by lia)]
        exact ⟨b₃, b₄⟩
      · obtain ⟨k₁, k₂⟩ := i₄ p (by lia) h₂
        have c₁ := hc p (by lia) e (by lia)
        have c₂ := hc (h + p) (by lia) (by lia) (by lia)
        rw [c₁, c₂] at k₁ k₂
        exact ⟨k₁, k₂⟩

section
variable {N F : Nat} (hF : F = 2 ^ N + 1)
include hF

omit hF in
private theorem inv_first_x {A B SA SB : Nat} (hA : MEq F A SA) (hB : MEq F B SB) (τ : Nat) :
    MEq F ((A + B) % F) (SA + SB * 2 ^ (τ * 0)) := by
  rw [Nat.mul_zero, Nat.pow_zero, Nat.mul_one]
  exact (MEq.mod _ _).trans (MEq.add hA hB)

private theorem inv_first_y {A B SA SB : Nat} (hA : MEq F A SA) (hB : MEq F B SB) (hB' : B ≤ F)
    (τ : Nat) : MEq F ((A + F - B) % F) (SA + SB * 2 ^ (τ * 0) * 2 ^ N) := by
  rw [Nat.mul_zero, Nat.pow_zero, Nat.mul_one]
  exact (MEq.mod _ _).trans ((neg_eq hF _ _ hB').trans (MEq.add hA (MEq.mul hB (MEq.refl _ _))))

private theorem inv_rest_x {A B SA SB e τ l q : Nat} (hA : MEq F A SA) (hB : MEq F B SB)
    (he : τ * l = e + N + 2 * N * q) :
    MEq F ((A + F - B * 2 ^ e % F) % F) (SA + SB * 2 ^ (τ * l)) := by
  have hF₀ : 0 < F := by rw [hF]; exact Nat.succ_pos _
  calc (A + F - B * 2 ^ e % F) % F
      MEq F _ (A + B * 2 ^ e % F * 2 ^ N) := (MEq.mod _ _).trans (neg_eq hF _ _ (Nat.le_of_lt
        (Nat.mod_lt _ hF₀)))
      MEq F _ (SA + SB * 2 ^ e * 2 ^ N) := MEq.add hA (MEq.mul ((MEq.mod _ _).trans (MEq.mul hB
        (MEq.refl _ _))) (MEq.refl _ _))
      _ = SA + SB * 2 ^ (e + N) := by rw [Nat.pow_add, Nat.mul_assoc]
      MEq F _ (SA + SB * 2 ^ (e + N + 2 * N * q)) := MEq.add (MEq.refl _ _) (MEq.mul (MEq.refl _ _)
        (pow_period hF _ _).symm)
      _ = SA + SB * 2 ^ (τ * l) := by rw [he]

private theorem inv_rest_y {A B SA SB e τ l q : Nat} (hA : MEq F A SA) (hB : MEq F B SB)
    (he : τ * l = e + N + 2 * N * q) :
    MEq F ((A + B * 2 ^ e % F) % F) (SA + SB * 2 ^ (τ * l) * 2 ^ N) := by
  calc (A + B * 2 ^ e % F) % F
      MEq F _ (SA + SB * 2 ^ e) := (MEq.mod _ _).trans (MEq.add hA ((MEq.mod _ _).trans
        (MEq.mul hB (MEq.refl _ _))))
      MEq F _ (SA + SB * 2 ^ e * 2 ^ N * 2 ^ N) := MEq.add (MEq.refl _ _) (pow_N_pow_N hF _).symm
      _ = SA + SB * 2 ^ (e + N) * 2 ^ N := by rw [Nat.pow_add, Nat.mul_assoc SB]
      MEq F _ (SA + SB * 2 ^ (e + N + 2 * N * q) * 2 ^ N) := MEq.add (MEq.refl _ _) (MEq.mul
        (MEq.mul (MEq.refl _ _) (pow_period hF _ _).symm) (MEq.refl _ _))
      _ = SA + SB * 2 ^ (τ * l) * 2 ^ N := by rw [he]

end

/--
The inverse transform of the block of `2ᵐ` windows at `o`, with the root `2^(2 N - σ)`: the
transforms of each half, then the butterflies.
-/
public def inv (n t : Nat) : Nat → UInt64Array → Nat → Nat → UInt64Array
  | 0, arr, _, _ => arr
  | m + 1, arr, o, σ =>
    let a := inv n t m arr o (2 * σ)
    let a := inv n t m a (o + 2 ^ m * (n + 1)) (2 * σ)
    invLoop n o (2 ^ m) σ t a 0 (2 ^ m)

set_option maxHeartbeats 400000 in
public theorem inv_spec (n t : Nat) (hn : 1 ≤ n) (h64 : 64 * n < USize.size) (m : Nat) :
    ∀ arr o σ, σ * 2 ^ m = 2 * (64 * n) → Block arr n o (2 ^ m) t →
      (∀ p < 2 ^ m, coef arr n o p < fermat n) →
      (inv n t m arr o σ).size = arr.size ∧
      (∀ i, (i < o ∨ o + 2 ^ m * (n + 1) ≤ i) → (i < t ∨ t + n + 1 ≤ i) →
        (inv n t m arr o σ)[i]! = arr[i]!) ∧
      (∀ l < 2 ^ m, coef (inv n t m arr o σ) n o l =
        sumRange (fun p => coef arr n o p * 2 ^ ((2 * (64 * n) - σ) * rev m p * l)) (2 ^ m) %
          fermat n) := by
  induction m with
  | zero =>
    intro arr o σ _ _ hv
    refine ⟨rfl, fun _ _ _ => rfl, fun p hp => ?_⟩
    simp only [Nat.pow_zero] at hp
    have : p = 0 := by lia
    subst this
    simp only [inv, sumRange, Nat.mul_zero, Nat.pow_zero, Nat.mul_one, Nat.zero_add]
    exact (Nat.mod_eq_of_lt (hv 0 (by simp))).symm
  | succ m ih =>
    intro arr o σ hσ hb hv
    obtain ⟨hS, hB, ht, htd⟩ := hb
    have hF : 0 < fermat n := by simp [fermat]
    have h2 : 2 ^ (m + 1) = 2 ^ m + 2 ^ m := by rw [Nat.pow_succ]; lia
    rw [h2] at hB htd hv ⊢
    have hσ' : σ * 2 ^ m = 64 * n := by rw [h2] at hσ; lia
    have hm₀ : 1 ≤ 2 ^ m := Nat.one_le_two_pow
    simp only [inv]
    have hmid := Nat.mul_le_mul_right (n + 1) (show 2 ^ m ≤ 2 ^ m + 2 ^ m by lia)
    have hoff : ∀ p, o + 2 ^ m * (n + 1) + p * (n + 1) = o + (2 ^ m + p) * (n + 1) := by
      intro p; rw [Nat.add_mul]; lia
    -- The first half.
    obtain ⟨f₁, f₂, f₃⟩ := ih arr o (2 * σ) (by rw [Nat.mul_assoc, hσ']) ⟨hS, by lia, ht,
      by lia⟩ (fun p hp => hv p (by lia))
    generalize inv n t m arr o (2 * σ) = a₁ at *
    -- The second half.
    have hu₁ : ∀ p < 2 ^ m, coef a₁ n (o + 2 ^ m * (n + 1)) p = coef arr n o (2 ^ m + p) := by
      intro p hp
      have d := win_in o n (2 ^ m + p) (2 ^ m + 2 ^ m) (by lia)
      show win a₁ n _ = win arr n _
      rw [hoff, win_congr fun i _ _ => f₂ i (by lia) (by lia)]
    obtain ⟨g₁, g₂, g₃⟩ := ih a₁ (o + 2 ^ m * (n + 1)) (2 * σ) (by rw [Nat.mul_assoc, hσ'])
      ⟨by lia, by lia, by lia, by lia⟩ (fun p hp => by rw [hu₁ p hp]; exact hv _ (by lia))
    generalize inv n t m a₁ (o + 2 ^ m * (n + 1)) (2 * σ) = a₂ at *
    -- The halves, as transforms.
    have hA : ∀ l < 2 ^ m, coef a₂ n o l = sumRange (fun p => coef arr n o p *
        2 ^ ((2 * (64 * n) - 2 * σ) * rev m p * l)) (2 ^ m) % fermat n := by
      intro l hl
      have d := win_in o n l (2 ^ m) hl
      show win a₂ n _ = _
      rw [win_congr fun i _ _ => g₂ i (by lia) (by lia)]
      exact f₃ l hl
    have hBv : ∀ l < 2 ^ m, coef a₂ n o (2 ^ m + l) = sumRange (fun p => coef arr n o (2 ^ m + p) *
        2 ^ ((2 * (64 * n) - 2 * σ) * rev m p * l)) (2 ^ m) % fermat n := by
      intro l hl
      show win a₂ n _ = _
      rw [← hoff]
      show coef a₂ n (o + 2 ^ m * (n + 1)) l = _
      rw [g₃ l hl]
      exact congrArg (· % fermat n) (sumRange_congr fun p hp => by rw [hu₁ p hp])
    have hv₂ : ∀ p < 2 ^ m + 2 ^ m, coef a₂ n o p < fermat n := by
      intro p hp
      rcases Nat.lt_or_ge p (2 ^ m) with e | e
      · rw [hA p e]; exact Nat.mod_lt _ hF
      · obtain ⟨p', rfl⟩ : ∃ p', p = 2 ^ m + p' := ⟨p - 2 ^ m, by lia⟩
        rw [hBv p' (by lia)]; exact Nat.mod_lt _ hF
    -- The butterflies.
    obtain ⟨l₁, l₂, -, l₄⟩ := invLoop_spec n o (2 ^ m) σ t hn hσ' h64 (2 ^ m) a₂ 0 (by lia)
      ⟨by lia, by lia, by lia, htd⟩ hv₂
    generalize invLoop n o (2 ^ m) σ t a₂ 0 (2 ^ m) = a₃ at *
    refine ⟨by rw [l₁, g₁, f₁], fun i h₁ h₂ => ?_, fun l hl => ?_⟩
    · rw [l₂ i h₁ h₂, g₂ i (by lia) h₂, f₂ i (by lia) h₂]
    -- Each output is congruent to the sum, and reduced.
    have hσle : σ ≤ σ * 2 ^ m := Nat.le_mul_of_pos_right σ hm₀
    have hτ : 2 * (64 * n) - σ + σ = 2 * (64 * n) := by lia
    have hτ' : 2 * (64 * n) - 2 * σ + 2 * σ = 2 * (64 * n) := by lia
    have hsplit : ∀ l', sumRange (fun p => coef arr n o p *
        2 ^ ((2 * (64 * n) - σ) * rev (m + 1) p * l')) (2 ^ m + 2 ^ m) = sumRange (fun p => coef arr n o p * 2 ^ ((2 * (64 * n) - σ) *
          (2 * rev m p) * l')) (2 ^ m) + sumRange (fun p => coef arr n o (2 ^ m + p) *
          2 ^ ((2 * (64 * n) - σ) * (2 * rev m p + 1) * l')) (2 ^ m) := by
      intro l'
      rw [sumRange_append]
      congr 1
      · exact sumRange_congr fun p hp => by rw [rev_succ_lo m p hp]
      · exact sumRange_congr fun p hp => by rw [rev_succ_hi m p]
    have hred : ∀ {c S}, c < fermat n → MEq (fermat n) c S → c = S % fermat n :=
      fun hc h => (Nat.mod_eq_of_lt hc).symm.trans h
    have hMA : ∀ l < 2 ^ m, MEq (fermat n) (coef a₂ n o l) (sumRange (fun p => coef arr n o p *
        2 ^ ((2 * (64 * n) - 2 * σ) * rev m p * l)) (2 ^ m)) := fun l hl => by
      rw [hA l hl]; exact MEq.mod _ _
    have hMB : ∀ l < 2 ^ m, MEq (fermat n) (coef a₂ n o (2 ^ m + l)) (sumRange (fun p =>
        coef arr n o (2 ^ m + p) * 2 ^ ((2 * (64 * n) - 2 * σ) * rev m p * l)) (2 ^ m)) :=
      fun l hl => by rw [hBv l hl]; exact MEq.mod _ _
    -- The exponent of a twiddle, `τ l ≡ e + N`.
    have hexp : ∀ l₁, l₁ + 1 < 2 ^ m → (2 * (64 * n) - σ) * (l₁ + 1) =
        (64 * n - σ * (l₁ + 1)) + 64 * n + 2 * (64 * n) * l₁ := by
      intro l₁ hl₁
      have h₁ : σ * (l₁ + 1) ≤ σ * 2 ^ m := Nat.mul_le_mul_left σ (by lia)
      rw [Nat.sub_mul]
      lia
    have hcl : ∀ l < 2 ^ m, coef a₃ n o l < fermat n ∧ coef a₃ n o (2 ^ m + l) < fermat n := by
      intro l hl
      obtain ⟨k₁, k₂⟩ := l₄ l (by lia) hl
      rw [k₁, k₂]
      constructor <;> split <;> exact Nat.mod_lt _ hF
    rcases Nat.lt_or_ge l (2 ^ m) with e | e
    · -- The outputs `l`.
      obtain ⟨k₁, -⟩ := l₄ l (by lia) e
      refine hred (hcl l e).1 ?_
      rw [hsplit l]
      refine MEq.trans ?_ (inv_lo rfl _ (rev m) σ _ _ (2 ^ m) l hτ hτ').symm
      rw [k₁]
      by_cases e₀ : l = 0
      · subst e₀
        simp only [beq_self_eq_true, ↓reduceIte]
        exact inv_first_x (hMA 0 e) (hMB 0 e) _
      · obtain ⟨l₁, rfl⟩ : ∃ l₁, l = l₁ + 1 := ⟨l - 1, by lia⟩
        simp only [show (l₁ + 1 == 0) = false from rfl, Bool.false_eq_true, ↓reduceIte,
          show l₁ + 1 ≠ 0 by lia]
        exact inv_rest_x rfl (hMA _ e) (hMB _ e) (hexp l₁ e)
    · -- The outputs `2ᵐ + l`.
      obtain ⟨l', rfl⟩ : ∃ l', l = 2 ^ m + l' := ⟨l - 2 ^ m, by lia⟩
      have e' : l' < 2 ^ m := by lia
      obtain ⟨-, k₂⟩ := l₄ l' (by lia) e'
      refine hred (hcl l' e').2 ?_
      rw [hsplit (2 ^ m + l')]
      refine MEq.trans ?_ (inv_hi rfl _ (rev m) σ _ _ (2 ^ m) l' hτ hτ' hσ' hm₀).symm
      rw [k₂]
      by_cases e₀ : l' = 0
      · subst e₀
        simp only [beq_self_eq_true, ↓reduceIte]
        exact inv_first_y rfl (hMA 0 e') (hMB 0 e') (Nat.le_of_lt (hv₂ _ (by lia))) _
      · obtain ⟨l₁, rfl⟩ : ∃ l₁, l' = l₁ + 1 := ⟨l' - 1, by lia⟩
        simp only [show (l₁ + 1 == 0) = false from rfl, Bool.false_eq_true, ↓reduceIte,
          show l₁ + 1 ≠ 0 by lia]
        exact inv_rest_y rfl (hMA _ e') (hMB _ e') (hexp l₁ e')

end MPN.FFT
