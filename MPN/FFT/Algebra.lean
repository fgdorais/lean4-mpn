/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import MPN.Sum
public import MPN.Poly
public import MPN.FFT.Roots

/-!
# The algebra of the transforms

The arithmetic of Schönhage–Strassen's transforms modulo `F = 2ᴺ + 1` on `Nat`, for any `N`, so
for limbs of any width: congruences (`MEq`), the reversal of the bits of an index (`rev`), the
identities of the butterflies of the forward transform by decimation in frequency and of the
inverse one by decimation in time, and the coefficients that the transforms give (`fft_coef`),
also when the pieces of the operands wrap around, for products modulo `x^K - 1` (`fft_coef_cyc`).
The transforms themselves, on residues in windows of limbs, are on `main32` and `main64`.
-/

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

section
variable {N F : Nat} (hF : F = 2 ^ N + 1)
include hF

omit hF in
public theorem inv_first_x {A B SA SB : Nat} (hA : MEq F A SA) (hB : MEq F B SB) (τ : Nat) :
    MEq F ((A + B) % F) (SA + SB * 2 ^ (τ * 0)) := by
  rw [Nat.mul_zero, Nat.pow_zero, Nat.mul_one]
  exact (MEq.mod _ _).trans (MEq.add hA hB)

public theorem inv_first_y {A B SA SB : Nat} (hA : MEq F A SA) (hB : MEq F B SB) (hB' : B ≤ F)
    (τ : Nat) : MEq F ((A + F - B) % F) (SA + SB * 2 ^ (τ * 0) * 2 ^ N) := by
  rw [Nat.mul_zero, Nat.pow_zero, Nat.mul_one]
  exact (MEq.mod _ _).trans ((neg_eq hF _ _ hB').trans (MEq.add hA (MEq.mul hB (MEq.refl _ _))))

public theorem inv_rest_x {A B SA SB e τ l q : Nat} (hA : MEq F A SA) (hB : MEq F B SB)
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

public theorem inv_rest_y {A B SA SB e τ l q : Nat} (hA : MEq F A SA) (hB : MEq F B SB)
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

/-! ## The coefficients -/

public theorem sum_eq_polyVal (αL : List Nat) (σ q K : Nat) (h : αL.length ≤ K) :
    sumRange (fun i => αL.getD i 0 * 2 ^ (σ * i * q)) K = polyVal (2 ^ (σ * q)) αL := by
  rw [polyVal_eq_sumRange _ αL K h]
  exact sumRange_congr fun i _ => by rw [← Nat.pow_mul]; congr 2; grind

/--
The coefficients from the transforms: the forward transforms of `α` and `β`, their pointwise
products, the inverse transform and the division by `2ᵏ` give the coefficients of `α β`, exactly
when they are less than `F`.
-/
public theorem fft_coef (αL βL : List Nat) (k N σ X : Nat) {F : Nat} (hF : F = 2 ^ N + 1)
    (hk : 1 ≤ k)
    (hσ : σ * 2 ^ k = 2 * (N)) (hlen : αL.length + βL.length ≤ 2 ^ k + 1) (hβ : βL ≠ [])
    (hαX : ∀ a ∈ αL, a < X) (hβX : ∀ b ∈ βL, b < X) (hbits : 2 ^ k * (X * X) ≤ 2 ^ (N))
    (hαK : αL.length ≤ 2 ^ k) (hβK : βL.length ≤ 2 ^ k) (l : Nat) (hl : l < 2 ^ k) :
    (F - sumRange (fun p =>
        sumRange (fun i => αL.getD i 0 * 2 ^ (σ * i * rev k p)) (2 ^ k) % F *
          (sumRange (fun i => βL.getD i 0 * 2 ^ (σ * i * rev k p)) (2 ^ k) % F) %
            F * 2 ^ ((2 * (N) - σ) * rev k p * l)) (2 ^ k) % F *
        2 ^ (N - k) % F) % F = (polyMul αL βL).getD l 0 := by
  have hF₀ : 0 < F := by rw [hF]; exact Nat.succ_pos _
  generalize hZ : polyMul αL βL = Z
  have hZK : Z.length ≤ 2 ^ k := by
    rw [← hZ]; have := length_polyMul αL βL hβ; lia
  -- `σ 2ᵏ⁻¹ = N`, and `τ = 2 N - σ` is the inverse root.
  have hk₁ : 2 ^ k = 2 * 2 ^ (k - 1) := by
    rw [← Nat.pow_succ']; congr 1; lia
  have hσN : σ * 2 ^ (k - 1) = N := by rw [hk₁] at hσ; lia
  have hσle : σ ≤ 2 * (N) := by
    rw [← hσ]; exact Nat.le_mul_of_pos_right _ (Nat.two_pow_pos _)
  -- The pointwise products are the values of `Z`.
  have hP : ∀ p, MEq (F)
      (sumRange (fun i => αL.getD i 0 * 2 ^ (σ * i * rev k p)) (2 ^ k) % F *
        (sumRange (fun i => βL.getD i 0 * 2 ^ (σ * i * rev k p)) (2 ^ k) % F) % F)
      (polyVal (2 ^ (σ * rev k p)) Z) := by
    intro p
    rw [sum_eq_polyVal _ _ _ _ hαK, sum_eq_polyVal _ _ _ _ hβK, ← hZ, polyVal_polyMul]
    exact (MEq.mod _ _).trans (MEq.mul (MEq.mod _ _) (MEq.mod _ _))
  -- The inverse transform, reindexed by `rev`.
  have hV : MEq (F) (sumRange (fun p =>
      sumRange (fun i => αL.getD i 0 * 2 ^ (σ * i * rev k p)) (2 ^ k) % F *
        (sumRange (fun i => βL.getD i 0 * 2 ^ (σ * i * rev k p)) (2 ^ k) % F) %
          F * 2 ^ ((2 * (N) - σ) * rev k p * l)) (2 ^ k) % F)
      (2 ^ k * Z.getD l 0) := by
    refine (MEq.mod _ _).trans ?_
    refine (MEq.sum fun p _ => MEq.mul (hP p) (MEq.refl _ _)).trans ?_
    rw [sumRange_rev (fun q => polyVal (2 ^ (σ * q)) Z * 2 ^ ((2 * (N) - σ) * q * l)) k]
    have e : sumRange (fun q => polyVal (2 ^ (σ * q)) Z * 2 ^ ((2 * (N) - σ) * q * l))
        (2 ^ k) = sumRange (fun j => sumRange (fun i => Z.getD i 0 * (2 ^ σ) ^ (i * j)) (2 ^ k) *
          (2 ^ (2 * (N) - σ)) ^ (j * l)) (2 ^ k) := by
      refine sumRange_congr fun q _ => ?_
      rw [polyVal_eq_sumRange _ Z _ hZK, ← Nat.pow_mul, Nat.mul_assoc]
      congr 1
      exact sumRange_congr fun i _ => by rw [← Nat.pow_mul, ← Nat.pow_mul]; congr 2; grind
    rw [e]
    refine inverse_mod (2 ^ σ) (2 ^ (2 * (N) - σ)) (F) k hk ?_ ?_ _ l hl
    · rw [← Nat.pow_mul, hσN, hF]; simp
    · rw [← Nat.pow_add, show σ + (2 * (N) - σ) = 2 * (N) by lia]
      exact pow_two_N hF
  -- Dividing by `2ᵏ`: `-2^(N - k) 2ᵏ = -2ᴺ ≡ 1`.
  have hc : MEq (F) ((F - sumRange (fun p =>
      sumRange (fun i => αL.getD i 0 * 2 ^ (σ * i * rev k p)) (2 ^ k) % F *
        (sumRange (fun i => βL.getD i 0 * 2 ^ (σ * i * rev k p)) (2 ^ k) % F) %
          F * 2 ^ ((2 * (N) - σ) * rev k p * l)) (2 ^ k) % F *
        2 ^ (N - k) % F) % F) (Z.getD l 0) := by
    have hkN : k ≤ N := by
      have : 2 ^ k ≤ 2 ^ (N) := Nat.le_trans (Nat.le_mul_of_pos_right _ (by
        have : 0 < X := by
          rcases βL with _ | ⟨b, _⟩
          · exact absurd rfl hβ
          · exact Nat.lt_of_le_of_lt (Nat.zero_le _) (hβX b (by simp))
        exact Nat.mul_pos this this)) hbits
      exact (Nat.pow_le_pow_iff_right (by decide)).1 this
    refine (MEq.mod _ _).trans ?_
    rw [show F - _ = 0 + F - _ by rw [Nat.zero_add]]
    refine (neg_eq hF _ _ (Nat.le_of_lt (Nat.mod_lt _ hF₀))).trans ?_
    rw [Nat.zero_add]
    refine (MEq.mul ((MEq.mod _ _).trans (MEq.mul hV (MEq.refl _ _))) (MEq.refl _ _)).trans ?_
    rw [show 2 ^ k * Z.getD l 0 * 2 ^ (N - k) = Z.getD l 0 * 2 ^ (N) by
      rw [Nat.mul_comm (2 ^ k), Nat.mul_assoc, ← Nat.pow_add,
        show k + (N - k) = N by lia]]
    exact pow_N_pow_N hF _
  -- Both are less than `F`.
  have hZl : Z.getD l 0 < F := by
    have h₁ := getD_polyMul_le αL βL (X - 1) (X - 1) (fun a h => by have := hαX a h; lia)
      (fun b h => by have := hβX b h; lia) l
    rw [hZ] at h₁
    have h₂ : (X - 1) * (X - 1) < X * X ∨ X = 0 := by
      rcases Nat.eq_zero_or_pos X with e | e
      · exact .inr e
      · exact .inl (Nat.mul_lt_mul'' (by lia) (by lia))
    have h₃ : αL.length * ((X - 1) * (X - 1)) ≤ 2 ^ k * (X * X) := by
      rcases h₂ with h | h
      · exact Nat.mul_le_mul hαK (Nat.le_of_lt h)
      · subst h; simp
    rw [hF]
    lia
  rw [← Nat.mod_eq_of_lt hZl]
  exact (Nat.mod_mod _ _).symm.trans hc

/-! ## Wrapped products -/

/-- The cyclic fold of a polynomial modulo `x^K - 1`: coefficient `l` is `Z_l + Z_{l+K}`. -/
@[expose] public def cyc (Z : List Nat) (K : Nat) : List Nat :=
  (List.range K).map fun l => Z.getD l 0 + Z.getD (l + K) 0

public theorem length_cyc (Z : List Nat) (K : Nat) : (cyc Z K).length = K := by simp [cyc]

public theorem getD_cyc (Z : List Nat) (K l : Nat) (hl : l < K) :
    (cyc Z K).getD l 0 = Z.getD l 0 + Z.getD (l + K) 0 := by
  simp [cyc, hl]

/-- At a `K`-th root of unity, a polynomial of degree below `2 K` has the value of its fold. -/
public theorem polyVal_cyc (y F K : Nat) (Z : List Nat) (hy : MEq F (y ^ K) 1)
    (hZ : Z.length ≤ 2 * K) : MEq F (polyVal y Z) (polyVal y (cyc Z K)) := by
  rw [polyVal_eq_sumRange _ Z (K + K) (by lia), sumRange_append,
    polyVal_eq_sumRange _ (cyc Z K) K (by rw [length_cyc]; exact Nat.le_refl _)]
  have e : sumRange (fun i => (cyc Z K).getD i 0 * y ^ i) K =
      sumRange (fun i => Z.getD i 0 * y ^ i) K +
        sumRange (fun i => Z.getD (i + K) 0 * y ^ i) K := by
    rw [← sumRange_add]
    exact sumRange_congr fun i hi => by rw [getD_cyc _ _ _ hi, Nat.add_mul]
  rw [e]
  refine MEq.add (MEq.refl _ _) (MEq.sum fun i _ => ?_)
  rw [Nat.add_comm K i, Nat.pow_add]
  have := MEq.mul (MEq.refl F (Z.getD (i + K) 0 * y ^ i)) hy
  rw [Nat.mul_one] at this
  rw [← Nat.mul_assoc]
  exact this

/--
The coefficients from the transforms when the pieces wrap around: with `K = 2ᵏ` pieces of each
operand, the forward transforms, their pointwise products, the inverse transform and the division
by `2ᵏ` give the coefficients of `α β` modulo `x^K - 1`, exactly when they are less than `F`.
-/
public theorem fft_coef_cyc (αL βL : List Nat) (k N σ X : Nat) {F : Nat} (hF : F = 2 ^ N + 1)
    (hk : 1 ≤ k)
    (hσ : σ * 2 ^ k = 2 * (N)) (hβ : βL ≠ [])
    (hαX : ∀ a ∈ αL, a < X) (hβX : ∀ b ∈ βL, b < X) (hbits : 2 * 2 ^ k * (X * X) ≤ 2 ^ (N))
    (hαK : αL.length ≤ 2 ^ k) (hβK : βL.length ≤ 2 ^ k) (l : Nat) (hl : l < 2 ^ k) :
    (F - sumRange (fun p =>
        sumRange (fun i => αL.getD i 0 * 2 ^ (σ * i * rev k p)) (2 ^ k) % F *
          (sumRange (fun i => βL.getD i 0 * 2 ^ (σ * i * rev k p)) (2 ^ k) % F) %
            F * 2 ^ ((2 * (N) - σ) * rev k p * l)) (2 ^ k) % F *
        2 ^ (N - k) % F) % F =
      (polyMul αL βL).getD l 0 + (polyMul αL βL).getD (l + 2 ^ k) 0 := by
  have hF₀ : 0 < F := by rw [hF]; exact Nat.succ_pos _
  have hZ2 : (polyMul αL βL).length ≤ 2 * 2 ^ k := by
    have := length_polyMul αL βL hβ; lia
  rw [← getD_cyc _ _ _ hl]
  generalize hZ : cyc (polyMul αL βL) (2 ^ k) = Z
  have hZK : Z.length ≤ 2 ^ k := by rw [← hZ, length_cyc]; exact Nat.le_refl _
  have hk₁ : 2 ^ k = 2 * 2 ^ (k - 1) := by
    rw [← Nat.pow_succ']; congr 1; lia
  have hσN : σ * 2 ^ (k - 1) = N := by rw [hk₁] at hσ; lia
  have hσle : σ ≤ 2 * (N) := by
    rw [← hσ]; exact Nat.le_mul_of_pos_right _ (Nat.two_pow_pos _)
  -- The pointwise products are the values of the fold `Z`.
  have hP : ∀ p, MEq (F)
      (sumRange (fun i => αL.getD i 0 * 2 ^ (σ * i * rev k p)) (2 ^ k) % F *
        (sumRange (fun i => βL.getD i 0 * 2 ^ (σ * i * rev k p)) (2 ^ k) % F) % F)
      (polyVal (2 ^ (σ * rev k p)) Z) := by
    intro p
    rw [sum_eq_polyVal _ _ _ _ hαK, sum_eq_polyVal _ _ _ _ hβK, ← hZ]
    refine ((MEq.mod _ _).trans (MEq.mul (MEq.mod _ _) (MEq.mod _ _))).trans ?_
    rw [← polyVal_polyMul]
    refine polyVal_cyc _ _ _ _ ?_ hZ2
    rw [← Nat.pow_mul, show σ * rev k p * 2 ^ k = 2 * (N) * rev k p by
      rw [Nat.mul_right_comm, hσ], Nat.pow_mul]
    have := MEq.mul (pow_two_N hF) (MEq.refl (F) 1)
    clear this
    induction rev k p with
    | zero => exact MEq.refl _ _
    | succ j ih =>
      rw [Nat.pow_succ]
      have := MEq.mul ih (pow_two_N hF)
      rw [Nat.one_mul] at this
      exact this
  -- The inverse transform, reindexed by `rev`.
  have hV : MEq (F) (sumRange (fun p =>
      sumRange (fun i => αL.getD i 0 * 2 ^ (σ * i * rev k p)) (2 ^ k) % F *
        (sumRange (fun i => βL.getD i 0 * 2 ^ (σ * i * rev k p)) (2 ^ k) % F) %
          F * 2 ^ ((2 * (N) - σ) * rev k p * l)) (2 ^ k) % F)
      (2 ^ k * Z.getD l 0) := by
    refine (MEq.mod _ _).trans ?_
    refine (MEq.sum fun p _ => MEq.mul (hP p) (MEq.refl _ _)).trans ?_
    rw [sumRange_rev (fun q => polyVal (2 ^ (σ * q)) Z * 2 ^ ((2 * (N) - σ) * q * l)) k]
    have e : sumRange (fun q => polyVal (2 ^ (σ * q)) Z * 2 ^ ((2 * (N) - σ) * q * l))
        (2 ^ k) = sumRange (fun j => sumRange (fun i => Z.getD i 0 * (2 ^ σ) ^ (i * j)) (2 ^ k) *
          (2 ^ (2 * (N) - σ)) ^ (j * l)) (2 ^ k) := by
      refine sumRange_congr fun q _ => ?_
      rw [polyVal_eq_sumRange _ Z _ hZK, ← Nat.pow_mul, Nat.mul_assoc]
      congr 1
      exact sumRange_congr fun i _ => by rw [← Nat.pow_mul, ← Nat.pow_mul]; congr 2; grind
    rw [e]
    refine inverse_mod (2 ^ σ) (2 ^ (2 * (N) - σ)) (F) k hk ?_ ?_ _ l hl
    · rw [← Nat.pow_mul, hσN, hF]; simp
    · rw [← Nat.pow_add, show σ + (2 * (N) - σ) = 2 * (N) by lia]
      exact pow_two_N hF
  -- Dividing by `2ᵏ`.
  have hc : MEq (F) ((F - sumRange (fun p =>
      sumRange (fun i => αL.getD i 0 * 2 ^ (σ * i * rev k p)) (2 ^ k) % F *
        (sumRange (fun i => βL.getD i 0 * 2 ^ (σ * i * rev k p)) (2 ^ k) % F) %
          F * 2 ^ ((2 * (N) - σ) * rev k p * l)) (2 ^ k) % F *
        2 ^ (N - k) % F) % F) (Z.getD l 0) := by
    have hkN : k ≤ N := by
      have : 2 ^ k ≤ 2 ^ (N) := Nat.le_trans (Nat.le_mul_of_pos_right _ (by
        have : 0 < X := by
          rcases βL with _ | ⟨b, _⟩
          · exact absurd rfl hβ
          · exact Nat.lt_of_le_of_lt (Nat.zero_le _) (hβX b (by simp))
        exact Nat.mul_pos this this)) (by rw [Nat.mul_assoc] at hbits; lia)
      exact (Nat.pow_le_pow_iff_right (by decide)).1 this
    refine (MEq.mod _ _).trans ?_
    rw [show F - _ = 0 + F - _ by rw [Nat.zero_add]]
    refine (neg_eq hF _ _ (Nat.le_of_lt (Nat.mod_lt _ hF₀))).trans ?_
    rw [Nat.zero_add]
    refine (MEq.mul ((MEq.mod _ _).trans (MEq.mul hV (MEq.refl _ _))) (MEq.refl _ _)).trans ?_
    rw [show 2 ^ k * Z.getD l 0 * 2 ^ (N - k) = Z.getD l 0 * 2 ^ (N) by
      rw [Nat.mul_comm (2 ^ k), Nat.mul_assoc, ← Nat.pow_add,
        show k + (N - k) = N by lia]]
    exact pow_N_pow_N hF _
  -- Both are less than `F`.
  have hZl : Z.getD l 0 < F := by
    rw [← hZ, getD_cyc _ _ _ hl]
    have h₁ := getD_polyMul_le αL βL (X - 1) (X - 1) (fun a h => by have := hαX a h; lia)
      (fun b h => by have := hβX b h; lia)
    have h₂ : (X - 1) * (X - 1) < X * X ∨ X = 0 := by
      rcases Nat.eq_zero_or_pos X with e | e
      · exact .inr e
      · exact .inl (Nat.mul_lt_mul'' (by lia) (by lia))
    have h₃ : αL.length * ((X - 1) * (X - 1)) ≤ 2 ^ k * (X * X) := by
      rcases h₂ with h | h
      · exact Nat.mul_le_mul hαK (Nat.le_of_lt h)
      · subst h; simp
    have := h₁ l
    have := h₁ (l + 2 ^ k)
    rw [hF]
    lia
  rw [← Nat.mod_eq_of_lt hZl]
  exact (Nat.mod_mod _ _).symm.trans hc

end MPN.FFT
