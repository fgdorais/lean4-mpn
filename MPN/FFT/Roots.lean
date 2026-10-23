/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import MPN.Sum
public import MPN.NatMod

/-!
# FFT multiplication

Schönhage–Strassen multiplication, like GMP's `mpn_mul_fft`: `a` and `b` are cut into `K = 2ᵏ`
pieces, whose products are the coefficients of a convolution. The convolution is computed modulo
the Fermat number `F = 2ᴺ + 1`, large enough to hold each coefficient, by a discrete Fourier
transform of length `K` with the root of unity `ω = 2^(2N / K)`: multiplying by a power of `ω` is
a shift, so the transforms need no products, and the `K` pointwise products are products of `N`
bits.

This first part, on natural numbers with the sums of `MPN.Sum` and the congruences of
`MPN.NatMod`, is the inversion of the transform modulo `F`. The transform of length `K` inverts
because its geometric sums `1 + x + ⋯ + x^(K - 1)` are the products `(1 + x) (1 + x²) ⋯
(1 + x^(K / 2))`, one of whose factors vanishes when `x` is a power of `ω` other than `1`, since
`ω^(K / 2) ≡ -1`. No division and no primality are needed. The residues are in
`MPN.FFT.Fermat`.
-/

namespace MPN.FFT

/-! ## Geometric sums of length `2ᵏ` -/

/-- `1 + x + ⋯ + x^(2ᵏ⁺¹ - 1) = (1 + x + ⋯ + x^(2ᵏ - 1)) (1 + x^(2ᵏ))`. -/
public theorem sumRange_pow_two_succ (x k : Nat) :
    sumRange (x ^ ·) (2 ^ (k + 1)) = sumRange (x ^ ·) (2 ^ k) * (1 + x ^ 2 ^ k) := by
  -- The second half is the first times `x^(2ᵏ)`.
  have split : ∀ m, sumRange (x ^ ·) (2 ^ k + m) =
      sumRange (x ^ ·) (2 ^ k) + x ^ 2 ^ k * sumRange (x ^ ·) m := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      rw [← Nat.add_assoc, sumRange_succ, ih, sumRange_succ, Nat.mul_add, Nat.pow_add]
      lia
  rw [Nat.pow_succ, Nat.mul_two, split, Nat.mul_add, Nat.mul_one, Nat.mul_comm]

/-- When some `x^(2ˢ)`, `s < k`, is `-1` modulo `F`, the geometric sum of length `2ᵏ` vanishes. -/
public theorem sumRange_pow_two_mod {x k s F : Nat} (hs : s < k)
    (hx : (x ^ 2 ^ s + 1) % F = 0) : sumRange (x ^ ·) (2 ^ k) % F = 0 := by
  induction k with
  | zero => lia
  | succ k ih =>
    rw [sumRange_pow_two_succ, Nat.mul_mod]
    by_cases hsk : s = k
    · subst hsk
      rw [Nat.add_comm 1, hx, Nat.mul_zero, Nat.zero_mod]
    · rw [ih (by lia), Nat.zero_mul, Nat.zero_mod]

/-! ## Roots of unity -/

/-- Every positive `d` is `2ᵛ u` with `u` odd. -/
public theorem exists_two_pow_mul_odd (d : Nat) (hd : 0 < d) :
    ∃ v u, d = 2 ^ v * u ∧ u % 2 = 1 := by
  induction d using Nat.strongRecOn with
  | ind d ih =>
    rcases Nat.mod_two_eq_zero_or_one d with h | h
    · obtain ⟨v, u, e, hu⟩ := ih (d / 2) (by lia) (by lia)
      exact ⟨v + 1, u, by rw [Nat.pow_succ]; lia, hu⟩
    · exact ⟨0, d, by simp, h⟩

/--
When `ω^(2ᵏ⁻¹) ≡ -1` modulo `F`, every power `ωᵈ` with `0 < d < 2ᵏ` has a power `(ωᵈ)^(2ˢ)`,
`s < k`, that is `-1` modulo `F`: with `d = 2ᵛ u`, `u` odd, take `s = k - 1 - v`.
-/
public theorem exists_pow_two_neg_one {w F k d : Nat} (hw : (w ^ 2 ^ (k - 1) + 1) % F = 0)
    (hd : 0 < d) (hdk : d < 2 ^ k) : ∃ s < k, ((w ^ d) ^ 2 ^ s + 1) % F = 0 := by
  obtain ⟨v, u, rfl, hu⟩ := exists_two_pow_mul_odd d hd
  have hv : v < k := by
    have : 2 ^ v ≤ 2 ^ v * u := Nat.le_mul_of_pos_right _ (by lia)
    exact (Nat.pow_lt_pow_iff_right (show 1 < 2 by decide)).1 (by lia)
  refine ⟨k - 1 - v, by lia, ?_⟩
  have e : (w ^ (2 ^ v * u)) ^ 2 ^ (k - 1 - v) = (w ^ 2 ^ (k - 1)) ^ u := by
    rw [← Nat.pow_mul, ← Nat.pow_mul]
    congr 1
    rw [Nat.mul_comm (2 ^ v) u, Nat.mul_assoc, ← Nat.pow_add,
      show v + (k - 1 - v) = k - 1 by lia, Nat.mul_comm]
  rw [e]
  exact pow_odd_mod hw hu

/--
The inversion of the transform: with `ω^(2ᵏ⁻¹) ≡ -1` and `ω ω' ≡ 1` modulo `F`, transforming
`z` by `ω` and the result by `ω'` gives `2ᵏ z`, modulo `F`.
-/
public theorem inverse_mod (w w' F k : Nat) (hk : 1 ≤ k) (hw : (w ^ 2 ^ (k - 1) + 1) % F = 0)
    (hww : (w * w') % F = 1 % F) (z : Nat → Nat) (l : Nat) (hl : l < 2 ^ k) :
    sumRange (fun j => sumRange (fun i => z i * w ^ (i * j)) (2 ^ k) * w' ^ (j * l)) (2 ^ k) % F =
      (2 ^ k * z l) % F := by
  -- `Σⱼ (Σᵢ zᵢ ωⁱʲ) ω'ʲˡ = Σᵢ zᵢ Σⱼ (ωⁱ ω'ˡ)ʲ`.
  have e : sumRange (fun j => sumRange (fun i => z i * w ^ (i * j)) (2 ^ k) * w' ^ (j * l))
      (2 ^ k) = sumRange (fun i => z i * sumRange ((w ^ i * w' ^ l) ^ ·) (2 ^ k)) (2 ^ k) := by
    rw [sumRange_congr (g := fun j => sumRange (fun i => z i * (w ^ i * w' ^ l) ^ j) (2 ^ k))
      (fun j _ => by
        rw [sumRange_mul_right]
        exact sumRange_congr fun i _ => by
          rw [Nat.mul_pow, ← Nat.pow_mul, ← Nat.pow_mul, Nat.mul_comm l j]; grind),
      sumRange_comm]
    exact sumRange_congr fun i _ => by rw [sumRange_mul_left]
  rw [e]
  -- `ωᴷ ≡ 1`.
  have hK : (w ^ 2 ^ k) % F = 1 % F := by
    have := sq_of_neg_one hw
    rw [← Nat.pow_two, ← Nat.pow_mul,
      show 2 ^ (k - 1) * 2 = 2 ^ k by rw [← Nat.pow_succ]; congr 1; lia] at this
    exact this
  -- `ωⁿ ω'ⁿ ≡ 1`.
  have hpow : ∀ n, (w ^ n * w' ^ n) % F = 1 % F := fun n => by
    rw [← Nat.mul_pow, Nat.pow_mod, hww, ← Nat.pow_mod, Nat.one_pow]
  rw [sumRange_single_mod hl (fun i hi hil => ?_)]
  · -- At `i = l`, every term is `1`.
    rw [Nat.mul_mod, sumRange_mod (g := fun _ => 1) (fun j _ => by
      rw [Nat.pow_mod, hpow l, ← Nat.pow_mod, Nat.one_pow]), ← Nat.mul_mod]
    have : sumRange (fun _ => 1) (2 ^ k) = 2 ^ k := by
      generalize 2 ^ k = K
      induction K with
      | zero => rfl
      | succ K ih => rw [sumRange_succ, ih]
    rw [this, Nat.mul_comm]
  · -- Elsewhere, `ωⁱ ω'ˡ ≡ ωᵈ` with `0 < d < 2ᵏ`, whose geometric sum vanishes.
    have hd : 0 < (i + 2 ^ k - l) % 2 ^ k := by
      rcases Nat.lt_or_ge i l with h | h
      · rw [Nat.mod_eq_of_lt (by lia)]; lia
      · rw [show i + 2 ^ k - l = (i - l) + 2 ^ k by lia, Nat.add_mod_right,
          Nat.mod_eq_of_lt (by lia)]
        lia
    generalize hdd : (i + 2 ^ k - l) % 2 ^ k = d at hd
    have hdk : d < 2 ^ k := by rw [← hdd]; exact Nat.mod_lt _ (Nat.two_pow_pos k)
    -- `d + l = i + 2ᵏ c`.
    have hdl : ∃ c, d + l = i + 2 ^ k * c := by
      rcases Nat.lt_or_ge i l with h | h
      · refine ⟨1, ?_⟩
        rw [← hdd, Nat.mod_eq_of_lt (by lia)]; lia
      · refine ⟨0, ?_⟩
        rw [← hdd, show i + 2 ^ k - l = (i - l) + 2 ^ k by lia, Nat.add_mod_right,
          Nat.mod_eq_of_lt (by lia)]
        lia
    obtain ⟨c, hc⟩ := hdl
    have hx : (w ^ i * w' ^ l) % F = (w ^ d) % F := by
      -- `ωᵈ ≡ ωᵈ (ωˡ ω'ˡ) = ω^(d + l) ω'ˡ ≡ ωⁱ ω'ˡ`.
      have h₁ : (w ^ d) % F = (w ^ d * (w ^ l * w' ^ l)) % F := by
        rw [Nat.mul_mod (w ^ d), hpow l, ← Nat.mul_mod, Nat.mul_one]
      have h₂ : w ^ d * (w ^ l * w' ^ l) = w ^ i * (w ^ 2 ^ k) ^ c * w' ^ l := by
        rw [← Nat.mul_assoc, ← Nat.pow_add, hc, Nat.pow_add, Nat.pow_mul]
      have hKc : ((w ^ 2 ^ k) ^ c) % F = 1 % F := by
        rw [Nat.pow_mod, hK, ← Nat.pow_mod, Nat.one_pow]
      have h₃ : (w ^ i * (w ^ 2 ^ k) ^ c * w' ^ l) % F = (w ^ i * w' ^ l) % F := by
        rw [show w ^ i * (w ^ 2 ^ k) ^ c * w' ^ l = (w ^ 2 ^ k) ^ c * (w ^ i * w' ^ l) by
          rw [Nat.mul_comm (w ^ i), Nat.mul_assoc], Nat.mul_mod, hKc, ← Nat.mul_mod, Nat.one_mul]
      rw [h₁, h₂, h₃]
    obtain ⟨s, hs, hroot⟩ := exists_pow_two_neg_one hw hd hdk
    have hsum : sumRange ((w ^ i * w' ^ l) ^ ·) (2 ^ k) % F = 0 := by
      rw [sumRange_mod (g := ((w ^ d) ^ ·)) (fun j _ => by
        rw [Nat.pow_mod, hx, ← Nat.pow_mod])]
      exact sumRange_pow_two_mod hs hroot
    rw [Nat.mul_mod, hsum, Nat.mul_zero, Nat.zero_mod]

end MPN.FFT
