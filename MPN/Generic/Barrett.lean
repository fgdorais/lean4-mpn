/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import MPN.Generic.Ops

/-!
# Division by a reciprocal, at any base

Barrett's division of `x` by an `n`-limb divisor `d` with `μ ≈ B²ⁿ / d`: the quotient estimate
`q = ⌊⌊x / Bⁿ⁻¹⌋ μ / Bⁿ⁺¹⌋` costs one product, the remainder `x - q d` another, and a good `μ`
leaves `q` at most a few units below the quotient. Longer dividends are divided `n` limbs at a
time (`divBlocks`). The reciprocal comes from Newton's iteration on the top half of `d`
(`recip`), at about the cost of a product.

None of the estimates needs a proof: `fixQuot` checks every quotient estimate exactly against
`x = q d + r` with `0 ≤ r < d`, corrects it a few units up or down, and falls back to the slow
division of `NatOps` when it is further off. The specifications therefore hold for any `μ`;
the quality of `μ` only decides how fast they are met.

`divMuW` saves part of the remainder's product. When `d μ ≤ B²ⁿ < d (μ + 5)` for a normalized `d`,
the remainder `x - q d` is less than `7 d`, so it is its residue modulo `B^N - 1` for `N > n`, which
`mulMod`, a wrapped product, computes faster (`barrettW`). That bound on `μ` is checked rather than
assumed: `recipW` makes the last Newton step itself, and the size of its error term
`e = B^(n+h) - d μₕ` bounds the error of the result whatever `μₕ` (`recipW_spec`). When the check
fails, `divMuW` is `divMu`.
-/

namespace MPN

/-! ## Inequalities of the checked reciprocal -/

/-- The Barrett estimate is at most 6 below the quotient, for a good reciprocal. -/
private theorem barrett_bound {P n x d μ : Nat} (hP : 2 ≤ P) (hn : 1 ≤ n) (hnorm : P ^ n ≤ 2 * d)
    (hA : d * μ ≤ P ^ (2 * n)) (hB : P ^ (2 * n) < d * (μ + 5)) (hx : x < P ^ (2 * n)) :
    x / P ^ (n - 1) * μ / P ^ (n + 1) * d ≤ x ∧
      x < (x / P ^ (n - 1) * μ / P ^ (n + 1) + 7) * d := by
  generalize hS : P ^ (n - 1) = S
  generalize hT : P ^ (n + 1) = T
  generalize hU : P ^ (2 * n) = U at hA hB hx
  have hST : S * T = U := by
    rw [← hS, ← hT, ← hU, ← Nat.pow_add]; congr 1; lia
  have hS0 : 0 < S := by rw [← hS]; exact Nat.pow_pos (by lia)
  have hT0 : 0 < T := by rw [← hT]; exact Nat.pow_pos (by lia)
  have hSd : S ≤ d := by
    have : P ^ n = P * S := by rw [← hS, ← Nat.pow_succ']; congr 1; lia
    have := Nat.mul_le_mul_right S hP
    lia
  have hd0 : 0 < d := by lia
  generalize hx₁ : x / S = x₁
  have e₁ : x₁ * S ≤ x := by rw [← hx₁]; exact Nat.div_mul_le_self x S
  have e₂ : x < (x₁ + 1) * S := by
    have := Nat.lt_mul_div_succ x hS0; rw [hx₁, Nat.mul_comm] at this; exact this
  generalize hq : x₁ * μ / T = q
  have f₁ : q * T ≤ x₁ * μ := by rw [← hq]; exact Nat.div_mul_le_self _ T
  have f₂ : x₁ * μ < (q + 1) * T := by
    have := Nat.lt_mul_div_succ (x₁ * μ) hT0
    rw [hq] at this; rw [Nat.mul_comm (q + 1) T]; exact this
  constructor
  · -- `q d U ≤ x U`.
    have g₁ : q * d * U ≤ x * U := by
      calc q * d * U = q * T * (d * S) := by rw [← hST]; grind
        _ ≤ x₁ * μ * (d * S) := Nat.mul_le_mul_right _ f₁
        _ = x₁ * S * (d * μ) := by grind
        _ ≤ x₁ * S * U := Nat.mul_le_mul_left _ hA
        _ ≤ x * U := Nat.mul_le_mul_right _ e₁
    exact Nat.le_of_mul_le_mul_right g₁ (by lia)
  · -- `x U < ((q + 1) d + S + 5 d) U`.
    have g₁ : x * U ≤ x * (d * μ) + 5 * (x * d) := by
      calc x * U ≤ x * (d * (μ + 5)) := Nat.mul_le_mul_left x (Nat.le_of_lt hB)
        _ = x * (d * μ) + 5 * (x * d) := by grind
    have g₂ : x * (d * μ) < (q + 1) * d * U + S * U := by
      calc x * (d * μ) ≤ (x₁ + 1) * S * (d * μ) := Nat.mul_le_mul_right _ (Nat.le_of_lt e₂)
        _ = x₁ * μ * (d * S) + S * (d * μ) := by grind
        _ < (q + 1) * T * (d * S) + S * (d * μ) :=
          Nat.add_lt_add_right (Nat.mul_lt_mul_of_pos_right f₂ (Nat.mul_pos hd0 hS0)) _
        _ ≤ (q + 1) * T * (d * S) + S * U := Nat.add_le_add_left (Nat.mul_le_mul_left _ hA) _
        _ = (q + 1) * d * U + S * U := by rw [← hST]; grind
    have g₃ : 5 * (x * d) < 5 * d * U := by
      have := Nat.mul_lt_mul_of_pos_right hx hd0
      lia
    have g₄ : x * U < ((q + 1) * d + S + 5 * d) * U := by
      rw [Nat.add_mul, Nat.add_mul]
      lia
    have := Nat.lt_of_mul_lt_mul_right g₄
    rw [Nat.add_mul]
    lia

/-- The floors of the Newton correction `δ = ⌊μₕ ⌊e / Bᵗ⌋ / Bʰ⁺²⌋`, with `t + h + 2 = 2 h`. -/
private theorem newton_floors {P t h μh e : Nat} (hP : 2 ≤ P) (ht : t + 2 = h) :
    μh * (e / P ^ t) / P ^ (h + 2) * P ^ (2 * h) ≤ μh * e ∧
      μh * e < (μh * (e / P ^ t) / P ^ (h + 2) + 1) * P ^ (2 * h) + μh * P ^ t := by
  have hU : P ^ (2 * h) = P ^ (h + 2) * P ^ t := by rw [← Nat.pow_add]; congr 1; lia
  have hT0 : 0 < P ^ t := Nat.pow_pos (by lia)
  have hH0 : 0 < P ^ (h + 2) := Nat.pow_pos (by lia)
  generalize hE : e / P ^ t = E at *
  have e₁ : E * P ^ t ≤ e := by rw [← hE]; exact Nat.div_mul_le_self e _
  have e₂ : e < (E + 1) * P ^ t := by
    have := Nat.lt_mul_div_succ e hT0; rw [hE] at this; rw [Nat.mul_comm (E + 1)]; exact this
  generalize hδ : μh * E / P ^ (h + 2) = δ
  have f₁ : δ * P ^ (h + 2) ≤ μh * E := by rw [← hδ]; exact Nat.div_mul_le_self _ _
  have f₂ : μh * E < (δ + 1) * P ^ (h + 2) := by
    have := Nat.lt_mul_div_succ (μh * E) hH0; rw [hδ] at this
    rw [Nat.mul_comm (δ + 1)]; exact this
  rw [hU]
  generalize P ^ (h + 2) = H at *
  generalize P ^ t = T at *
  constructor
  · calc δ * (H * T) = δ * H * T := by rw [Nat.mul_assoc]
      _ ≤ μh * E * T := Nat.mul_le_mul_right _ f₁
      _ = μh * (E * T) := by rw [Nat.mul_assoc]
      _ ≤ μh * e := Nat.mul_le_mul_left _ e₁
  · calc μh * e ≤ μh * ((E + 1) * T) := Nat.mul_le_mul_left _ (Nat.le_of_lt e₂)
      _ = μh * E * T + μh * T := by grind
      _ < (δ + 1) * H * T + μh * T :=
          Nat.add_lt_add_right (Nat.mul_lt_mul_of_pos_right f₂ hT0) _
      _ = (δ + 1) * (H * T) + μh * T := by rw [Nat.mul_assoc]

/-- The Newton step when `d μₕ ≤ B^(n+h)`: the reciprocal from below, within 4. -/
private theorem newton_pos {P n k h d μh e : Nat} (hP : 2 ≤ P) (hkh : k + h = n)
    (h2 : n + 2 ≤ 2 * h) (hh : 2 ≤ h) (hnorm : P ^ n ≤ 2 * d) (he : d * μh + e = P ^ (n + h))
    (heb : e < P ^ (n + 1)) :
    d * (μh * P ^ k + μh * (e / P ^ (h - 2)) / P ^ (h + 2)) ≤ P ^ (2 * n) ∧
      P ^ (2 * n) < d * (μh * P ^ k + μh * (e / P ^ (h - 2)) / P ^ (h + 2) + 4) := by
  obtain ⟨f₁, f₂⟩ := newton_floors (μh := μh) (e := e) hP (show h - 2 + 2 = h by lia)
  generalize μh * (e / P ^ (h - 2)) / P ^ (h + 2) = δ at *
  have hQ : P ^ (n + h) = P ^ (2 * h) * P ^ k := by rw [← Nat.pow_add]; congr 1; lia
  have h2n : P ^ (2 * n) = P ^ (n + h) * P ^ k := by rw [← Nat.pow_add]; congr 1; lia
  have hQt : P ^ (n + h) * P ^ (h - 2) = P ^ (2 * h) * P ^ (n - 2) := by
    rw [← Nat.pow_add, ← Nat.pow_add]; congr 1; lia
  have hn2 : P ^ (n - 2) ≤ d := by
    have : P ^ n = P ^ (n - 2) * (P * P) := by
      rw [← Nat.pow_two, ← Nat.pow_add]; congr 1; lia
    have := Nat.mul_le_mul_left (P ^ (n - 2)) (Nat.mul_le_mul hP hP)
    lia
  have he2 : e * e < P ^ (2 * h) * (2 * d) := by
    have h₁ : e * e < P ^ (n + 1) * P ^ (n + 1) := Nat.mul_lt_mul'' heb heb
    have h₂ : P ^ (n + 1) * P ^ (n + 1) ≤ P ^ (2 * h) * P ^ n := by
      rw [← Nat.pow_add, ← Nat.pow_add]; exact Nat.pow_le_pow_right (by lia) (by lia)
    have h₃ := Nat.mul_le_mul_left (P ^ (2 * h)) hnorm
    lia
  have hU0 : 0 < P ^ (2 * h) := Nat.pow_pos (by lia)
  rw [h2n, ← he]
  generalize P ^ (2 * h) = U at *
  generalize P ^ k = K at *
  generalize P ^ (n + h) = Q at *
  generalize P ^ (h - 2) = T at *
  generalize P ^ (n - 2) = R at *
  subst hQ
  -- `d δ U ≤ d μₕ e ≤ Q e = U K e`, and `U K e < U (d (δ + 1) + d + 2 d)`.
  have hA : d * δ * U ≤ U * K * e := by
    calc d * δ * U = d * (δ * U) := by rw [Nat.mul_assoc]
      _ ≤ d * (μh * e) := Nat.mul_le_mul_left _ f₁
      _ = (d * μh) * e := by rw [Nat.mul_assoc]
      _ ≤ (d * μh + e) * e := Nat.mul_le_mul_right _ (Nat.le_add_right _ _)
      _ = U * K * e := by rw [he]
  have hdK : d * δ ≤ K * e := by
    have : d * δ * U ≤ K * e * U := by rw [Nat.mul_comm (K * e), ← Nat.mul_assoc]; exact hA
    exact Nat.le_of_mul_le_mul_right this hU0
  have hB : U * K * e < U * (d * (δ + 1) + d + 2 * d) := by
    have g₁ : d * (μh * e) < d * ((δ + 1) * U + μh * T) := Nat.mul_lt_mul_of_pos_left f₂ (by lia)
    have g₂ : d * μh * T ≤ U * d := by
      calc d * μh * T ≤ (d * μh + e) * T := Nat.mul_le_mul_right _ (Nat.le_add_right _ _)
        _ = U * K * T := by rw [he]
        _ = U * R := hQt
        _ ≤ U * d := Nat.mul_le_mul_left _ hn2
    have g₃ : d * μh * e + e * e = U * K * e := by rw [← Nat.add_mul, he]
    have g₄ : d * ((δ + 1) * U + μh * T) = d * (δ + 1) * U + d * μh * T := by grind
    have g₅ : U * (d * (δ + 1) + d + 2 * d) = d * (δ + 1) * U + U * d + U * (2 * d) := by grind
    rw [Nat.mul_assoc d μh e] at g₃
    lia
  constructor
  · calc d * (μh * K + δ) = d * μh * K + d * δ := by grind
      _ ≤ d * μh * K + K * e := Nat.add_le_add_left hdK _
      _ = (d * μh + e) * K := by grind
  · have hKe : K * e < d * δ + 4 * d := by
      have : K * e * U < (d * (δ + 1) + d + 2 * d) * U := by
        rw [Nat.mul_comm (K * e), ← Nat.mul_assoc, Nat.mul_comm _ U]; exact hB
      have := Nat.lt_of_mul_lt_mul_right this
      lia
    calc (d * μh + e) * K = d * μh * K + K * e := by grind
      _ < d * μh * K + (d * δ + 4 * d) := Nat.add_lt_add_left hKe _
      _ = d * (μh * K + δ + 4) := by grind

/-- The Newton step when `d μₕ > B^(n+h)`: the reciprocal, less one, from below, within 5. -/
private theorem newton_neg {P n k h d μh e : Nat} (hP : 2 ≤ P) (hkh : k + h = n)
    (h2 : n + 2 ≤ 2 * h) (hh : 2 ≤ h) (hnorm : P ^ n ≤ 2 * d) (he : d * μh = P ^ (n + h) + e)
    (heb : e < P ^ (n + 1))
    (hc : μh * (e / P ^ (h - 2)) / P ^ (h + 2) + 2 ≤ μh * P ^ k) :
    d * (μh * P ^ k - (μh * (e / P ^ (h - 2)) / P ^ (h + 2) + 1) - 1) ≤ P ^ (2 * n) ∧
      P ^ (2 * n) < d * (μh * P ^ k - (μh * (e / P ^ (h - 2)) / P ^ (h + 2) + 1) - 1 + 5) := by
  obtain ⟨f₁, f₂⟩ := newton_floors (μh := μh) (e := e) hP (show h - 2 + 2 = h by lia)
  generalize μh * (e / P ^ (h - 2)) / P ^ (h + 2) = δ at *
  have hQ : P ^ (n + h) = P ^ (2 * h) * P ^ k := by rw [← Nat.pow_add]; congr 1; lia
  have h2n : P ^ (2 * n) = P ^ (n + h) * P ^ k := by rw [← Nat.pow_add]; congr 1; lia
  have hQt : P ^ (n + h) * P ^ (h - 2) = P ^ (2 * h) * P ^ (n - 2) := by
    rw [← Nat.pow_add, ← Nat.pow_add]; congr 1; lia
  have hn2 : 2 * P ^ (n - 2) ≤ d := by
    have : P ^ n = P ^ (n - 2) * (P * P) := by
      rw [← Nat.pow_two, ← Nat.pow_add]; congr 1; lia
    have := Nat.mul_le_mul_left (P ^ (n - 2)) (Nat.mul_le_mul hP hP)
    lia
  have heQ : e ≤ P ^ (n + h) := Nat.le_of_lt (Nat.lt_of_lt_of_le heb
    (Nat.pow_le_pow_right (by lia) (by lia)))
  have he2 : e * e < P ^ (2 * h) * (2 * d) := by
    have h₁ : e * e < P ^ (n + 1) * P ^ (n + 1) := Nat.mul_lt_mul'' heb heb
    have h₂ : P ^ (n + 1) * P ^ (n + 1) ≤ P ^ (2 * h) * P ^ n := by
      rw [← Nat.pow_add, ← Nat.pow_add]; exact Nat.pow_le_pow_right (by lia) (by lia)
    have h₃ := Nat.mul_le_mul_left (P ^ (2 * h)) hnorm
    lia
  have hU0 : 0 < P ^ (2 * h) := Nat.pow_pos (by lia)
  rw [h2n]
  generalize P ^ (2 * h) = U at *
  generalize P ^ k = K at *
  generalize P ^ (n + h) = Q at *
  generalize P ^ (h - 2) = T at *
  generalize P ^ (n - 2) = R at *
  subst hQ
  have g₀ : d * μh * e = U * K * e + e * e := by rw [he]; grind
  constructor
  · -- `K e ≤ d (δ + 2)`.
    have hKe : K * e ≤ d * (δ + 2) := by
      have g₁ : d * (μh * e) < d * ((δ + 1) * U + μh * T) :=
        Nat.mul_lt_mul_of_pos_left f₂ (by lia)
      have g₂ : d * μh * T ≤ U * d := by
        calc d * μh * T = (U * K + e) * T := by rw [he]
          _ ≤ (U * K + U * K) * T := Nat.mul_le_mul_right _ (Nat.add_le_add_left heQ _)
          _ = 2 * (U * K * T) := by grind
          _ = 2 * (U * R) := by rw [hQt]
          _ ≤ U * d := by
            have := Nat.mul_le_mul_left U hn2
            grind
      have g₃ : d * ((δ + 1) * U + μh * T) = d * (δ + 1) * U + d * μh * T := by grind
      rw [← Nat.mul_assoc] at g₁
      have : K * e * U < (d * (δ + 2)) * U := by
        have e₁ : K * e * U = U * K * e := by grind
        have e₂ : d * (δ + 2) * U = d * (δ + 1) * U + U * d := by grind
        lia
      exact Nat.le_of_lt (Nat.lt_of_mul_lt_mul_right this)
    have e₁ : d * (μh * K - (δ + 1) - 1) = d * μh * K - d * (δ + 2) := by
      rw [Nat.sub_sub, Nat.mul_sub, ← Nat.mul_assoc]
    rw [e₁, he]
    have : (U * K + e) * K = U * K * K + K * e := by grind
    lia
  · -- `d δ < K e + 2 d`.
    have hdδ : d * δ < K * e + 2 * d := by
      have g₁ : d * (δ * U) ≤ d * (μh * e) := Nat.mul_le_mul_left _ f₁
      have : d * δ * U < (K * e + 2 * d) * U := by
        have e₁ : d * (δ * U) = d * δ * U := by rw [Nat.mul_assoc]
        have e₂ : (K * e + 2 * d) * U = U * K * e + U * (2 * d) := by grind
        rw [← Nat.mul_assoc] at g₁
        lia
      exact Nat.lt_of_mul_lt_mul_right this
    have e₁ : μh * K - (δ + 1) - 1 + 5 = μh * K - δ + 3 := by lia
    rw [e₁, Nat.mul_add, Nat.mul_sub, ← Nat.mul_assoc, he]
    have : (U * K + e) * K = U * K * K + K * e := by grind
    lia

/-- One fold modulo `P - 1`: `x ≡ x % P + x / P`. -/
private theorem fold_mod {x P : Nat} (hP : 2 ≤ P) : (x % P + x / P) % (P - 1) = x % (P - 1) := by
  have h := Nat.div_add_mod x P
  generalize x / P = q at *
  generalize x % P = r at *
  subst h
  rw [show P * q + r = (r + q) + q * (P - 1) by
    rw [Nat.mul_sub, Nat.mul_one, Nat.mul_comm q P]
    have : q ≤ P * q := Nat.le_mul_of_pos_left _ (by lia)
    lia, Nat.add_mul_mod_self_right]

/-- `a - b` from the residues of `a` and `b`, when it is less than the modulus. -/
private theorem sub_of_mod {a b M : Nat} (hba : b ≤ a) (hlt : a - b < M) :
    a - b = if b % M ≤ a % M then a % M - b % M else a % M + M - b % M := by
  have hM : 0 < M := by lia
  have ha := Nat.div_add_mod a M
  have hb := Nat.div_add_mod b M
  have hra := Nat.mod_lt a hM
  have hrb := Nat.mod_lt b hM
  generalize a / M = qa at *
  generalize b / M = qb at *
  generalize a % M = ra at *
  generalize b % M = rb at *
  subst ha hb
  split
  · -- `qa = qb`.
    have : qa ≤ qb := by
      rcases Nat.lt_or_ge qb qa with h | h
      · have := Nat.mul_le_mul_left M (show qb + 1 ≤ qa by lia)
        rw [Nat.mul_add, Nat.mul_one] at this; lia
      · exact h
    have : qb ≤ qa := by
      rcases Nat.lt_or_ge qa qb with h | h
      · have := Nat.mul_le_mul_left M (show qa + 1 ≤ qb by lia)
        rw [Nat.mul_add, Nat.mul_one] at this; lia
      · exact h
    have : qa = qb := by lia
    subst this; lia
  · -- `qa = qb + 1`.
    have h₁ : qb + 1 ≤ qa := by
      rcases Nat.lt_or_ge qb qa with h | h
      · exact h
      · have := Nat.mul_le_mul_left M h; lia
    have h₂ : qa ≤ qb + 1 := by
      rcases Nat.lt_or_ge (qb + 1) qa with h | h
      · have := Nat.mul_le_mul_left M (show qb + 2 ≤ qa by lia)
        rw [Nat.mul_add] at this; lia
      · exact h
    have : qa = qb + 1 := by lia
    subst this
    rw [Nat.mul_add, Nat.mul_one]; lia

namespace NatOps

variable {α : Type} (o : NatOps α)

/-! ## Correcting a quotient -/

/--
The quotient and remainder of `x` by `d` from a quotient `q` and the remainder `r = x - q d`
when `q` may be too small: `q` goes up by one while `r ≥ d`, at most `fuel` times before the
slow division.
-/
def fixUp (x d q r : α) : Nat → α × α
  | 0 => if o.le d r then o.divRem x d else (q, r)
  | fuel + 1 => if o.le d r then fixUp x d (o.add q o.one) (o.sub r d) fuel else (q, r)

/--
The quotient and remainder of `x` by `d` from a quotient `q` that is too large, with
`q d = x + t` and `t > 0`: `q` goes down by one while `t > d`, at most `fuel` times before the
slow division.
-/
def fixDown (x d q t : α) : Nat → α × α
  | 0 => if o.le t d then (o.sub q o.one, o.sub d t) else o.divRem x d
  | fuel + 1 => if o.le t d then (o.sub q o.one, o.sub d t)
      else fixDown x d (o.sub q o.one) (o.sub t d) fuel

/--
The quotient and remainder of `x` by `d`, from an estimate `q` of the quotient: one product
`q d`, then `fixUp` or `fixDown`.
-/
public def fixQuot (x d q : α) (fuel : Nat) : α × α :=
  let p := o.mul q d
  if o.le p x then o.fixUp x d q (o.sub x p) fuel else o.fixDown x d q (o.sub p x) fuel

/-- The specification of a quotient and remainder: `x = q d + r` with `r < d`. -/
@[expose] public def IsDivRem (x d : Nat) (qr : α × α) : Prop :=
  x = o.val qr.1 * d + o.val qr.2 ∧ o.val qr.2 < d

theorem isDivRem_divRem (x d : α) (hd : 0 < o.val d) :
    o.IsDivRem (o.val x) (o.val d) (o.divRem x d) := by
  obtain ⟨h₁, h₂⟩ := o.val_divRem x d (by lia)
  refine ⟨?_, ?_⟩
  · rw [h₁, h₂]; exact (Nat.div_add_mod' _ _).symm
  · rw [h₂]; exact Nat.mod_lt _ hd

theorem fixUp_spec (x d : α) (hd : 0 < o.val d) :
    ∀ fuel (q r : α), o.val x = o.val q * o.val d + o.val r →
      o.IsDivRem (o.val x) (o.val d) (o.fixUp x d q r fuel) := by
  intro fuel
  induction fuel with
  | zero =>
    intro q r h
    simp only [fixUp]
    split
    · exact o.isDivRem_divRem x d hd
    · rename_i hn
      rw [o.le_iff] at hn
      exact ⟨h, by lia⟩
  | succ fuel ih =>
    intro q r h
    simp only [fixUp]
    split
    · rename_i hle
      rw [o.le_iff] at hle
      apply ih
      rw [o.val_add, o.val_one, o.val_sub _ _ hle, Nat.add_mul, Nat.one_mul]
      lia
    · rename_i hn
      rw [o.le_iff] at hn
      exact ⟨h, by lia⟩

theorem fixDown_spec (x d : α) (hd : 0 < o.val d) :
    ∀ fuel (q t : α), o.val q * o.val d = o.val x + o.val t → 0 < o.val t →
      o.IsDivRem (o.val x) (o.val d) (o.fixDown x d q t fuel) := by
  intro fuel
  induction fuel with
  | zero =>
    intro q t h ht
    simp only [fixDown]
    split
    · rename_i hle
      rw [o.le_iff] at hle
      have hq : 1 ≤ o.val q := by
        rcases Nat.eq_zero_or_pos (o.val q) with h0 | h0
        · rw [h0, Nat.zero_mul] at h; lia
        · exact h0
      refine ⟨?_, ?_⟩
      · rw [o.val_sub _ _ (by rw [o.val_one]; exact hq), o.val_one, o.val_sub _ _ hle,
          Nat.sub_mul, Nat.one_mul]
        have : o.val d ≤ o.val q * o.val d := Nat.le_mul_of_pos_left _ hq
        lia
      · rw [o.val_sub _ _ hle]; lia
    · exact o.isDivRem_divRem x d hd
  | succ fuel ih =>
    intro q t h ht
    simp only [fixDown]
    have hq : 1 ≤ o.val q := by
      rcases Nat.eq_zero_or_pos (o.val q) with h0 | h0
      · rw [h0, Nat.zero_mul] at h; lia
      · exact h0
    split
    · rename_i hle
      rw [o.le_iff] at hle
      refine ⟨?_, ?_⟩
      · rw [o.val_sub _ _ (by rw [o.val_one]; exact hq), o.val_one, o.val_sub _ _ hle,
          Nat.sub_mul, Nat.one_mul]
        have : o.val d ≤ o.val q * o.val d := Nat.le_mul_of_pos_left _ hq
        lia
      · rw [o.val_sub _ _ hle]; lia
    · rename_i hn
      rw [o.le_iff] at hn
      apply ih
      · rw [o.val_sub _ _ (by rw [o.val_one]; exact hq), o.val_one, o.val_sub _ _ (by lia),
          Nat.sub_mul, Nat.one_mul]
        have : o.val d ≤ o.val q * o.val d := Nat.le_mul_of_pos_left _ hq
        lia
      · rw [o.val_sub _ _ (by lia)]; lia

public theorem fixQuot_spec (x d q : α) (fuel : Nat) (hd : 0 < o.val d) :
    o.IsDivRem (o.val x) (o.val d) (o.fixQuot x d q fuel) := by
  unfold fixQuot
  dsimp only
  split
  · rename_i hle
    rw [o.le_iff, o.val_mul] at hle
    apply o.fixUp_spec x d hd
    rw [o.val_sub _ _ (by rw [o.val_mul]; exact hle), o.val_mul]
    lia
  · rename_i hn
    rw [o.le_iff, o.val_mul] at hn
    apply o.fixDown_spec x d hd
    · rw [o.val_sub _ _ (by rw [o.val_mul]; lia), o.val_mul]; lia
    · rw [o.val_sub _ _ (by rw [o.val_mul]; lia), o.val_mul]; lia

/-! ## Barrett's division -/

/--
`x` by the `n`-limb `d` with the reciprocal `μ ≈ B²ⁿ / d`, for `x < B²ⁿ`: the estimate
`⌊⌊x / Bⁿ⁻¹⌋ μ / Bⁿ⁺¹⌋`, corrected by `fixQuot`.
-/
public def barrettStep (x d μ : α) (n : Nat) : α × α :=
  o.fixQuot x d (o.hi (n + 1) (o.mul (o.hi (n - 1) x) μ)) 2

public theorem barrettStep_spec (x d μ : α) (n : Nat) (hd : 0 < o.val d) :
    o.IsDivRem (o.val x) (o.val d) (o.barrettStep x d μ n) :=
  o.fixQuot_spec _ _ _ _ hd

/--
`a` by the `n`-limb `d` with the reciprocal `μ`, `n` limbs of quotient at a time from the top:
the quotient of the part above the low `n` limbs, then one `barrettStep` on its remainder
followed by those limbs.
-/
public def divBlocks (d μ : α) (n : Nat) (hn : 0 < n) (a : α) : α × α :=
  if o.size a ≤ 2 * n then o.barrettStep a d μ n
  else
    let t := divBlocks d μ n hn (o.hi n a)
    let s := o.barrettStep (o.add (o.shl n t.2) (o.lo n a)) d μ n
    (o.add (o.shl n t.1) s.1, s.2)
termination_by o.size a
decreasing_by rw [o.size_hi]; lia

public theorem divBlocks_spec (d μ : α) (n : Nat) (hn : 0 < n) (hd : 0 < o.val d) (a : α) :
    o.IsDivRem (o.val a) (o.val d) (o.divBlocks d μ n hn a) := by
  induction a using WellFounded.induction (InvImage.wf o.size Nat.lt_wfRel.wf) with
  | h a ih =>
    unfold divBlocks
    split
    · exact o.barrettStep_spec _ _ _ _ hd
    · rename_i hsz
      dsimp only
      obtain ⟨ht₁, ht₂⟩ := ih (o.hi n a) (by
        show o.size (o.hi n a) < o.size a
        rw [o.size_hi]; lia)
      generalize o.divBlocks d μ n hn (o.hi n a) = t at ht₁ ht₂
      obtain ⟨hs₁, hs₂⟩ := o.barrettStep_spec (o.add (o.shl n t.2) (o.lo n a)) d μ n hd
      generalize o.barrettStep (o.add (o.shl n t.2) (o.lo n a)) d μ n = s at hs₁ hs₂
      refine ⟨?_, hs₂⟩
      rw [o.val_add, o.val_lo] at hs₁
      rw [o.val_shl] at hs₁
      rw [o.val_hi] at ht₁
      show o.val a = o.val (o.add (o.shl n t.1) s.1) * o.val d + o.val s.2
      rw [o.val_add, o.val_shl]
      have hsplit := Nat.div_add_mod (o.val a) (o.B ^ n)
      generalize o.val a / o.B ^ n = A at hsplit ht₁
      generalize o.val a % o.B ^ n = L at hsplit hs₁
      generalize o.B ^ n = P at *
      rw [← hsplit, ht₁]
      generalize o.val t.1 = T₁ at *
      generalize o.val t.2 = T₂ at *
      generalize o.val s.1 = S₁ at *
      generalize o.val s.2 = S₂ at *
      generalize o.val d = D at *
      grind

/-! ## The reciprocal -/

/--
An approximation of `B²ⁿ / d` for the `n`-limb `d`, by Newton's iteration: the reciprocal
`μₕ` of the top `h = ⌈n / 2⌉ + 1` limbs, then one step from `μ₀ = μₕ Bᵏ`, `k = n - h`:
`μ₀ + μ₀ (B²ⁿ - d μ₀) / B²ⁿ = μₕ Bᵏ + μₕ e / B²ⁿ⁻²ᵏ` with `e = B²ⁿ⁻ᵏ - d μₕ`, an `n` by `h`
product. `e` is about `B²ⁿ⁻ᵏ⁻ʰ`, and only its limbs from `t = 2n - 2k - h - 2` on enter the
correction, an `h` by `k` product. The step squares the relative error of `μ₀`, about `B⁻ʰ`, so
the error of the result is about `Bⁿ⁻²ʰ ≤ B⁻²` units: the extra limb of `h` keeps errors from
growing from one level to the next. Four limbs and fewer by the slow division.
-/
public def recip (d : α) : α :=
  let n := o.size d
  if hn : n ≤ 4 then (o.divRem (o.pow (2 * n)) d).1
  else
    let k := n - ((n + 1) / 2 + 1)
    let μₕ := recip (o.hi k d)
    let t := 2 * n - 2 * k - ((n + 1) / 2 + 1) - 2
    let Q := o.pow (2 * n - k)
    let p := o.mul d μₕ
    if o.le p Q then
      o.add (o.shl k μₕ) (o.hi (2 * n - 2 * k - t) (o.mul μₕ (o.hi t (o.sub Q p))))
    else
      o.sub (o.shl k μₕ)
        (o.add (o.hi (2 * n - 2 * k - t) (o.mul μₕ (o.hi t (o.sub p Q)))) o.one)
termination_by o.size d
decreasing_by rw [o.size_hi]; lia

/-- `(a / d, a % d)` by Barrett's division with Newton's reciprocal, for `d ≠ 0`. -/
public def divMu (a d : α) : α × α :=
  if hn : 0 < o.size d then o.divBlocks d (o.recip d) (o.size d) hn a else o.divRem a d

public theorem divMu_spec (a d : α) (hd : 0 < o.val d) :
    o.val (o.divMu a d).1 = o.val a / o.val d ∧ o.val (o.divMu a d).2 = o.val a % o.val d := by
  have h : o.IsDivRem (o.val a) (o.val d) (o.divMu a d) := by
    unfold divMu
    split
    · exact o.divBlocks_spec _ _ _ _ hd a
    · exact o.isDivRem_divRem a d hd
  obtain ⟨h₁, h₂⟩ := h
  have hq : o.val a / o.val d = o.val (o.divMu a d).1 := by
    rw [h₁, Nat.add_comm, Nat.add_mul_div_right _ _ hd, Nat.div_eq_of_lt h₂, Nat.zero_add]
  have hr : o.val a % o.val d = o.val (o.divMu a d).2 := by
    rw [h₁, Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt h₂]
  exact ⟨hq.symm, hr.symm⟩

/-! ## Barrett's division with wrapped remainders

When the reciprocal is good, `d μ ≤ B²ⁿ < d (μ + 5)` for a normalized `d`, Barrett's estimate is at
most 6 below the quotient, so that the remainder `x - q d` is less than `7 d`: it is then its
residue modulo `B^N - 1` for `N > n`, and `mulMod` computes `q d` modulo `B^N - 1` faster than the
product. Whether the reciprocal is good is checked rather than proved: `recipW` makes the last
Newton step of `recip` itself, whose error term `e = B^(n+h) - d μₕ` shows how good its result is,
whatever `μₕ`; when `|e| < Bⁿ⁺¹`, the step gives `d μ ≤ B²ⁿ < d (μ + 5)`. Otherwise `divMuW` falls
back on `divMu`.
-/

/-- `x mod (B^N - 1)`: folds while `x ≥ Bᴺ`, at most `fuel` times before the slow division. -/
def foldM (N : Nat) : Nat → α → α
  | 0, x => (o.divRem x (o.sub (o.pow N) o.one)).2
  | fuel + 1, x =>
    if o.le (o.pow N) x then foldM N fuel (o.add (o.lo N x) (o.hi N x))
    else if o.le (o.sub (o.pow N) o.one) x then o.lo 0 x else x

theorem val_pow_sub_one (N : Nat) : o.val (o.sub (o.pow N) o.one) = o.B ^ N - 1 := by
  have := o.one_lt_B
  rw [o.val_sub _ _ (by rw [o.val_pow, o.val_one]; exact Nat.one_le_pow _ _ (by lia)), o.val_pow,
    o.val_one]

theorem val_foldM (N : Nat) (hN : 1 ≤ N) :
    ∀ fuel x, o.val (o.foldM N fuel x) = o.val x % (o.B ^ N - 1) := by
  have hB := o.one_lt_B
  have hP : 2 ≤ o.B ^ N := by
    have := Nat.pow_le_pow_left (show 2 ≤ o.B by lia) N
    have := Nat.pow_le_pow_right (show 0 < 2 by decide) hN
    simp at this; lia
  intro fuel
  induction fuel with
  | zero =>
    intro x
    rw [foldM, (o.val_divRem _ _ (by rw [o.val_pow_sub_one]; lia)).2, o.val_pow_sub_one]
  | succ fuel ih =>
    intro x
    rw [foldM]
    split
    · rw [ih, o.val_add, o.val_lo, o.val_hi]
      exact fold_mod hP
    · rename_i hlt
      rw [o.le_iff, o.val_pow] at hlt
      split
      · rename_i hge
        rw [o.le_iff, o.val_pow_sub_one] at hge
        rw [o.val_lo, Nat.pow_zero, Nat.mod_one, show o.val x = o.B ^ N - 1 by lia, Nat.mod_self]
      · rename_i hlt'
        rw [o.le_iff, o.val_pow_sub_one] at hlt'
        rw [Nat.mod_eq_of_lt (by lia)]

/--
The reciprocal of the `n`-limb `d`, less one, by the last Newton step of `recip` from `recip` of
the top `h = ⌈n / 2⌉ + 1` limbs of `d`, and whether the step's error term
`e = B^(n+h) - d μₕ` is below `Bⁿ⁺¹` and its subtractions are exact.
-/
public def recipW (d : α) : α × Bool :=
  let n := o.size d
  let h := (n + 1) / 2 + 1
  let k := n - h
  let μₕ := o.recip (o.hi k d)
  let Q := o.pow (n + h)
  let p := o.mul d μₕ
  if o.le p Q then
    let e := o.sub Q p
    let μ := o.add (o.shl k μₕ) (o.hi (h + 2) (o.mul μₕ (o.hi (h - 2) e)))
    (o.sub μ o.one, !o.le (o.pow (n + 1)) e && o.le o.one μ)
  else
    let e := o.sub p Q
    let c := o.add (o.hi (h + 2) (o.mul μₕ (o.hi (h - 2) e))) o.one
    (o.sub (o.sub (o.shl k μₕ) c) o.one,
      !o.le (o.pow (n + 1)) e && o.le (o.add c o.one) (o.shl k μₕ))

theorem le_false {x y : α} (h : o.le x y = false) : o.val y < o.val x := by
  have := o.le_iff x y
  rw [h] at this
  lia

public theorem recipW_spec (d : α) (hn : 2 ≤ o.size d)
    (hnorm : o.B ^ o.size d ≤ 2 * o.val d) (hok : (o.recipW d).2 = true) :
    o.val d * o.val (o.recipW d).1 ≤ o.B ^ (2 * o.size d) ∧
      o.B ^ (2 * o.size d) < o.val d * (o.val (o.recipW d).1 + 5) := by
  have hB : 2 ≤ o.B := o.one_lt_B
  unfold recipW at hok ⊢
  generalize hsz : o.size d = n at *
  dsimp only at hok ⊢
  generalize o.recip (o.hi (n - ((n + 1) / 2 + 1)) d) = μₕ at hok ⊢
  have hkh : n - ((n + 1) / 2 + 1) + ((n + 1) / 2 + 1) = n := by lia
  generalize hh : (n + 1) / 2 + 1 = h at hkh hok ⊢
  generalize hk : n - h = k at hkh hok ⊢
  have h2 : n + 2 ≤ 2 * h := by lia
  have hh2 : 2 ≤ h := by lia
  by_cases hle : o.le (o.mul d μₕ) (o.pow (n + h)) = true
  · simp only [hle, ↓reduceIte, Bool.and_eq_true, Bool.not_eq_true'] at hok ⊢
    obtain ⟨hok₁, hok₂⟩ := hok
    rw [o.le_iff, o.val_mul, o.val_pow] at hle
    have hsub := o.val_sub (o.pow (n + h)) (o.mul d μₕ) (by rw [o.val_mul, o.val_pow]; exact hle)
    rw [o.val_mul, o.val_pow] at hsub
    have he := o.le_false hok₁
    rw [hsub, o.val_pow] at he
    rw [o.le_iff, o.val_one] at hok₂
    rw [o.val_sub _ _ (by rw [o.val_one]; exact hok₂), o.val_one]
    simp only [o.val_add, o.val_shl, o.val_hi, o.val_mul, hsub] at hok₂ ⊢
    obtain ⟨p₁, p₂⟩ := newton_pos (d := o.val d) (μh := o.val μₕ)
      (e := o.B ^ (n + h) - o.val d * o.val μₕ) hB hkh h2 hh2 hnorm (by lia) he
    generalize o.val μₕ * o.B ^ k + o.val μₕ * ((o.B ^ (n + h) - o.val d * o.val μₕ) /
      o.B ^ (h - 2)) / o.B ^ (h + 2) = μ at p₁ p₂ hok₂
    refine ⟨Nat.le_trans (Nat.mul_le_mul_left _ (Nat.sub_le _ _)) p₁, ?_⟩
    rw [show μ - 1 + 5 = μ + 4 by lia]
    exact p₂
  · simp only [Bool.not_eq_true] at hle
    simp only [hle, Bool.false_eq_true, ↓reduceIte, Bool.and_eq_true, Bool.not_eq_true'] at hok ⊢
    obtain ⟨hok₁, hok₂⟩ := hok
    have hlt := o.le_false hle
    rw [o.val_mul, o.val_pow] at hlt
    have hsub := o.val_sub (o.mul d μₕ) (o.pow (n + h)) (by rw [o.val_mul, o.val_pow]; lia)
    rw [o.val_mul, o.val_pow] at hsub
    have he := o.le_false hok₁
    rw [hsub, o.val_pow] at he
    rw [o.le_iff] at hok₂
    simp only [o.val_add, o.val_one, o.val_shl, o.val_hi, o.val_mul, hsub] at hok₂
    have hc : o.val (o.add (o.hi (h + 2) (o.mul μₕ (o.hi (h - 2) (o.sub (o.mul d μₕ)
        (o.pow (n + h)))))) o.one) ≤ o.val (o.shl k μₕ) := by
      simp only [o.val_add, o.val_one, o.val_shl, o.val_hi, o.val_mul, hsub]; lia
    rw [o.val_sub _ _ (by
      rw [o.val_sub _ _ hc]
      simp only [o.val_add, o.val_one, o.val_shl, o.val_hi, o.val_mul, hsub]; lia)]
    rw [o.val_sub _ _ hc]
    simp only [o.val_add, o.val_one, o.val_shl, o.val_hi, o.val_mul, hsub]
    have := newton_neg (d := o.val d) (μh := o.val μₕ)
      (e := o.val d * o.val μₕ - o.B ^ (n + h)) hB hkh h2 hh2 hnorm (by lia) he (by lia)
    exact this

/--
Barrett's step for `x < B²ⁿ` by the `n`-limb `d` with the reciprocal `μ`, like `barrettStep`, but
with the remainder `x - q d` from residues modulo `B^N - 1`, `N = mulModSize (n + 1)`, and `q d`
by `mulMod`. It is exact when `d μ ≤ B²ⁿ < d (μ + 5)` and `Bⁿ ≤ 2 d`, where `x - q d < 7 d`.
-/
public def barrettW (x d μ : α) (n : Nat) : α × α :=
  let q := o.hi (n + 1) (o.mul (o.hi (n - 1) x) μ)
  let N := o.mulModSize (n + 1)
  let w := o.foldM N 4 (o.mulMod (n + 1) q d)
  let xm := o.foldM N 4 x
  let r := if o.le w xm then o.sub xm w else o.sub (o.add xm (o.sub (o.pow N) o.one)) w
  o.fixUp x d q r 7

public theorem barrettW_spec (x d μ : α) (n : Nat) (hB : 8 ≤ o.B) (hn : 1 ≤ n)
    (hd : o.val d < o.B ^ n) (hnorm : o.B ^ n ≤ 2 * o.val d)
    (hA : o.val d * o.val μ ≤ o.B ^ (2 * n)) (hμ : o.B ^ (2 * n) < o.val d * (o.val μ + 5))
    (hx : o.val x < o.B ^ (2 * n)) :
    o.IsDivRem (o.val x) (o.val d) (o.barrettW x d μ n) := by
  have hd0 : 0 < o.val d := by have := Nat.pow_pos (n := n) (show 0 < o.B by lia); lia
  obtain ⟨b₁, b₂⟩ := barrett_bound (show 2 ≤ o.B by lia) hn hnorm hA hμ hx
  unfold barrettW
  dsimp only
  have hN := o.le_mulModSize (n + 1)
  have hwN : ∀ q : α, o.val (o.foldM (o.mulModSize (n + 1)) 4 (o.mulMod (n + 1) q d)) =
      o.val q * o.val d % (o.B ^ o.mulModSize (n + 1) - 1) := fun q => by
    rw [o.val_foldM _ (by lia), o.val_mulMod]
  generalize o.mulModSize (n + 1) = N at *
  have hq : o.val (o.hi (n + 1) (o.mul (o.hi (n - 1) x) μ)) =
      o.val x / o.B ^ (n - 1) * o.val μ / o.B ^ (n + 1) := by
    rw [o.val_hi, o.val_mul, o.val_hi]
  generalize o.hi (n + 1) (o.mul (o.hi (n - 1) x) μ) = q at *
  rw [← hq] at b₁ b₂
  -- The modulus exceeds `7 d`.
  have hM : 7 * o.val d < o.B ^ N - 1 := by
    have h₁ : o.B ^ n * 8 ≤ o.B ^ (n + 1) := by rw [Nat.pow_succ]; exact Nat.mul_le_mul_left _ hB
    have h₂ : o.B ^ (n + 1) ≤ o.B ^ N := Nat.pow_le_pow_right (by lia) hN
    have h₃ : 0 < o.B ^ n := Nat.pow_pos (by lia)
    lia
  have hw := hwN q
  have hxm : o.val (o.foldM N 4 x) = o.val x % (o.B ^ N - 1) := o.val_foldM N (by lia) 4 x
  have hr := sub_of_mod (a := o.val x) (b := o.val q * o.val d) (M := o.B ^ N - 1) b₁ (by lia)
  apply o.fixUp_spec x d hd0
  split
  · rename_i hle
    rw [o.le_iff, hw, hxm] at hle
    rw [o.val_sub _ _ (by rw [hw, hxm]; exact hle), hw, hxm]
    rw [ite_eq_left hle] at hr
    lia
  · rename_i hle
    have hlt := o.le_false (by simpa using hle)
    rw [hw, hxm] at hlt
    have hmod := Nat.mod_lt (o.val q * o.val d) (show 0 < o.B ^ N - 1 by lia)
    rw [o.val_sub _ _ (by rw [o.val_add, o.val_pow_sub_one, hw, hxm]; lia), o.val_add,
      o.val_pow_sub_one, hw, hxm]
    rw [ite_eq_right (by lia)] at hr
    lia

/--
`a` by the `n`-limb `d`, `n` limbs of quotient at a time from the top as in `divBlocks`, by
`barrettW`.
-/
public def divBlocksW (d μ : α) (n : Nat) (hn : 0 < n) (a : α) : α × α :=
  if o.size a ≤ 2 * n then o.barrettW a d μ n
  else
    let t := divBlocksW d μ n hn (o.hi n a)
    let s := o.barrettW (o.add (o.shl n t.2) (o.lo n a)) d μ n
    (o.add (o.shl n t.1) s.1, s.2)
termination_by o.size a
decreasing_by rw [o.size_hi]; lia

public theorem divBlocksW_spec (d μ : α) (n : Nat) (hn : 0 < n) (hB : 8 ≤ o.B)
    (hd : o.val d < o.B ^ n) (hnorm : o.B ^ n ≤ 2 * o.val d)
    (hA : o.val d * o.val μ ≤ o.B ^ (2 * n)) (hμ : o.B ^ (2 * n) < o.val d * (o.val μ + 5))
    (a : α) : o.IsDivRem (o.val a) (o.val d) (o.divBlocksW d μ n hn a) := by
  have hBn : 0 < o.B ^ n := Nat.pow_pos (by lia)
  induction a using WellFounded.induction (InvImage.wf o.size Nat.lt_wfRel.wf) with
  | h a ih =>
    unfold divBlocksW
    split
    · rename_i hsz
      refine o.barrettW_spec _ _ _ _ hB hn hd hnorm hA hμ ?_
      exact Nat.lt_of_lt_of_le (o.val_lt a) (Nat.pow_le_pow_right (by lia) hsz)
    · rename_i hsz
      dsimp only
      obtain ⟨ht₁, ht₂⟩ := ih (o.hi n a) (by
        show o.size (o.hi n a) < o.size a
        rw [o.size_hi]; lia)
      generalize o.divBlocksW d μ n hn (o.hi n a) = t at ht₁ ht₂
      have hblk : o.val (o.add (o.shl n t.2) (o.lo n a)) < o.B ^ (2 * n) := by
        rw [o.val_add, o.val_shl, o.val_lo]
        have h₁ := Nat.mod_lt (o.val a) hBn
        have h₂ : (o.val t.2 + 1) * o.B ^ n ≤ o.val d * o.B ^ n := Nat.mul_le_mul_right _ ht₂
        have h₃ : o.val d * o.B ^ n ≤ o.B ^ n * o.B ^ n := Nat.mul_le_mul_right _ (Nat.le_of_lt hd)
        rw [show 2 * n = n + n by lia, Nat.pow_add]
        rw [Nat.add_mul, Nat.one_mul] at h₂
        lia
      obtain ⟨hs₁, hs₂⟩ := o.barrettW_spec (o.add (o.shl n t.2) (o.lo n a)) d μ n hB hn hd hnorm
        hA hμ hblk
      generalize o.barrettW (o.add (o.shl n t.2) (o.lo n a)) d μ n = s at hs₁ hs₂
      refine ⟨?_, hs₂⟩
      rw [o.val_add, o.val_lo] at hs₁
      rw [o.val_shl] at hs₁
      rw [o.val_hi] at ht₁
      show o.val a = o.val (o.add (o.shl n t.1) s.1) * o.val d + o.val s.2
      rw [o.val_add, o.val_shl]
      have hsplit := Nat.div_add_mod (o.val a) (o.B ^ n)
      generalize o.val a / o.B ^ n = A at hsplit ht₁
      generalize o.val a % o.B ^ n = L at hsplit hs₁
      generalize o.B ^ n = P at *
      rw [← hsplit, ht₁]
      generalize o.val t.1 = T₁ at *
      generalize o.val t.2 = T₂ at *
      generalize o.val s.1 = S₁ at *
      generalize o.val s.2 = S₂ at *
      generalize o.val d = D at *
      grind

/--
`(a / d, a % d)` by Barrett's division with wrapped remainders (`divBlocksW`) when `d` is
normalized, `Bⁿ ≤ 2 d`, and `recipW` checks its reciprocal; otherwise by `divMu`.
-/
public def divMuW (a d : α) : α × α :=
  let n := o.size d
  if hn : 2 ≤ n then
    let m := o.recipW d
    if 8 ≤ o.B ∧ o.le (o.pow n) (o.add d d) = true ∧ m.2 = true then
      o.divBlocksW d m.1 n (by lia) a
    else o.divMu a d
  else o.divMu a d

public theorem divMuW_spec (a d : α) (hd : 0 < o.val d) :
    o.val (o.divMuW a d).1 = o.val a / o.val d ∧ o.val (o.divMuW a d).2 = o.val a % o.val d := by
  unfold divMuW
  dsimp only
  split
  · rename_i hn
    split
    · rename_i hc
      obtain ⟨hB, hnorm, hok⟩ := hc
      rw [o.le_iff, o.val_pow, o.val_add] at hnorm
      obtain ⟨hA, hμ⟩ := o.recipW_spec d hn (by lia) hok
      obtain ⟨h₁, h₂⟩ := o.divBlocksW_spec d (o.recipW d).1 (o.size d) (by lia) hB (o.val_lt d)
        (by lia) hA hμ a
      generalize o.divBlocksW d (o.recipW d).1 (o.size d) _ a = r at h₁ h₂
      refine ⟨?_, ?_⟩
      · rw [h₁, Nat.add_comm, Nat.add_mul_div_right _ _ hd, Nat.div_eq_of_lt h₂, Nat.zero_add]
      · rw [h₁, Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt h₂]
    · exact o.divMu_spec a d hd
  · exact o.divMu_spec a d hd

end NatOps

end MPN
