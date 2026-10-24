/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import MPN.Num

/-!
# Square root

`sqrtRem` computes `⌊√a⌋` and the remainder `a - ⌊√a⌋²` by Zimmermann's Karatsuba square root,
like GMP's `mpn_sqrtrem`. The base case is a double word, by Newton's iteration on words
(`sqrtIter`).
-/

open ScalarArray UInt64Array

namespace MPN

/-! ## Facts about `Nat.sqrt` -/

/-- `⌊√N⌋` is the `r` with `r² ≤ N < (r + 1)²`. -/
public theorem eq_sqrt {r N : Nat} (h₁ : r * r ≤ N) (h₂ : N < (r + 1) * (r + 1)) :
    r = _root_.Nat.sqrt N := by
  have s₁ := Nat.sqrt_le N
  have s₂ := Nat.lt_succ_sqrt N
  rcases Nat.lt_trichotomy r (_root_.Nat.sqrt N) with h | h | h
  · have := Nat.mul_self_le_mul_self (show r + 1 ≤ _root_.Nat.sqrt N by lia)
    lia
  · exact h
  · have := Nat.mul_self_le_mul_self (show _root_.Nat.sqrt N + 1 ≤ r by lia)
    simp only [Nat.succ_eq_add_one] at s₂
    lia

/-- `x ≤ ⌊√N⌋` when `x² ≤ N`. -/
public theorem le_sqrt_of {x N : Nat} (h : x * x ≤ N) : x ≤ _root_.Nat.sqrt N := by
  refine Nat.le_of_not_lt fun hlt => ?_
  have := Nat.mul_self_le_mul_self (show _root_.Nat.sqrt N + 1 ≤ x from hlt)
  have := Nat.lt_succ_sqrt N
  simp only [Nat.succ_eq_add_one] at this
  lia

/-- One step of Newton's iteration stays at or above `s` when `s² ≤ N`, by AM-GM. -/
public theorem le_newton {x s N : Nat} (hx : 0 < x) (hs : s * s ≤ N) :
    s ≤ (x + N / x) / 2 := by
  refine Nat.le_of_not_lt fun hlt => ?_
  have hN : N < x * (N / x + 1) := Nat.lt_mul_div_succ N hx
  generalize N / x = q at *
  have h2 : x + q + 1 ≤ 2 * s := by lia
  have h3 := Nat.mul_self_le_mul_self h2
  -- `4 x (q + 1) ≤ (x + q + 1)²`, since their difference is a square.
  have h4 : 4 * (x * (q + 1)) ≤ (x + q + 1) * (x + q + 1) := by
    have e : ((x : Int) + q + 1) * ((x : Int) + q + 1) - 4 * ((x : Int) * (q + 1)) =
        ((x : Int) - (q + 1)) * ((x : Int) - (q + 1)) := by grind
    have hsq : 0 ≤ ((x : Int) - (q + 1)) * ((x : Int) - (q + 1)) := by
      rcases Int.le_total 0 ((x : Int) - (q + 1)) with h | h
      · exact Int.mul_nonneg h h
      · exact Int.mul_nonneg_of_nonpos_of_nonpos h h
    have h : ((4 * (x * (q + 1)) : Nat) : Int) ≤ (((x + q + 1) * (x + q + 1) : Nat) : Int) := by
      push_cast; lia
    exact_mod_cast h
  have : 2 * s * (2 * s) = 4 * (s * s) := by rw [Nat.mul_mul_mul_comm]
  lia

/-! ## Words -/

/-- The average `⌊(x + q) / 2⌋` of two words, without overflow. -/
@[inline] public def avg (x q : UInt64) : UInt64 := (x >>> 1) + (q >>> 1) + (x &&& 1) * (q &&& 1)

private theorem toNat_avg (x q : UInt64) : (avg x q).toNat = (x.toNat + q.toNat) / 2 := by
  have hx := x.toNat_lt; have hq := q.toNat_lt
  have hand : ((x &&& 1) * (q &&& 1)).toNat = x.toNat % 2 * (q.toNat % 2) := by
    rw [UInt64.toNat_mul, UInt64.toNat_and, UInt64.toNat_and, UInt64.toNat_one, Nat.and_one_is_mod,
      Nat.and_one_is_mod]
    have h₁ := Nat.mod_lt x.toNat (show 0 < 2 by decide)
    have h₂ := Nat.mod_lt q.toNat (show 0 < 2 by decide)
    have := Nat.mul_le_mul h₁ h₂
    exact Nat.mod_eq_of_lt (by lia)
  simp only [avg, UInt64.toNat_add, UInt64.toNat_shiftRight, hand, Nat.shiftRight_eq_div_pow]
  simp only [UInt64.reduceToNat, Nat.reduceMod, Nat.pow_one]
  rcases Nat.mod_two_eq_zero_or_one x.toNat with h | h <;>
    rcases Nat.mod_two_eq_zero_or_one q.toNat with h' | h' <;>
    simp only [h, h', Nat.mul_zero, Nat.mul_one] <;> lia

/--
Newton's iteration for `⌊√N⌋`, `N = hi β + lo`, from `x ≥ ⌊√N⌋`, while it decreases: the next
step is the average of `x` and `N / x`. When `hi ≥ x`, `x` is already `⌊√N⌋`, since `⌊√N⌋ ≥ hi`.
-/
public def sqrtIter (hi lo x : UInt64) : UInt64 :=
  if hi < x then
    let y := avg x (UInt64.div2 hi lo x)
    if y < x then sqrtIter hi lo y else x
  else x
termination_by x.toNat
decreasing_by exact UInt64.lt_iff_toNat_lt.1 (by assumption)

private theorem sqrtIter_eq (hi lo x : UInt64)
    (hx : _root_.Nat.sqrt (hi.toNat * 2 ^ 64 + lo.toNat) ≤ x.toNat) :
    (sqrtIter hi lo x).toNat = _root_.Nat.sqrt (hi.toNat * 2 ^ 64 + lo.toNat) := by
  induction x using sqrtIter.induct hi lo with
  | case1 x h y hy ih =>
    rw [sqrtIter, ite_eq_left h]
    simp only [y] at hy ⊢
    rw [ite_eq_left hy]
    apply ih
    rw [toNat_avg, UInt64.toNat_div2 _ _ _ (UInt64.lt_iff_toNat_lt.1 h)]
    exact le_newton (by have := UInt64.lt_iff_toNat_lt.1 h; lia) (Nat.sqrt_le _)
  | case2 x h y hy =>
    rw [sqrtIter, ite_eq_left h]
    simp only [y] at hy ⊢
    rw [ite_eq_right hy]
    rw [UInt64.lt_iff_toNat_lt, toNat_avg, UInt64.toNat_div2 _ _ _ (UInt64.lt_iff_toNat_lt.1 h)]
      at hy
    -- `N / x ≥ x`, so `x² ≤ N`.
    have hxx : x.toNat * x.toNat ≤ hi.toNat * 2 ^ 64 + lo.toNat :=
      (Nat.le_div_iff_mul_le (by have := UInt64.lt_iff_toNat_lt.1 h; lia)).1 (by lia)
    exact Nat.le_antisymm (le_sqrt_of hxx) hx
  | case3 x h =>
    rw [sqrtIter, ite_eq_right h]
    -- `hi² ≤ N`, so `hi ≤ ⌊√N⌋ ≤ x ≤ hi`.
    have hle : hi.toNat ≤ _root_.Nat.sqrt (hi.toNat * 2 ^ 64 + lo.toNat) :=
      le_sqrt_of (by
        have := Nat.mul_le_mul_left hi.toNat (Nat.le_of_lt hi.toNat_lt)
        lia)
    have := UInt64.le_iff_toNat_le.1 (UInt64.not_lt.1 h)
    lia

/-- `⌊√N⌋` of a double word `N = hi β + lo`. -/
public def sqrt2 (hi lo : UInt64) : UInt64 := sqrtIter hi lo 0xFFFFFFFFFFFFFFFF

public theorem toNat_sqrt2 (hi lo : UInt64) :
    (sqrt2 hi lo).toNat = _root_.Nat.sqrt (hi.toNat * 2 ^ 64 + lo.toNat) := by
  apply sqrtIter_eq
  -- `⌊√N⌋ < β`, since `N < β²`.
  have := hi.toNat_lt; have := lo.toNat_lt
  have h : _root_.Nat.sqrt (hi.toNat * 2 ^ 64 + lo.toNat) < 2 ^ 64 := by
    refine Nat.lt_of_not_le fun hge => ?_
    have := Nat.mul_self_le_mul_self hge
    have := Nat.sqrt_le (hi.toNat * 2 ^ 64 + lo.toNat)
    have := Nat.mul_le_mul_right (2 ^ 64) (show hi.toNat + 1 ≤ 2 ^ 64 by lia)
    lia
  simp only [UInt64.reduceToNat]
  lia

/-! ## Zimmermann's step -/

/--
Zimmermann's Karatsuba square root step, as in GMP's `mpn_dc_sqrtrem`: for `N = N' B² + a₁ B + a₀`
with `a₁, a₀ < B` and `B ≤ 2 s'`, where `s' = ⌊√N'⌋`, the quotient `q` and the remainder `u` of
`(N' - s'²) B + a₁` by `2 s'` give `s = s' B + q` and `T = u B + a₀`, and then `⌊√N⌋` is `s` with
the remainder `T - q²` when `q² ≤ T`, and `s - 1` with the remainder `T + 2 s - 1 - q²` otherwise.
-/
public theorem karatsuba_sqrt {B N' a₁ a₀ t q u : Nat} (ht : t = _root_.Nat.sqrt N')
    (ha₁ : a₁ < B) (ha₀ : a₀ < B) (hs : B ≤ 2 * t)
    (hq : q = ((N' - t * t) * B + a₁) / (2 * t)) (hu : u = ((N' - t * t) * B + a₁) % (2 * t)) :
    (q * q ≤ u * B + a₀ →
      _root_.Nat.sqrt (N' * B * B + a₁ * B + a₀) = t * B + q ∧
        N' * B * B + a₁ * B + a₀ - (t * B + q) * (t * B + q) = u * B + a₀ - q * q) ∧
    (u * B + a₀ < q * q →
      _root_.Nat.sqrt (N' * B * B + a₁ * B + a₀) = t * B + q - 1 ∧
        N' * B * B + a₁ * B + a₀ - (t * B + q - 1) * (t * B + q - 1) =
          u * B + a₀ + (2 * (t * B + q) - 1) - q * q ∧
        1 ≤ q ∧ q * q ≤ u * B + a₀ + (2 * (t * B + q) - 1)) := by
  subst hq hu
  have h₁ := Nat.sqrt_le N'
  have h₂ := Nat.lt_succ_sqrt N'
  simp only [Nat.succ_eq_add_one] at h₂
  rw [← ht] at h₁ h₂
  have hr : N' - t * t ≤ 2 * t := by
    rw [Nat.add_mul, Nat.mul_add, Nat.mul_one, Nat.one_mul] at h₂; lia
  have ht : 0 < 2 * t := by lia
  have hdm := Nat.div_add_mod ((N' - t * t) * B + a₁) (2 * t)
  have hu := Nat.mod_lt ((N' - t * t) * B + a₁) ht
  generalize ((N' - t * t) * B + a₁) / (2 * t) = q at *
  generalize ((N' - t * t) * B + a₁) % (2 * t) = u at *
  generalize hR : N' - t * t = r at *
  have hN' : N' = t * t + r := by lia
  subst hN'
  -- `q ≤ B`.
  have hqB : q ≤ B := by
    refine Nat.le_of_not_lt fun hlt => ?_
    have := Nat.mul_le_mul_left (2 * t) (show B + 1 ≤ q from hlt)
    have := Nat.mul_le_mul_right B hr
    have := Nat.mul_le_mul_left (2 * t) hs
    rw [Nat.mul_add, Nat.mul_one] at *
    lia
  -- `N + q² = s² + T`.
  have key : (t * t + r) * B * B + a₁ * B + a₀ + q * q =
      (t * B + q) * (t * B + q) + (u * B + a₀) := by
    have e : r * B + a₁ = 2 * t * q + u := by lia
    have e' : (r * B + a₁) * B = (2 * t * q + u) * B := by rw [e]
    grind
  have hq2 : q * q ≤ B * B := Nat.mul_self_le_mul_self hqB
  have hBs : B * B ≤ 2 * t * B := Nat.mul_le_mul_right B hs
  have huB : u * B + a₀ < 2 * t * B := by
    have := Nat.mul_le_mul_right B (show u + 1 ≤ 2 * t from hu)
    rw [Nat.add_mul, Nat.one_mul] at this
    lia
  generalize (t * t + r) * B * B + a₁ * B + a₀ = N at *
  constructor
  · intro hle
    refine ⟨(eq_sqrt (by lia) ?_).symm, by lia⟩
    have : (t * B + q + 1) * (t * B + q + 1) =
        (t * B + q) * (t * B + q) + 2 * (t * B) + 2 * q + 1 := by grind
    have : 2 * (t * B) = 2 * t * B := by rw [Nat.mul_assoc]
    lia
  · intro hlt
    have hq1 : 1 ≤ q := by
      rcases Nat.eq_zero_or_pos q with h | h
      · subst h; simp at hlt
      · exact h
    have e : (t * B + q - 1) * (t * B + q - 1) + 2 * (t * B + q) =
        (t * B + q) * (t * B + q) + 1 := by
      obtain ⟨p, hp⟩ : ∃ p, t * B + q = p + 1 := ⟨t * B + q - 1, by lia⟩
      rw [hp, Nat.add_sub_cancel]
      grind
    have : 2 * (t * B) = 2 * t * B := by rw [Nat.mul_assoc]
    refine ⟨(eq_sqrt (by lia) ?_).symm, by lia, hq1, by lia⟩
    rw [Nat.sub_add_cancel (by lia)]
    lia

/-- The three parts of `N` at `B²` and `B`. -/
private theorem split3 (N B : Nat) : N = N / (B * B) * B * B + N / B % B * B + N % B := by
  have h1 := Nat.div_add_mod N B
  have h2 := Nat.div_add_mod (N / B) B
  rw [Nat.div_div_eq_div_mul] at h2
  generalize N / (B * B) = c at *
  generalize N / B % B = b at *
  generalize N % B = a at *
  generalize N / B = d at *
  subst h2 h1
  grind

/-- The remainder by `2 s` from the remainder of `X / 2` by `s`. -/
private theorem mod_two_mul (X s : Nat) (hs : 0 < s) : X % (2 * s) = 2 * (X / 2 % s) + X % 2 := by
  have h1 := Nat.div_add_mod X 2
  have h2 := Nat.div_add_mod (X / 2) s
  have h3 := Nat.mod_lt (X / 2) hs
  have h4 := Nat.mod_lt X (show 0 < 2 by decide)
  have e : X = (2 * (X / 2 % s) + X % 2) + 2 * s * (X / 2 / s) := by
    generalize X / 2 / s = k at *
    generalize X / 2 % s = m at *
    generalize X / 2 = d at *
    generalize X % 2 = b at *
    subst h1 h2
    grind
  conv => lhs; rw [e]
  rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by lia)]

/-- The root of a value below `β^(2n)` is below `βⁿ`. -/
private theorem sqrt_lt_of {N P : Nat} (h : N < P * P) : _root_.Nat.sqrt N < P := by
  refine Nat.lt_of_not_le fun hge => ?_
  have := Nat.mul_self_le_mul_self hge
  have := Nat.sqrt_le N
  lia

/-- The remainder of the root is at most twice the root. -/
private theorem sqrt_rem_le (N : Nat) :
    N - _root_.Nat.sqrt N * _root_.Nat.sqrt N ≤ 2 * _root_.Nat.sqrt N := by
  have := Nat.lt_succ_sqrt N
  simp only [Nat.succ_eq_add_one, Nat.add_mul, Nat.mul_add, Nat.mul_one, Nat.one_mul] at this
  lia

/-- Normalizing by `4ᶜ`: `⌊√(a 4ᶜ)⌋ / 2ᶜ = ⌊√a⌋`. -/
public theorem sqrt_mul_four_pow (a c : Nat) :
    _root_.Nat.sqrt (a * 2 ^ (2 * c)) / 2 ^ c = _root_.Nat.sqrt a := by
  have h₁ := Nat.sqrt_le a
  have h₂ := Nat.lt_succ_sqrt a
  simp only [Nat.succ_eq_add_one] at h₂
  generalize _root_.Nat.sqrt a = t at *
  have hP : 2 ^ (2 * c) = 2 ^ c * 2 ^ c := by rw [← Nat.pow_add]; congr 1; lia
  have hlo : t * 2 ^ c ≤ _root_.Nat.sqrt (a * 2 ^ (2 * c)) := le_sqrt_of (by
    rw [hP]
    have := Nat.mul_le_mul_right (2 ^ c * 2 ^ c) h₁
    calc t * 2 ^ c * (t * 2 ^ c) = t * t * (2 ^ c * 2 ^ c) := by
          rw [Nat.mul_mul_mul_comm]
      _ ≤ a * (2 ^ c * 2 ^ c) := this)
  have hhi : _root_.Nat.sqrt (a * 2 ^ (2 * c)) < (t + 1) * 2 ^ c := by
    apply sqrt_lt_of
    rw [hP]
    have := Nat.mul_lt_mul_of_pos_right h₂ (show 0 < 2 ^ c * 2 ^ c from
      Nat.mul_pos (Nat.two_pow_pos _) (Nat.two_pow_pos _))
    calc a * (2 ^ c * 2 ^ c) < (t + 1) * (t + 1) * (2 ^ c * 2 ^ c) := this
      _ = (t + 1) * 2 ^ c * ((t + 1) * 2 ^ c) := by rw [Nat.mul_mul_mul_comm]
  apply Nat.le_antisymm
  · rw [Nat.div_le_iff_le_mul_add_pred (Nat.two_pow_pos _)]
    have := Nat.two_pow_pos c
    rw [Nat.add_mul, Nat.one_mul] at hhi
    lia
  · exact (Nat.le_div_iff_mul_le (Nat.two_pow_pos _)).2 hlo

/-! ## The recursion -/

/-- The word `x` as an array of one limb. -/
@[inline] public def word (x : UInt64) : UInt64Array := UInt64Array.replicate 1 x

private theorem toNat_word (x : UInt64) : (word x).toNat = x.toNat := by
  simp [word, toNat_eq_valAt]

/--
`(⌊√N⌋, N - ⌊√N⌋²)`, in `n` and `n + 1` limbs, for `N` of `2 n` limbs with `β^(2n) ≤ 4 N`, by
Zimmermann's step (`karatsuba_sqrt`) with `B = β^l`, `l = ⌊n / 2⌋`, on the root of the top `2 h`
limbs, `h = n - l`, and by `sqrt2` on two limbs.
-/
public def sqrtRemAux (N : UInt64Array) (n : Nat) : UInt64Array × UInt64Array :=
  if hn : n ≤ 1 then
    let S := word (sqrt2 N[1]! N[0]!)
    (S, Num.low (Num.sub N (Num.sqr S)) 2)
  else
    let l := n / 2
    let h := n - l
    let p := sqrtRemAux (Num.shr N (128 * l)) h
    let s' := p.1
    let r' := p.2
    let X := Num.add (Num.shl r' (64 * l)) (Num.low (Num.shr N (64 * l)) l)
    let X₂ := Num.shr X 1
    let d := Num.divMod X₂ s'
    let q := Num.low d.1 (l + 1)
    let u := Num.add (Num.shl (Num.low d.2 h) 1) (Num.sub X (Num.shl X₂ 1))
    let s := Num.add (Num.shl s' (64 * l)) q
    let T := Num.add (Num.shl u (64 * l)) (Num.low N l)
    let q₂ := Num.sqr q
    if Num.lt T q₂ then
      (Num.low (Num.sub s (word 1)) n,
        Num.low (Num.sub (Num.add T (Num.sub (Num.shl s 1) (word 1))) q₂) (n + 1))
    else
      (Num.low s n, Num.low (Num.sub T q₂) (n + 1))
termination_by n
decreasing_by lia

private theorem sqrtRemAux_spec (N : UInt64Array) (n : Nat) (hn : 1 ≤ n) (hs : N.size = 2 * n)
    (hnorm : 2 ^ (128 * n) ≤ 4 * N.toNat) (hU : 4 * n + 16 < USize.size) :
    (sqrtRemAux N n).1.size ≤ n ∧ (sqrtRemAux N n).2.size ≤ n + 1 ∧
      (sqrtRemAux N n).1.toNat = _root_.Nat.sqrt N.toNat ∧
      (sqrtRemAux N n).2.toNat =
        N.toNat - _root_.Nat.sqrt N.toNat * _root_.Nat.sqrt N.toNat := by
  induction n using Nat.strongRecOn generalizing N with
  | ind n ih =>
  by_cases hn' : n ≤ 1
  · have h1 : n = 1 := by lia
    subst h1
    rw [sqrtRemAux, dite_eq_left hn']
    dsimp only
    clear ih
    have hN : N.size < USize.size := by lia
    have hNv : N.toNat = N[1]!.toNat * 2 ^ 64 + N[0]!.toNat := by
      rw [toNat_eq_valAt, hs]; simp only [valAt_succ, valAt_zero]; lia
    have hS : (word (sqrt2 N[1]! N[0]!)).toNat = _root_.Nat.sqrt N.toNat := by
      rw [toNat_word, toNat_sqrt2, hNv]
    have hSs : (word (sqrt2 N[1]! N[0]!)).size = 1 := by simp [word]
    have hsq := Num.toNat_sqr (word (sqrt2 N[1]! N[0]!)) (by rw [hSs]; lia)
    have hsqs := Num.size_sqr_le (word (sqrt2 N[1]! N[0]!))
    have hNlt : N.toNat < 2 ^ 64 * 2 ^ 64 := by
      rw [toNat_eq_valAt, hs, ← Nat.pow_add]; exact valAt_lt ..
    have hrt := sqrt_lt_of hNlt
    have hrem := sqrt_rem_le N.toNat
    refine ⟨by rw [hSs]; exact Nat.le_refl _, ?_, hS, ?_⟩
    · rw [Num.size_low _ _ (by rw [Num.size_sub]; lia)]; lia
    · rw [Num.toNat_low _ _ (by rw [Num.size_sub]; lia), Num.toNat_sub _ _ (by
        rw [hsq, hS]; exact Nat.sqrt_le _) hN (by lia), hsq, hS, Nat.mod_eq_of_lt]
      have : 2 ^ (64 * 2) = 2 ^ 64 * 2 ^ 64 := by rw [← Nat.pow_add]
      rw [this]
      have := Nat.two_pow_pos 64
      have : 2 * 2 ^ 64 ≤ 2 ^ 64 * 2 ^ 64 := Nat.mul_le_mul_right _ (by decide)
      lia
  · rw [sqrtRemAux, dite_eq_right hn']
    dsimp only
    have hN : N.size < USize.size := by lia
    have hNlt : N.toNat < 2 ^ (128 * n) := by
      rw [toNat_eq_valAt, hs, show 128 * n = 64 * (2 * n) by lia]; exact valAt_lt ..
    -- The top half and its root.
    have hN₁s : (Num.shr N (128 * (n / 2))).size = 2 * (n - n / 2) := by
      rw [Num.size_shr, hs]; lia
    have hN₁v : (Num.shr N (128 * (n / 2))).toNat = N.toNat / 2 ^ (128 * (n / 2)) :=
      Num.toNat_shr _ _ hN
    have hP : 2 ^ (128 * n) = 2 ^ (128 * (n - n / 2)) * 2 ^ (128 * (n / 2)) := by
      rw [← Nat.pow_add]; congr 1; lia
    have hnorm₁ : 2 ^ (128 * (n - n / 2)) ≤ 4 * (Num.shr N (128 * (n / 2))).toNat := by
      rw [hN₁v]
      have e : 2 ^ (128 * (n - n / 2)) = 4 * 2 ^ (128 * (n - n / 2) - 2) := by
        rw [show (4 : Nat) = 2 ^ 2 by rfl, ← Nat.pow_add]; congr 1; lia
      rw [e]
      apply Nat.mul_le_mul_left
      apply (Nat.le_div_iff_mul_le (Nat.two_pow_pos _)).2
      rw [hP, e, Nat.mul_assoc] at hnorm
      exact Nat.le_of_mul_le_mul_left hnorm (by decide)
    obtain ⟨i₁, i₂, i₃, i₄⟩ := ih (n - n / 2) (by lia) _ (by lia) hN₁s hnorm₁ (by lia)
    clear ih
    generalize hl : n / 2 = l at *
    generalize sqrtRemAux (Num.shr N (128 * l)) (n - l) = p at i₁ i₂ i₃ i₄ ⊢
    rw [hN₁v] at i₃ i₄
    generalize hB : 2 ^ (64 * l) = B at *
    have hBB : 2 ^ (128 * l) = B * B := by rw [← hB, ← Nat.pow_add]; congr 1; lia
    rw [hBB] at i₃ i₄
    generalize hN₁ : N.toNat / (B * B) = N₁ at i₃ i₄
    generalize ht : _root_.Nat.sqrt N₁ = t at i₃ i₄
    -- `B ≤ 2 t`, from the normalization of the top half.
    have hN₁ge : 2 ^ (128 * (n - l) - 2) ≤ N₁ := by
      rw [← hN₁, ← hBB]
      apply (Nat.le_div_iff_mul_le (Nat.two_pow_pos _)).2
      rw [← Nat.pow_add]
      have : 2 ^ (128 * (n - l) - 2 + 128 * l) * 4 = 2 ^ (128 * n) := by
        rw [show (4 : Nat) = 2 ^ 2 by rfl, ← Nat.pow_add]; congr 1; lia
      lia
    have htge : 2 ^ (64 * (n - l) - 1) ≤ t := by
      rw [← ht]
      apply le_sqrt_of
      rw [← Nat.pow_add]
      exact Nat.le_trans (Nat.pow_le_pow_right (by decide) (by lia)) hN₁ge
    have hBt : B ≤ 2 * t := by
      rw [← hB]
      have : 2 * 2 ^ (64 * (n - l) - 1) = 2 ^ (64 * (n - l)) := by
        rw [← Nat.pow_succ']; congr 1; lia
      have : 2 ^ (64 * l) ≤ 2 ^ (64 * (n - l)) := Nat.pow_le_pow_right (by decide) (by lia)
      lia
    have ht0 : 0 < t := by have := Nat.two_pow_pos (64 * (n - l) - 1); lia
    have hN₁lt : N₁ < 2 ^ (64 * (n - l)) * 2 ^ (64 * (n - l)) := by
      rw [← Nat.pow_add, ← hN₁]
      apply (Nat.div_lt_iff_lt_mul (by rw [← hBB]; exact Nat.two_pow_pos _)).2
      rw [← hBB, ← Nat.pow_add]
      exact Nat.lt_of_lt_of_le hNlt (Nat.pow_le_pow_right (by decide) (by lia))
    have htlt : t < 2 ^ (64 * (n - l)) := by rw [← ht]; exact sqrt_lt_of hN₁lt
    -- The parts `a₁` and `a₀`.
    have hA₁s : (Num.low (Num.shr N (64 * l)) l).size ≤ l := by
      rw [Num.size_low _ _ (by rw [Num.size_shr]; lia)]; lia
    have hA₁v : (Num.low (Num.shr N (64 * l)) l).toNat = N.toNat / B % B := by
      rw [Num.toNat_low _ _ (by rw [Num.size_shr]; lia), Num.toNat_shr _ _ hN, hB]
    generalize Num.low (Num.shr N (64 * l)) l = A₁ at hA₁s hA₁v ⊢
    have hA₀s : (Num.low N l).size ≤ l := by rw [Num.size_low _ _ hN]; lia
    have hA₀v : (Num.low N l).toNat = N.toNat % B := by rw [Num.toNat_low _ _ hN, hB]
    generalize Num.low N l = A₀ at hA₀s hA₀v ⊢
    -- `X = r' B + a₁`, and its quotient and remainder by `2 t`.
    have hR's : (Num.shl p.2 (64 * l)).size = l + p.2.size + 1 := by rw [Num.size_shl]; lia
    have hR'v : (Num.shl p.2 (64 * l)).toNat = (N₁ - t * t) * B := by
      rw [Num.toNat_shl _ _ (by lia), i₄, hB]
    generalize Num.shl p.2 (64 * l) = R' at hR's hR'v ⊢
    have hXs : (Num.add R' A₁).size = max R'.size A₁.size + 1 := Num.size_add ..
    have hXv : (Num.add R' A₁).toNat = (N₁ - t * t) * B + N.toNat / B % B := by
      rw [Num.toNat_add _ _ (by lia), hR'v, hA₁v]
    generalize Num.add R' A₁ = X at hXs hXv ⊢
    generalize hXn : (N₁ - t * t) * B + N.toNat / B % B = Xn at hXv
    have hX₂s : (Num.shr X 1).size = X.size := by rw [Num.size_shr]; lia
    have hX₂v : (Num.shr X 1).toNat = Xn / 2 := by rw [Num.toNat_shr _ _ (by lia), hXv]
    generalize Num.shr X 1 = X₂ at hX₂s hX₂v ⊢
    obtain ⟨d₁, d₂⟩ := Num.toNat_divMod X₂ p.1 (by lia) (by lia)
    obtain ⟨d₃, d₄⟩ := Num.size_divMod X₂ p.1 (by lia)
    rw [hX₂v, i₃] at d₁ d₂
    generalize Num.divMod X₂ p.1 = d at d₁ d₂ d₃ d₄ ⊢
    -- `q ≤ B`.
    have hqB : Xn / 2 / t ≤ B := by
      rw [Nat.div_div_eq_div_mul]
      refine Nat.le_of_lt_succ ((Nat.div_lt_iff_lt_mul (by lia)).2 ?_)
      have hr : N₁ - t * t ≤ 2 * t := by rw [← ht]; exact sqrt_rem_le N₁
      have := Nat.mul_le_mul_right B hr
      have := Nat.mod_lt (N.toNat / B) (show 0 < B by rw [← hB]; exact Nat.two_pow_pos _)
      rw [Nat.succ_mul]
      have : 2 * t * B = B * (2 * t) := Nat.mul_comm _ _
      lia
    have hqs : (Num.low d.1 (l + 1)).size ≤ l + 1 := by
      rw [Num.size_low _ _ (by lia)]; lia
    have hqv : (Num.low d.1 (l + 1)).toNat = Xn / 2 / t := by
      rw [Num.toNat_low _ _ (by lia), d₁, Nat.mod_eq_of_lt]
      have : B < 2 ^ (64 * (l + 1)) := by
        rw [← hB]; exact Nat.pow_lt_pow_right (by decide) (by lia)
      lia
    generalize Num.low d.1 (l + 1) = q at hqs hqv ⊢
    have hU2s : (Num.low d.2 (n - l)).size ≤ n - l := by
      rw [Num.size_low _ _ (by lia)]; lia
    have hU2v : (Num.low d.2 (n - l)).toNat = Xn / 2 % t := by
      rw [Num.toNat_low _ _ (by lia), d₂, Nat.mod_eq_of_lt]
      exact Nat.lt_trans (Nat.mod_lt _ ht0) htlt
    generalize Num.low d.2 (n - l) = U2 at hU2s hU2v ⊢
    have hW2s : (Num.shl U2 1).size = U2.size + 1 := by rw [Num.size_shl]; lia
    have hW2v : (Num.shl U2 1).toNat = Xn / 2 % t * 2 := by
      rw [Num.toNat_shl _ _ (by lia), hU2v]
    generalize Num.shl U2 1 = W2 at hW2s hW2v ⊢
    have hXss : (Num.shl X₂ 1).size = X₂.size + 1 := by rw [Num.size_shl]; lia
    have hXsv : (Num.shl X₂ 1).toNat = Xn / 2 * 2 := by
      rw [Num.toNat_shl _ _ (by lia), hX₂v]
    generalize Num.shl X₂ 1 = Xs at hXss hXsv ⊢
    have hbs : (Num.sub X Xs).size = X.size := Num.size_sub ..
    have hbv : (Num.sub X Xs).toNat = Xn % 2 := by
      rw [Num.toNat_sub _ _ (by rw [hXsv, hXv]; lia) (by lia) (by lia), hXsv, hXv]
      have := Nat.div_add_mod Xn 2
      lia
    generalize Num.sub X Xs = Bt at hbs hbv ⊢
    have hus : (Num.add W2 Bt).size = max W2.size Bt.size + 1 := Num.size_add ..
    have huv : (Num.add W2 Bt).toNat = Xn % (2 * t) := by
      rw [Num.toNat_add _ _ (by lia), hW2v, hbv, mod_two_mul _ _ ht0]
      lia
    generalize Num.add W2 Bt = u at hus huv ⊢
    -- `s = t B + q` and `T = u B + a₀`.
    have hS1s : (Num.shl p.1 (64 * l)).size = l + p.1.size + 1 := by rw [Num.size_shl]; lia
    have hS1v : (Num.shl p.1 (64 * l)).toNat = t * B := by
      rw [Num.toNat_shl _ _ (by lia), i₃, hB]
    generalize Num.shl p.1 (64 * l) = S1 at hS1s hS1v ⊢
    have hss : (Num.add S1 q).size = max S1.size q.size + 1 := Num.size_add ..
    have hsv : (Num.add S1 q).toNat = t * B + Xn / 2 / t := by
      rw [Num.toNat_add _ _ (by lia), hS1v, hqv]
    generalize Num.add S1 q = sv at hss hsv ⊢
    have hU3s : (Num.shl u (64 * l)).size = l + u.size + 1 := by rw [Num.size_shl]; lia
    have hU3v : (Num.shl u (64 * l)).toNat = Xn % (2 * t) * B := by
      rw [Num.toNat_shl _ _ (by lia), huv, hB]
    generalize Num.shl u (64 * l) = U3 at hU3s hU3v ⊢
    have hTs : (Num.add U3 A₀).size = max U3.size A₀.size + 1 := Num.size_add ..
    have hTv : (Num.add U3 A₀).toNat = Xn % (2 * t) * B + N.toNat % B := by
      rw [Num.toNat_add _ _ (by lia), hU3v, hA₀v]
    generalize Num.add U3 A₀ = T at hTs hTv ⊢
    have hq₂s := Num.size_sqr_le q
    have hq₂v : (Num.sqr q).toNat = Xn / 2 / t * (Xn / 2 / t) := by
      rw [Num.toNat_sqr _ (by lia), hqv]
    generalize Num.sqr q = q₂ at hq₂s hq₂v ⊢
    -- Zimmermann's step.
    have hsplit := split3 N.toNat B
    rw [hN₁] at hsplit
    have hB0 : 0 < B := by rw [← hB]; exact Nat.two_pow_pos _
    obtain ⟨k₁, k₂⟩ := karatsuba_sqrt (B := B) (N' := N₁) (a₁ := N.toNat / B % B)
      (a₀ := N.toNat % B) (t := t) (q := Xn / 2 / t) (u := Xn % (2 * t)) ht.symm
      (Nat.mod_lt _ hB0) (Nat.mod_lt _ hB0) hBt (by rw [Nat.div_div_eq_div_mul, hXn])
      (by rw [hXn])
    rw [← hsplit] at k₁ k₂
    have hNlt' : N.toNat < 2 ^ (64 * n) * 2 ^ (64 * n) := by
      rw [← Nat.pow_add, show 64 * n + 64 * n = 128 * n by lia]; exact hNlt
    have hrt := sqrt_lt_of hNlt'
    have hrem := sqrt_rem_le N.toNat
    have hrem' : 2 * _root_.Nat.sqrt N.toNat < 2 ^ (64 * (n + 1)) := by
      rw [show 64 * (n + 1) = 64 * n + 64 by lia, Nat.pow_add]
      have := Nat.two_pow_pos (64 * n)
      lia
    have hw1 : (word 1).toNat = 1 := toNat_word 1
    have hw1s : (word 1).size = 1 := by simp [word]
    by_cases hlt : T.toNat < q₂.toNat
    · rw [ite_eq_left ((Num.lt_iff _ _ (by lia)).2 hlt)]
      rw [hTv, hq₂v] at hlt
      obtain ⟨e₁, e₂, e₃, e₄⟩ := k₂ hlt
      have hsub1 : (Num.sub sv (word 1)).toNat = t * B + Xn / 2 / t - 1 := by
        rw [Num.toNat_sub _ _ (by rw [hw1, hsv]; lia) (by lia) (by lia), hw1, hsv]
      have hs2 : (Num.sub (Num.shl sv 1) (word 1)).toNat = 2 * (t * B + Xn / 2 / t) - 1 := by
        rw [Num.toNat_sub _ _ (by rw [hw1, Num.toNat_shl _ _ (by lia), hsv]; lia)
          (by rw [Num.size_shl]; lia) (by lia), hw1, Num.toNat_shl _ _ (by lia), hsv]
        lia
      have hs2s : (Num.sub (Num.shl sv 1) (word 1)).size = sv.size + 1 := by
        rw [Num.size_sub, Num.size_shl]; lia
      have hadd : (Num.add T (Num.sub (Num.shl sv 1) (word 1))).toNat =
          Xn % (2 * t) * B + N.toNat % B + (2 * (t * B + Xn / 2 / t) - 1) := by
        rw [Num.toNat_add _ _ (by lia), hTv, hs2]
      have hadds := Num.size_add T (Num.sub (Num.shl sv 1) (word 1))
      refine ⟨?_, ?_, ?_, ?_⟩
      · rw [Num.size_low _ _ (by rw [Num.size_sub]; lia)]; lia
      · rw [Num.size_low _ _ (by rw [Num.size_sub]; lia)]; lia
      · rw [Num.toNat_low _ _ (by rw [Num.size_sub]; lia), hsub1, ← e₁, Nat.mod_eq_of_lt hrt]
      · rw [Num.toNat_low _ _ (by rw [Num.size_sub]; lia),
          Num.toNat_sub _ _ (by rw [hadd, hq₂v]; lia) (by lia) (by lia), hadd, hq₂v, ← e₂, e₁,
          Nat.mod_eq_of_lt (by rw [← e₁]; lia)]
    · rw [ite_eq_right (fun h => hlt ((Num.lt_iff _ _ (by lia)).1 h))]
      rw [hTv, hq₂v] at hlt
      obtain ⟨e₁, e₂⟩ := k₁ (by lia)
      refine ⟨?_, ?_, ?_, ?_⟩
      · rw [Num.size_low _ _ (by lia)]; lia
      · rw [Num.size_low _ _ (by rw [Num.size_sub]; lia)]; lia
      · rw [Num.toNat_low _ _ (by lia), hsv, ← e₁, Nat.mod_eq_of_lt hrt]
      · rw [Num.toNat_low _ _ (by rw [Num.size_sub]; lia),
          Num.toNat_sub _ _ (by rw [hTv, hq₂v]; lia) (by lia) (by lia), hTv, hq₂v, ← e₂, e₁,
          Nat.mod_eq_of_lt (by rw [← e₁]; lia)]

/-! ## Any number -/

/--
`(⌊√a⌋, a - ⌊√a⌋²)`. The value is normalized by `4ᶜ` to `2 n` limbs with `β^(2n) ≤ 4 N`, the
root of `N` by `sqrtRemAux` is shifted back by `c` bits, and the remainder is `a - s²`.
-/
public def sqrtRem (a : UInt64Array) : UInt64Array × UInt64Array :=
  let L := MPN.log2 a.toUSlice
  if L = 0 then (Num.low a 1, UInt64Array.replicate 0 0)
  else
    let n := L / 128 + 1
    let c := (128 * n - 1 - L) / 2
    let N := Num.low (Num.shl a (2 * c)) (2 * n)
    let S := Num.shr (sqrtRemAux N n).1 c
    (S, Num.sub a (Num.sqr S))

public theorem toNat_sqrtRem (a : UInt64Array) (hU : 2 * a.size + 40 < USize.size) :
    (sqrtRem a).1.toNat = _root_.Nat.sqrt a.toNat ∧
      (sqrtRem a).2.toNat = a.toNat - _root_.Nat.sqrt a.toNat * _root_.Nat.sqrt a.toNat := by
  have ha : a.size < USize.size := by lia
  have hA : a.toNat < 2 ^ (64 * a.size) := by rw [toNat_eq_valAt]; exact valAt_lt ..
  have hL : MPN.log2 a.toUSlice = _root_.Nat.log2 a.toNat := by
    rw [log2_eq, toUSlice_toNat a ha]
  unfold sqrtRem
  dsimp only
  rw [hL]
  generalize hl : _root_.Nat.log2 a.toNat = L
  split
  · rename_i h0
    -- `a ≤ 1`.
    have ha1 : a.toNat ≤ 1 := by
      by_cases h : a.toNat = 0
      · lia
      · have := Nat.lt_log2_self (n := a.toNat); rw [hl, h0] at this; lia
    have hs : _root_.Nat.sqrt a.toNat = a.toNat := by
      symm; apply eq_sqrt
      · rcases Nat.le_one_iff_eq_zero_or_eq_one.1 ha1 with h | h <;> rw [h] <;> decide
      · rcases Nat.le_one_iff_eq_zero_or_eq_one.1 ha1 with h | h <;> rw [h] <;> decide
    rw [Num.toNat_low _ _ ha, hs, Nat.mod_eq_of_lt (by lia)]
    refine ⟨rfl, ?_⟩
    rw [toNat_eq_valAt]
    rcases Nat.le_one_iff_eq_zero_or_eq_one.1 ha1 with h | h <;> rw [h] <;> simp
  · rename_i h0
    have ha0 : a.toNat ≠ 0 := by intro h; rw [h] at hl; simp at hl; lia
    have hlo : 2 ^ L ≤ a.toNat := by rw [← hl]; exact Nat.log2_self_le ha0
    have hhi : a.toNat < 2 ^ (L + 1) := by rw [← hl]; exact Nat.lt_log2_self
    have hLa : L < 64 * a.size := by
      refine Nat.lt_of_not_le fun h => ?_
      have := Nat.pow_le_pow_right (show 0 < 2 by decide) h
      lia
    generalize hn : L / 128 + 1 = n
    generalize hc : (128 * n - 1 - L) / 2 = c
    have hLn : L < 128 * n := by lia
    have hc₁ : 128 * n - 2 ≤ L + 2 * c := by lia
    have hc₂ : L + 2 * c + 1 ≤ 128 * n := by lia
    -- The normalized value `N = a 4ᶜ` of `2 n` limbs.
    have hshs : (Num.shl a (2 * c)).size = 2 * c / 64 + a.size + 1 := Num.size_shl ..
    have hshv : (Num.shl a (2 * c)).toNat = a.toNat * 2 ^ (2 * c) :=
      Num.toNat_shl _ _ (by lia)
    have hNlt : a.toNat * 2 ^ (2 * c) < 2 ^ (128 * n) := by
      calc a.toNat * 2 ^ (2 * c) < 2 ^ (L + 1) * 2 ^ (2 * c) :=
            Nat.mul_lt_mul_of_pos_right hhi (Nat.two_pow_pos _)
        _ = 2 ^ (L + 2 * c + 1) := by rw [← Nat.pow_add]; congr 1; lia
        _ ≤ 2 ^ (128 * n) := Nat.pow_le_pow_right (by decide) hc₂
    have hNge : 2 ^ (128 * n) ≤ 4 * (a.toNat * 2 ^ (2 * c)) := by
      calc 2 ^ (128 * n) ≤ 2 ^ (L + 2 * c + 2) := Nat.pow_le_pow_right (by decide) (by lia)
        _ = 4 * (2 ^ L * 2 ^ (2 * c)) := by
            rw [show (4 : Nat) = 2 ^ 2 by rfl, ← Nat.pow_add, ← Nat.pow_add]; congr 1; lia
        _ ≤ 4 * (a.toNat * 2 ^ (2 * c)) :=
            Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ hlo)
    have hNs : (Num.low (Num.shl a (2 * c)) (2 * n)).size = 2 * n := by
      rw [Num.size_low _ _ (by lia), hshs]
      lia
    have hNv : (Num.low (Num.shl a (2 * c)) (2 * n)).toNat = a.toNat * 2 ^ (2 * c) := by
      rw [Num.toNat_low _ _ (by lia), hshv, Nat.mod_eq_of_lt (by
        rw [show 64 * (2 * n) = 128 * n by lia]; exact hNlt)]
    obtain ⟨i₁, -, i₃, -⟩ := sqrtRemAux_spec _ n (by lia) hNs (by rw [hNv]; exact hNge)
      (by lia)
    rw [hNv] at i₃
    generalize (sqrtRemAux (Num.low (Num.shl a (2 * c)) (2 * n)) n).1 = S at i₁ i₃
    have hSv : (Num.shr S c).toNat = _root_.Nat.sqrt a.toNat := by
      rw [Num.toNat_shr _ _ (by lia), i₃, sqrt_mul_four_pow]
    have hSs : (Num.shr S c).size ≤ n := by rw [Num.size_shr]; lia
    refine ⟨hSv, ?_⟩
    rw [Num.toNat_sub _ _ (by rw [Num.toNat_sqr _ (by lia), hSv]; exact Nat.sqrt_le _) ha
      (by have := Num.size_sqr_le (Num.shr S c); lia), Num.toNat_sqr _ (by lia), hSv]

end MPN
