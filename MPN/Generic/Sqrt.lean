/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import MPN.Generic.Ops

/-!
# Square root, at any base

`NatOps.sqrtRemAux base T N n` computes `⌊√N⌋` and the remainder `N - ⌊√N⌋²` for `N < B²ⁿ` with
`B²ⁿ ≤ 4 N`, by Zimmermann's Karatsuba square root, like GMP's `mpn_dc_sqrtrem`: with `B' = Bˡ`
for `l = ⌊n / 2⌋`, `N = N₁ B'² + a₁ B' + a₀`, the root `t` of `N₁` and its remainder recursively,
then the quotient `q` and the remainder `u` of `(N₁ - t²) B' + a₁` by `2 t` give the root `t B' + q`
or one less (`karatsuba_sqrt`); the division is by `t`, whose top limb is at least `B / 2`, and its
quotient is halved. Up to `T` limbs, or at one, the instance's `base` takes over; the
instance normalizes by `4ᶜ` before calling. The facts about `Nat.sqrt` here serve both libraries.
From `main64`'s `MPN.Sqrt`, at any even base.
-/

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
public theorem split3 (N B : Nat) : N = N / (B * B) * B * B + N / B % B * B + N % B := by
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
public theorem mod_two_mul (X s : Nat) (hs : 0 < s) : X % (2 * s) = 2 * (X / 2 % s) + X % 2 := by
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
public theorem sqrt_lt_of {N P : Nat} (h : N < P * P) : _root_.Nat.sqrt N < P := by
  refine Nat.lt_of_not_le fun hge => ?_
  have := Nat.mul_self_le_mul_self hge
  have := Nat.sqrt_le N
  lia

/-- The remainder of the root is at most twice the root. -/
public theorem sqrt_rem_le (N : Nat) :
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

namespace NatOps

variable {α : Type} (o : NatOps α)

/-! ## The recursion -/

/--
`(⌊√N⌋, N - ⌊√N⌋²)` for `N < B²ⁿ` with `B²ⁿ ≤ 4 N`, by Zimmermann's step with `B' = Bˡ`,
`l = ⌊n / 2⌋`, on the root of the top `2 (n - l)` limbs, and by `base` up to `T` limbs.
-/
public def sqrtRemAux (base : α → α × α) (T : Nat) (N : α) (n : Nat) : α × α :=
  if _hn : n ≤ T ∨ n ≤ 1 then base N
  else
    let l := n / 2
    let p := sqrtRemAux base T (o.hi (l + l) N) (n - l)
    let X := o.add (o.shl l p.2) (o.lo l (o.hi l N))
    -- `X` by `2 t` from `X = q₁ t + r₁`: `q = ⌊q₁ / 2⌋`, `u = (q₁ mod 2) t + r₁`, so that the
    -- divisor is `t`, whose top limb is at least `B / 2`.
    let d₁ := o.divRem X p.1
    let h := o.divRem d₁.1 (o.add o.one o.one)
    let q := h.1
    let u := if o.le o.one h.2 then o.add p.1 d₁.2 else d₁.2
    let s := o.add (o.shl l p.1) q
    let U := o.add (o.shl l u) (o.lo l N)
    let q₂ := o.mul q q
    if o.le q₂ U then (s, o.sub U q₂)
    else (o.sub s o.one, o.sub (o.add U (o.sub (o.add s s) o.one)) q₂)
termination_by n
decreasing_by lia

public theorem sqrtRemAux_spec (base : α → α × α) (T : Nat)
    (hbase : ∀ N n, 1 ≤ n → (n ≤ T ∨ n ≤ 1) → o.val N < o.B ^ (2 * n) →
      o.B ^ (2 * n) ≤ 4 * o.val N →
      o.val (base N).1 = Nat.sqrt (o.val N) ∧
        o.val (base N).2 = o.val N - Nat.sqrt (o.val N) * Nat.sqrt (o.val N))
    (hB : 2 ∣ o.B) (n : Nat) : ∀ N : α, 1 ≤ n → o.val N < o.B ^ (2 * n) →
      o.B ^ (2 * n) ≤ 4 * o.val N →
      o.val (o.sqrtRemAux base T N n).1 = Nat.sqrt (o.val N) ∧
        o.val (o.sqrtRemAux base T N n).2 = o.val N - Nat.sqrt (o.val N) * Nat.sqrt (o.val N) := by
  have hBpos : ∀ m, 0 < o.B ^ m := fun _ => Nat.pow_pos (by have := o.one_lt_B; lia)
  induction n using Nat.strongRecOn with
  | ind n ih =>
  intro N hn hNlt hnorm
  rw [sqrtRemAux]
  split
  · rename_i h
    exact hbase N n hn h hNlt hnorm
  · rename_i h
    dsimp only
    generalize hl : n / 2 = l
    have hl1 : 1 ≤ l := by lia
    have hln : l ≤ n - l := by lia
    generalize hh : n - l = h' at hln
    have hnl : n = h' + l := by lia
    subst hnl
    -- `B' = Bˡ`, and the top part `N₁ = N / B'²` with its root `t`.
    generalize hB' : o.B ^ l = B at *
    have hB0 : 0 < B := by rw [← hB']; exact hBpos _
    have hBB : o.B ^ (l + l) = B * B := by rw [Nat.pow_add, hB']
    have hP : o.B ^ (2 * (h' + l)) = o.B ^ (2 * h') * (B * B) := by
      rw [← hBB, ← Nat.pow_add]; congr 1; lia
    have hN₁v : o.val (o.hi (l + l) N) = o.val N / (B * B) := by rw [o.val_hi, hBB]
    -- `4 ∣ B^(2h')`, so the normalization passes to `N₁`.
    have h4 : 4 ∣ o.B ^ (2 * h') := by
      obtain ⟨c, hc⟩ := hB
      refine ⟨c * c * o.B ^ (2 * h' - 2), ?_⟩
      rw [show 2 * h' = 2 + (2 * h' - 2) by lia, Nat.pow_add, hc]
      grind
    obtain ⟨Q, hQ⟩ := h4
    have hnorm₁ : o.B ^ (2 * h') ≤ 4 * (o.val N / (B * B)) := by
      rw [hQ]
      apply Nat.mul_le_mul_left
      apply (Nat.le_div_iff_mul_le (Nat.mul_pos hB0 hB0)).2
      rw [hP, hQ] at hnorm
      have : 4 * (Q * (B * B)) ≤ 4 * o.val N := by rw [← Nat.mul_assoc]; exact hnorm
      lia
    have hN₁lt : o.val N / (B * B) < o.B ^ (2 * h') := by
      apply (Nat.div_lt_iff_lt_mul (Nat.mul_pos hB0 hB0)).2
      rw [← hP]; exact hNlt
    obtain ⟨i₃, i₄⟩ := ih h' (by lia) _ (by lia) (by rw [hN₁v]; exact hN₁lt)
      (by rw [hN₁v]; exact hnorm₁)
    clear ih
    rw [hN₁v] at i₃ i₄
    generalize o.sqrtRemAux base T (o.hi (l + l) N) h' = p at i₃ i₄ ⊢
    generalize hN₁ : o.val N / (B * B) = N₁ at i₃ i₄ hnorm₁ hN₁lt
    generalize ht : Nat.sqrt N₁ = t at i₃ i₄
    -- `B' ≤ 2 t`, from the normalization of the top part.
    have hH : o.B ^ (2 * h') = o.B ^ h' * o.B ^ h' := by rw [← Nat.pow_add]; congr 1; lia
    obtain ⟨c, hc⟩ := hB
    have hHc : o.B ^ h' = 2 * (c * o.B ^ (h' - 1)) := by
      rw [show h' = 1 + (h' - 1) by lia, Nat.pow_add, Nat.pow_one, hc]; grind
    generalize hk : c * o.B ^ (h' - 1) = k at hHc
    have htge : k ≤ t := by
      rw [← ht]
      apply le_sqrt_of
      rw [hH, hHc] at hnorm₁
      have : 2 * k * (2 * k) = 4 * (k * k) := by grind
      lia
    have hBt : B ≤ 2 * t := by
      have : B ≤ o.B ^ h' := by rw [← hB']; exact Nat.pow_le_pow_right (by have := o.one_lt_B; lia) hln
      lia
    have ht0 : 0 < t := by
      have : 0 < o.B ^ h' := hBpos _
      lia
    -- The parts `a₁` and `a₀`.
    have hA₁v : o.val (o.lo l (o.hi l N)) = o.val N / B % B := by
      rw [o.val_lo, o.val_hi, hB']
    have hA₀v : o.val (o.lo l N) = o.val N % B := by rw [o.val_lo, hB']
    -- `X = r' B' + a₁`, and its quotient and remainder by `2 t`.
    have hXv : o.val (o.add (o.shl l p.2) (o.lo l (o.hi l N))) =
        (N₁ - t * t) * B + o.val N / B % B := by
      rw [o.val_add, o.val_shl, hB', i₄, hA₁v]
    generalize o.add (o.shl l p.2) (o.lo l (o.hi l N)) = X at hXv ⊢
    generalize hXn : (N₁ - t * t) * B + o.val N / B % B = Xn at hXv
    obtain ⟨e₁, e₂⟩ := o.val_divRem X p.1 (by rw [i₃]; lia)
    rw [hXv, i₃] at e₁ e₂
    generalize o.divRem X p.1 = d at e₁ e₂ ⊢
    have h2 : o.val (o.add o.one o.one) = 2 := by rw [o.val_add, o.val_one]
    obtain ⟨f₁, f₂⟩ := o.val_divRem d.1 (o.add o.one o.one) (by rw [h2]; lia)
    rw [e₁, h2, Nat.div_div_eq_div_mul, Nat.mul_comm t 2] at f₁
    rw [e₁, h2] at f₂
    generalize o.divRem d.1 (o.add o.one o.one) = hd at f₁ f₂ ⊢
    -- `u = (q₁ mod 2) t + r₁ = X mod 2 t`.
    have huv : o.val (if o.le o.one hd.2 = true then o.add p.1 d.2 else d.2) = Xn % (2 * t) := by
      have hmod : Xn % (2 * t) = Xn / t % 2 * t + Xn % t := by
        rw [Nat.mul_comm 2 t, Nat.mod_mul, Nat.mul_comm t]; lia
      have hm2 := Nat.mod_lt (Xn / t) (show 0 < 2 by decide)
      split
      · rename_i hc
        rw [o.le_iff, o.val_one, f₂] at hc
        have hb : Xn / t % 2 = 1 := by lia
        rw [o.val_add, i₃, e₂, hmod, hb, Nat.one_mul]
      · rename_i hc
        rw [o.le_iff, o.val_one, f₂] at hc
        have hb : Xn / t % 2 = 0 := by lia
        rw [e₂, hmod, hb, Nat.zero_mul, Nat.zero_add]
    generalize (if o.le o.one hd.2 = true then o.add p.1 d.2 else d.2) = u at huv ⊢
    -- `s = t B' + q` and `U = u B' + a₀`.
    have hsv : o.val (o.add (o.shl l p.1) hd.1) = t * B + Xn / (2 * t) := by
      rw [o.val_add, o.val_shl, hB', i₃, f₁]
    generalize o.add (o.shl l p.1) hd.1 = sv at hsv ⊢
    have hUv : o.val (o.add (o.shl l u) (o.lo l N)) = Xn % (2 * t) * B + o.val N % B := by
      rw [o.val_add, o.val_shl, hB', huv, hA₀v]
    generalize o.add (o.shl l u) (o.lo l N) = U at hUv ⊢
    have hq₂v : o.val (o.mul hd.1 hd.1) = Xn / (2 * t) * (Xn / (2 * t)) := by
      rw [o.val_mul, f₁]
    generalize o.mul hd.1 hd.1 = q₂ at hq₂v ⊢
    -- Zimmermann's step.
    have hsplit := split3 (o.val N) B
    rw [hN₁] at hsplit
    obtain ⟨k₁, k₂⟩ := karatsuba_sqrt (B := B) (N' := N₁) (a₁ := o.val N / B % B)
      (a₀ := o.val N % B) (t := t) (q := Xn / (2 * t)) (u := Xn % (2 * t)) ht.symm
      (Nat.mod_lt _ hB0) (Nat.mod_lt _ hB0) hBt (by rw [hXn]) (by rw [hXn])
    rw [← hsplit] at k₁ k₂
    split
    · rename_i hle
      rw [o.le_iff, hq₂v, hUv] at hle
      obtain ⟨e₁, e₂⟩ := k₁ hle
      refine ⟨by rw [hsv, ← e₁], ?_⟩
      rw [o.val_sub _ _ (by rw [hq₂v, hUv]; exact hle), hUv, hq₂v, ← e₂, e₁]
    · rename_i hle
      rw [o.le_iff, hq₂v, hUv] at hle
      obtain ⟨e₁, e₂, e₃, e₄⟩ := k₂ (by lia)
      have hs1 : o.val (o.sub sv o.one) = t * B + Xn / (2 * t) - 1 := by
        rw [o.val_sub _ _ (by rw [o.val_one, hsv]; lia), hsv, o.val_one]
      have hs2 : o.val (o.sub (o.add sv sv) o.one) = 2 * (t * B + Xn / (2 * t)) - 1 := by
        rw [o.val_sub _ _ (by rw [o.val_one, o.val_add, hsv]; lia), o.val_add, hsv, o.val_one]
        lia
      have hadd : o.val (o.add U (o.sub (o.add sv sv) o.one)) =
          Xn % (2 * t) * B + o.val N % B + (2 * (t * B + Xn / (2 * t)) - 1) := by
        rw [o.val_add, hUv, hs2]
      refine ⟨by rw [hs1, ← e₁], ?_⟩
      rw [o.val_sub _ _ (by rw [hadd, hq₂v]; exact e₄), hadd, hq₂v, ← e₂, e₁]

end NatOps

end MPN
