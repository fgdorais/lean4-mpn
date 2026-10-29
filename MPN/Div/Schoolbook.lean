/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import MPN.WordArray

/-!
# Schoolbook division, for limbs of any width

The core of Knuth's Algorithm D, like GMP's schoolbook division, on arrays of limbs of `w` bits,
`β = 2ʷ`, over `WordArray` and `WordFolds`: one quotient limb per step from the top down. At the
step for window `i`, the remainder `R` so far is below `v βⁱ⁺¹`, so the quotient limb is
`⌊W / v⌋ < β`, where `W` is the window of limbs `i` to `i + n` of `R`.

The limb is estimated by `qEst` from the top three limbs of `W` and the top two of `v`, as in
Algorithm D. The step subtracts the estimate times `v` from the window in place, and adds `v` back
while the window is negative (`addBack`). Correctness only needs the estimate never to be too
small, which `qEst_ge` proves; that it is rarely too large, when the top limb of `v` is at least
`β / 2`, is only a matter of speed, and the callers normalize the divisor for it. Given the
reciprocal of the top two limbs of `v`, the estimate is instead GMP's 3-by-2 step (`qEstR`),
checked exactly, with `qEst` when a check fails, so that neither the reciprocal nor the error of
the step needs a proof.

The division works in one array (`divLoopIn`): after the step for window `i`, its remainder is
below `v`, so the top limb `i + n` of the window is free, and the step writes the quotient limb
there (`divStepIn`). The multiply-subtract pass is the in-place fold `foldThen`, ended by a
continuation, so that a step allocates nothing unless the estimate was too large. At the end the
limbs below `n` are the remainder and the limbs from `n` on the quotient. The divisor is another
array, read from an offset.
-/

namespace MPN.Schoolbook

open WordArray

/-! ## Arithmetic -/

/-- One correction: when `q (v₁ β + v₂)` exceeds the dividend, every `Q` below it is below `q`. -/
private theorem qEst_dec {Q q r v₁ v₂ W₂ w₀ B : Nat}
    (hW : v₁ * q + r = W₂) (hQ : Q * (v₁ * B + v₂) ≤ W₂ * B + w₀)
    (hgt : r * B + w₀ < q * v₂) : Q < q := by
  refine Nat.lt_of_not_le fun hle => ?_
  have h₁ := Nat.mul_le_mul_right (v₁ * B + v₂) hle
  have e₁ : q * (v₁ * B + v₂) = v₁ * q * B + q * v₂ := by grind
  have e₂ : W₂ * B = v₁ * q * B + r * B := by rw [← hW, Nat.add_mul]
  lia

/-- The quotient of the top two limbs by `v₁` is never too small. -/
private theorem qEst_top {Q q r v₁ v₂ W₂ w₀ B : Nat} (hW : v₁ * q + r = W₂) (hr : r < v₁)
    (hw₀ : w₀ < B) (hQ : Q * (v₁ * B + v₂) ≤ W₂ * B + w₀) : Q ≤ q := by
  refine Nat.le_of_not_lt fun hlt => ?_
  have h₁ := Nat.mul_le_mul_right (v₁ * B + v₂) (show q + 1 ≤ Q from hlt)
  have h₂ := Nat.mul_le_mul_right B (show r + 1 ≤ v₁ from hr)
  have e₁ : (q + 1) * (v₁ * B + v₂) = v₁ * q * B + v₁ * B + (q + 1) * v₂ := by grind
  have e₂ : W₂ * B = v₁ * q * B + r * B := by rw [← hW, Nat.add_mul]
  rw [Nat.add_mul, Nat.one_mul] at h₂
  lia

variable {A L : Type} [LA : LimbArray A L] [R : WordArray A L]

/-- `x - 1` for a limb `x ≥ 1`. -/
private theorem val_sub_one (x : L) (h : 1 ≤ LA.val x) : LA.val (R.sub x R.one) = LA.val x - 1 := by
  have := LA.val_lt x; have := four_le (R := R)
  rw [R.val_sub, R.val_one, show LA.val x + (2 ^ LA.w - 1) = (LA.val x - 1) + 2 ^ LA.w * 1 by lia,
    Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by lia)]

/-- The limb of all ones. -/
private theorem val_ones : LA.val (R.sub R.zero R.one) = 2 ^ LA.w - 1 := by
  have := four_le (R := R)
  rw [R.val_sub, R.val_zero, R.val_one, Nat.zero_add, Nat.mod_eq_of_lt (by lia)]

/-- The low and high limbs of `q v₂`. -/
private theorem mul_words (q v₂ : L) :
    LA.val (R.mulh q v₂) * 2 ^ LA.w + LA.val (R.mul q v₂) = LA.val q * LA.val v₂ := by
  rw [R.val_mulh, R.val_mul, Nat.mul_comm]
  exact Nat.div_add_mod ..

/-- The quotient and remainder of `div2`. -/
private theorem div2_rem (hi lo d : L) (h : LA.val hi < LA.val d) :
    LA.val (R.sub lo (R.mul (R.div2 hi lo d) d)) = (LA.val hi * 2 ^ LA.w + LA.val lo) % LA.val d ∧
      LA.val d * LA.val (R.div2 hi lo d) + LA.val (R.sub lo (R.mul (R.div2 hi lo d) d)) =
        LA.val hi * 2 ^ LA.w + LA.val lo := by
  have hq := R.val_div2 hi lo d h
  have hd := LA.val_lt d; have hl := LA.val_lt lo
  rw [R.val_sub, R.val_mul, hq]
  generalize LA.val hi = H at *
  generalize LA.val lo = Lo at *
  generalize LA.val d = D at *
  generalize 2 ^ LA.w = B at *
  have hD : 0 < D := by lia
  have e := Nat.div_add_mod (H * B + Lo) D
  have hr := Nat.mod_lt (H * B + Lo) hD
  generalize (H * B + Lo) / D = q at *
  generalize (H * B + Lo) % D = r at *
  -- `m` is `q D` modulo `B`, and `m + r` is `Lo` or `Lo + B`.
  have hB : 0 < B := by lia
  have hm := Nat.mod_lt (q * D) hB
  have hmr : (q * D % B + r) % B = Lo := by
    rw [Nat.mod_add_mod, Nat.mul_comm, e, Nat.mul_comm, Nat.mul_add_mod, Nat.mod_eq_of_lt hl]
  have hk := carry_le (s := q * D % B + r) (B := B) (by lia)
  have e₂ := Nat.mod_add_div (q * D % B + r) B
  rw [hmr] at e₂
  generalize q * D % B = m at *
  generalize (m + r) / B = k at *
  have h₁ : (Lo + (B - m)) % B = r := by
    rcases Nat.lt_or_ge k 1 with h₀ | h₁
    · obtain rfl : k = 0 := by lia
      rw [show Lo + (B - m) = r + B * 1 by lia, Nat.add_mul_mod_self_left,
        Nat.mod_eq_of_lt (by lia)]
    · obtain rfl : k = 1 := by lia
      rw [show Lo + (B - m) = r by lia, Nat.mod_eq_of_lt (by lia)]
  exact ⟨h₁, by rw [h₁]; exact e⟩

/-! ## The estimate of a quotient limb -/

variable (A) in
/--
Whether `q v₂ > r β + w₀` for the limb `r`, where `h β + l = q v₂`: a comparison of double limbs.
-/
@[inline, expose] public def gt2 (h l r w₀ : L) : Bool :=
  R.ltB r h || (R.eqB h r && R.ltB w₀ l)

private theorem gt2_iff (h l r w₀ : L) :
    gt2 A h l r w₀ = true ↔
      LA.val r * 2 ^ LA.w + LA.val w₀ < LA.val h * 2 ^ LA.w + LA.val l := by
  have := LA.val_lt l; have := LA.val_lt w₀
  simp only [gt2, Bool.or_eq_true, Bool.and_eq_true, R.ltB_iff, R.eqB_iff]
  generalize LA.val h = H at *
  generalize LA.val r = Rr at *
  generalize LA.val l = Ll at *
  generalize LA.val w₀ = W at *
  generalize 2 ^ LA.w = B at *
  constructor
  · rintro (h₁ | ⟨h₁, h₂⟩)
    · have := Nat.mul_le_mul_right B (show Rr + 1 ≤ H from h₁)
      rw [Nat.add_mul, Nat.one_mul] at this
      lia
    · rw [h₁]; lia
  · intro h'
    rcases Nat.lt_trichotomy Rr H with h₁ | h₁ | h₁
    · exact .inl h₁
    · exact .inr ⟨h₁.symm, by rw [h₁] at h'; lia⟩
    · have := Nat.mul_le_mul_right B (show H + 1 ≤ Rr from h₁)
      rw [Nat.add_mul, Nat.one_mul] at this
      lia

variable (A) in
/--
The estimate of the quotient limb of `w₂ β² + w₁ β + w₀` by `v₁ β + v₂`, from the quotient `q` of
`w₂ β + w₁` by `v₁`, decreased at most twice while `q (v₁ β + v₂)` exceeds the dividend, as in
Algorithm D; `β - 1` when `w₂ ≥ v₁`.
-/
@[expose, specialize]
public def qEst (w₂ w₁ w₀ v₁ v₂ : L) : L :=
  if R.ltB w₂ v₁ then
    let q := R.div2 w₂ w₁ v₁
    let r := R.sub w₁ (R.mul q v₁)
    if gt2 A (R.mulh q v₂) (R.mul q v₂) r w₀ then
      let q := R.sub q R.one
      let r := R.add r v₁
      -- `r < v₁` when `r + v₁` overflows, and then `q v₂ < r β`.
      if R.ltB r v₁ then q
      else if gt2 A (R.mulh q v₂) (R.mul q v₂) r w₀ then R.sub q R.one else q
    else q
  else R.sub R.zero R.one

/--
The estimate is never too small: every `Q < β` with `Q (v₁ β + v₂) ≤ w₂ β² + w₁ β + w₀` is at most
`qEst w₂ w₁ w₀ v₁ v₂`.
-/
public theorem qEst_ge (w₂ w₁ w₀ v₁ v₂ : L) (Q : Nat) (hQβ : Q < 2 ^ LA.w)
    (hQ : Q * (LA.val v₁ * 2 ^ LA.w + LA.val v₂) ≤
      (LA.val w₂ * 2 ^ LA.w + LA.val w₁) * 2 ^ LA.w + LA.val w₀) :
    Q ≤ LA.val (qEst A w₂ w₁ w₀ v₁ v₂) := by
  rw [qEst]
  split
  · rename_i hw
    have hw' := (R.ltB_iff _ _).1 hw
    obtain ⟨hrem, hdq⟩ := div2_rem w₂ w₁ v₁ hw'
    have hr := Nat.mod_lt (LA.val w₂ * 2 ^ LA.w + LA.val w₁) (show 0 < LA.val v₁ by lia)
    rw [← hrem] at hr
    dsimp only
    generalize R.div2 w₂ w₁ v₁ = q at hdq hr ⊢
    generalize R.sub w₁ (R.mul q v₁) = r at hdq hr ⊢
    split
    · rename_i hg
      rw [gt2_iff, mul_words] at hg
      have h₁ := qEst_dec hdq hQ hg
      have hq₁ : LA.val (R.sub q R.one) = LA.val q - 1 := val_sub_one q (by lia)
      -- `r + v₁` as a limb, and whether it overflows.
      have hv := LA.val_lt v₁
      have hrv : LA.val (R.add r v₁) = (LA.val r + LA.val v₁) % 2 ^ LA.w := R.val_add ..
      split
      · rw [hq₁]; lia
      · rename_i hno
        have hno' : LA.val r + LA.val v₁ < 2 ^ LA.w := by
          rw [R.ltB_iff, hrv] at hno
          have hr64 := LA.val_lt r
          generalize 2 ^ LA.w = M at *
          refine Nat.lt_of_not_le fun hge => hno ?_
          rw [Nat.mod_eq_sub_mod hge, Nat.mod_eq_of_lt (by lia)]
          lia
        rw [Nat.mod_eq_of_lt hno'] at hrv
        split
        · rename_i hg₂
          rw [gt2_iff, mul_words, hrv, hq₁] at hg₂
          have hdq' : LA.val v₁ * (LA.val q - 1) + (LA.val r + LA.val v₁) =
              LA.val w₂ * 2 ^ LA.w + LA.val w₁ := by
            rw [Nat.mul_sub, Nat.mul_one]
            have : LA.val v₁ ≤ LA.val v₁ * LA.val q := Nat.le_mul_of_pos_right _ (by lia)
            lia
          have h₂ := qEst_dec hdq' hQ hg₂
          have hq₂ : LA.val (R.sub (R.sub q R.one) R.one) = LA.val q - 1 - 1 := by
            rw [val_sub_one _ (by rw [hq₁]; lia), hq₁]
          rw [hq₂]; lia
        · rw [hq₁]; lia
    · exact qEst_top hdq hr (LA.val_lt w₀) hQ
  · rw [val_ones]; lia

/-! ## The estimate with a precomputed reciprocal

GMP's schoolbook division estimates each quotient limb without the hardware divider, by Möller
and Granlund's 3-by-2 step (`udiv_qr_3by2`) with the reciprocal `⌊(β³ - 1) / (v₁ β + v₂)⌋ - β`
of the top two limbs of the normalized divisor (`invert_pi1`). `qEstR` checks the quotient and
remainder of the step exactly, `q (v₁ β + v₂) + r = w₂ β² + w₁ β + w₀` with `r < v₁ β + v₂`, by
four products off the dependency chain; then `q` is the quotient of the top three limbs by the
top two, which is never too small. Otherwise it takes `qEst`. So neither the reciprocal nor the
error bound of the step needs a proof, and the callers compute the reciprocal their own way.
-/

variable (A) in
/-- The carry out of `x + y`, as a limb. -/
@[inline, expose] public def carry (x y : L) : L := R.addh R.zero x y

private theorem carry_add (x y : L) :
    LA.val (carry A x y) * 2 ^ LA.w + LA.val (R.add x y) = LA.val x + LA.val y := by
  rw [carry, R.val_addh, R.val_add, R.val_zero, Nat.zero_add]
  have := LA.val_lt x; have := LA.val_lt y; have := four_le (R := R)
  rw [Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (carry_le (B := 2 ^ LA.w) (by lia)) (by lia))]
  have := Nat.div_add_mod (LA.val x + LA.val y) (2 ^ LA.w)
  rw [Nat.mul_comm] at this
  exact this

variable (A) in
/--
Whether `q (d₁ β + d₀) + r₁ β + r₀ = n₂ β² + n₁ β + n₀` and `r₁ β + r₀ < d₁ β + d₀`, exactly, by
the four products of `q` by the limbs of the divisor.
-/
@[inline, expose] public def div32Ok (n₂ n₁ n₀ d₁ d₀ q r₁ r₀ : L) : Bool :=
  let p₀ := R.mul q d₀
  let h₀ := R.mulh q d₀
  let p₁ := R.mul q d₁
  let h₁ := R.mulh q d₁
  let u := R.add h₀ p₁
  let c₀ := carry A p₀ r₀
  let s₁ := R.add (R.add u r₁) c₀
  let c₂ := R.add (carry A u r₁) (carry A (R.add u r₁) c₀)
  R.eqB (R.add p₀ r₀) n₀ && R.eqB s₁ n₁ && R.eqB (R.add (R.add h₁ (carry A h₀ p₁)) c₂) n₂ &&
    (R.ltB r₁ d₁ || (R.eqB r₁ d₁ && R.ltB r₀ d₀))

private theorem div32Ok_spec (n₂ n₁ n₀ d₁ d₀ q r₁ r₀ : L)
    (h : div32Ok A n₂ n₁ n₀ d₁ d₀ q r₁ r₀ = true) :
    LA.val q * (LA.val d₁ * 2 ^ LA.w + LA.val d₀) + (LA.val r₁ * 2 ^ LA.w + LA.val r₀) =
        (LA.val n₂ * 2 ^ LA.w + LA.val n₁) * 2 ^ LA.w + LA.val n₀ ∧
      LA.val r₁ * 2 ^ LA.w + LA.val r₀ < LA.val d₁ * 2 ^ LA.w + LA.val d₀ := by
  simp only [div32Ok, Bool.and_eq_true, Bool.or_eq_true, R.eqB_iff, R.ltB_iff] at h
  obtain ⟨⟨⟨e₀, e₁⟩, e₂⟩, hlt⟩ := h
  have hB4 := four_le (R := R)
  have hR : LA.val r₁ * 2 ^ LA.w + LA.val r₀ < LA.val d₁ * 2 ^ LA.w + LA.val d₀ := by
    have := LA.val_lt r₀
    rcases hlt with h | ⟨h₁, h₂⟩
    · have := Nat.mul_le_mul_right (2 ^ LA.w) (show LA.val r₁ + 1 ≤ LA.val d₁ by lia)
      rw [Nat.add_mul, Nat.one_mul] at this
      lia
    · rw [h₁]; lia
  refine ⟨?_, hR⟩
  -- The products and the carries, as equations.
  have m₀ := mul_words (A := A) q d₀
  have m₁ := mul_words (A := A) q d₁
  have k₀ := carry_add (A := A) (R.mul q d₀) r₀
  have k₁ := carry_add (A := A) (R.mulh q d₀) (R.mul q d₁)
  have k₂ := carry_add (A := A) (R.add (R.mulh q d₀) (R.mul q d₁)) r₁
  have k₃ := carry_add (A := A) (R.add (R.add (R.mulh q d₀) (R.mul q d₁)) r₁)
    (carry A (R.mul q d₀) r₀)
  rw [R.val_add, R.val_add, R.val_add] at e₂
  have hq := LA.val_lt q
  have hd₁ := LA.val_lt d₁; have hd₀ := LA.val_lt d₀
  have hr₁ := LA.val_lt r₁; have hr₀ := LA.val_lt r₀
  generalize LA.val (carry A (R.add (R.add (R.mulh q d₀) (R.mul q d₁)) r₁)
    (carry A (R.mul q d₀) r₀)) = c₄ at *
  generalize LA.val (carry A (R.add (R.mulh q d₀) (R.mul q d₁)) r₁) = c₃ at *
  generalize LA.val (carry A (R.mulh q d₀) (R.mul q d₁)) = c₁ at *
  generalize LA.val (carry A (R.mul q d₀) r₀) = c₀ at *
  generalize LA.val (R.add (R.add (R.add (R.mulh q d₀) (R.mul q d₁)) r₁)
    (carry A (R.mul q d₀) r₀)) = s₁ at *
  generalize LA.val (R.add (R.add (R.mulh q d₀) (R.mul q d₁)) r₁) = s at *
  generalize LA.val (R.add (R.mulh q d₀) (R.mul q d₁)) = u at *
  generalize LA.val (R.add (R.mul q d₀) r₀) = s₀ at *
  generalize LA.val (R.mulh q d₀) = Hh at *
  generalize LA.val (R.mulh q d₁) = Hb at *
  generalize LA.val (R.mul q d₀) = a at *
  generalize LA.val (R.mul q d₁) = b at *
  generalize LA.val q = Q at *
  generalize LA.val d₁ = D₁ at *
  generalize LA.val d₀ = D₀ at *
  generalize LA.val r₁ = R₁ at *
  generalize LA.val r₀ = R₀ at *
  generalize LA.val n₂ = N₂ at *
  subst e₀ e₁
  generalize LA.val n₁ = s₁ at *
  generalize LA.val n₀ = s₀ at *
  generalize 2 ^ LA.w = B at *
  -- The whole, with the top limb `T` before it is reduced.
  have m₁B := congrArg (· * B) m₁
  have k₁B := congrArg (· * B) k₁
  have k₂B := congrArg (· * B) k₂
  have k₃B := congrArg (· * B) k₃
  have hT : Q * (D₁ * B + D₀) + (R₁ * B + R₀) = ((Hb + c₁ + c₃ + c₄) * B + s₁) * B + s₀ := by
    grind
  -- `T < B`, since the whole is below `B (D₁ B + D₀) < B³`.
  have hX : D₁ * B + D₀ < B * B := by
    have := Nat.mul_le_mul_right B (show D₁ + 1 ≤ B by lia)
    rw [Nat.add_mul, Nat.one_mul] at this
    lia
  have hbig : Q * (D₁ * B + D₀) + (R₁ * B + R₀) < B * (B * B) := by
    have h₁ : Q * (D₁ * B + D₀) + (R₁ * B + R₀) < (Q + 1) * (D₁ * B + D₀) := by
      rw [Nat.succ_mul]; lia
    have h₂ := Nat.mul_le_mul_right (D₁ * B + D₀) (show Q + 1 ≤ B by lia)
    have h₃ := Nat.mul_lt_mul_of_pos_left hX (show 0 < B by lia)
    lia
  have hTB : Hb + c₁ + c₃ + c₄ < B := by
    refine Nat.lt_of_not_le fun hle => ?_
    have h₁ := Nat.mul_le_mul_right (B * B) hle
    have h₂ : ((Hb + c₁ + c₃ + c₄) * B + s₁) * B + s₀ =
        (Hb + c₁ + c₃ + c₄) * (B * B) + (s₁ * B + s₀) := by
      generalize Hb + c₁ + c₃ + c₄ = T
      rw [Nat.add_mul, Nat.mul_assoc]; lia
    have : B * (B * B) = B * B * B := (Nat.mul_assoc ..).symm
    lia
  rw [← Nat.add_mod, show Hb + c₁ + (c₃ + c₄) = Hb + c₁ + c₃ + c₄ by lia,
    Nat.mod_eq_of_lt hTB] at e₂
  rw [hT, e₂]

variable (A) in
/--
The estimate of the quotient limb of `w₂ β² + w₁ β + w₀` by `v₁ β + v₂` by the 3-by-2 step with
the reciprocal `dv`, checked by `div32Ok`; `qEst` when the check fails.
-/
@[expose, specialize]
public def qEstR (dv w₂ w₁ w₀ v₁ v₂ : L) : L :=
  let q₀ := R.mul dv w₂
  let q₁ := R.addh (R.add (R.mulh dv w₂) w₂) q₀ w₁
  let q₀ := R.add q₀ w₁
  let r₁ := R.sub w₁ (R.mul v₁ q₁)
  -- `(r₁, r₀) = (r₁, w₀) - (v₁, v₂) - v₂ q₁`.
  let r₁ := R.sub (R.sub r₁ v₁) (R.subh R.zero w₀ v₂)
  let r₀ := R.sub w₀ v₂
  let t₁ := R.mulh v₂ q₁
  let t₀ := R.mul v₂ q₁
  let r₁ := R.sub (R.sub r₁ t₁) (R.subh R.zero r₀ t₀)
  let r₀ := R.sub r₀ t₀
  let q₁ := R.add q₁ R.one
  let mask := R.sub R.zero (R.ofBool (!R.ltB r₁ q₀))
  let q₁ := R.add q₁ mask
  let r₁ := R.addh (R.add r₁ (R.land mask v₁)) r₀ (R.land mask v₂)
  let r₀ := R.add r₀ (R.land mask v₂)
  let fix := R.ofBool (R.ltB v₁ r₁ || (R.eqB r₁ v₁ && !R.ltB r₀ v₂))
  let m := R.sub R.zero fix
  let q₁ := R.add q₁ fix
  let r₁' := R.sub (R.sub r₁ (R.land m v₁)) (R.subh R.zero r₀ (R.land m v₂))
  let r₀ := R.sub r₀ (R.land m v₂)
  if div32Ok A w₂ w₁ w₀ v₁ v₂ q₁ r₁' r₀ then q₁ else qEst A w₂ w₁ w₀ v₁ v₂

/-- `qEstR` is never too small, like `qEst`. -/
public theorem qEstR_ge (dv w₂ w₁ w₀ v₁ v₂ : L) (Q : Nat) (hQβ : Q < 2 ^ LA.w)
    (hQ : Q * (LA.val v₁ * 2 ^ LA.w + LA.val v₂) ≤
      (LA.val w₂ * 2 ^ LA.w + LA.val w₁) * 2 ^ LA.w + LA.val w₀) :
    Q ≤ LA.val (qEstR A dv w₂ w₁ w₀ v₁ v₂) := by
  obtain ⟨q, r₁, r₀, e⟩ : ∃ q r₁ r₀, qEstR A dv w₂ w₁ w₀ v₁ v₂ =
      if div32Ok A w₂ w₁ w₀ v₁ v₂ q r₁ r₀ then q else qEst A w₂ w₁ w₀ v₁ v₂ := ⟨_, _, _, rfl⟩
  rw [e]; clear e
  split
  · rename_i hok
    obtain ⟨e, hr⟩ := div32Ok_spec _ _ _ _ _ _ _ _ hok
    have h : Q * (LA.val v₁ * 2 ^ LA.w + LA.val v₂) <
        (LA.val q + 1) * (LA.val v₁ * 2 ^ LA.w + LA.val v₂) := by
      rw [Nat.succ_mul]; exact Nat.lt_of_le_of_lt hQ (by rw [← e]; exact Nat.add_lt_add_left hr _)
    exact Nat.le_of_lt_succ (Nat.lt_of_mul_lt_mul_right h)
  · exact qEst_ge w₂ w₁ w₀ v₁ v₂ Q hQβ hQ

variable (A) in
/-- `qEstR` with the reciprocal `dv`, or `qEst` when there is none, `dv = 0`. -/
@[inline, expose] public def qEstD (dv w₂ w₁ w₀ v₁ v₂ : L) : L :=
  if R.isZero dv then qEst A w₂ w₁ w₀ v₁ v₂ else qEstR A dv w₂ w₁ w₀ v₁ v₂

public theorem qEstD_ge (dv w₂ w₁ w₀ v₁ v₂ : L) (Q : Nat) (hQβ : Q < 2 ^ LA.w)
    (hQ : Q * (LA.val v₁ * 2 ^ LA.w + LA.val v₂) ≤
      (LA.val w₂ * 2 ^ LA.w + LA.val w₁) * 2 ^ LA.w + LA.val w₀) :
    Q ≤ LA.val (qEstD A dv w₂ w₁ w₀ v₁ v₂) := by
  rw [qEstD]; split
  · exact qEst_ge w₂ w₁ w₀ v₁ v₂ Q hQβ hQ
  · exact qEstR_ge dv w₂ w₁ w₀ v₁ v₂ Q hQβ hQ

/-! ## The passes

The multiply-subtract pass and the add-back pass of a step, over limbs `rs` to `rs + n - 1` of the
array and limbs `vs` to `vs + n - 1` of the divisor `v`, another array.
-/

/-- One limb of the multiply-subtract pass: limb `z` less limb `j` of `v x` and the borrow. -/
@[inline, expose] public def subMulStep (v : A) (vs n : USize) (hv : LoopBound v vs n) (x : L)
    (j : USize) (h : j < n) (z c : L) : L × L :=
  R.subMulC z (R.uget v (vs + j) (hv.uset_bound h)) x c

/-- One limb of the add-back pass: limb `z` plus limb `j` of `v` and the carry. -/
@[inline, expose] public def addVStep (v : A) (vs n : USize) (hv : LoopBound v vs n) (j : USize)
    (h : j < n) (z c : L) : L × L :=
  R.addC z (R.uget v (vs + j) (hv.uset_bound h)) c

public theorem subMulFold_spec (arr : A) (rs : USize) (v : A) (vs n : USize)
    (hv : LoopBound v vs n) (hr : LoopBound arr rs n) (x : L) (j : USize) (c : L) :
    LA.size (foldUInPlace n (subMulStep v vs n hv x) arr rs hr j c).1 = LA.size arr ∧
      (∀ i, (i < rs.toNat + j.toNat ∨ rs.toNat + n.toNat ≤ i) →
        LA.get (foldUInPlace n (subMulStep v vs n hv x) arr rs hr j c).1 i = LA.get arr i) ∧
      LimbArray.valAt (foldUInPlace n (subMulStep v vs n hv x) arr rs hr j c).1
          (rs.toNat + j.toNat) (n.toNat - j.toNat) +
          LimbArray.valAt v (vs.toNat + j.toNat) (n.toNat - j.toNat) * LA.val x + LA.val c =
        LimbArray.valAt arr (rs.toNat + j.toNat) (n.toNat - j.toNat) +
          2 ^ (LA.w * (n.toNat - j.toNat)) *
            LA.val (foldUInPlace n (subMulStep v vs n hv x) arr rs hr j c).2 := by
  induction arr, hr, j, c using foldUInPlace.induct (R := R) n (subMulStep v vs n hv x) rs with
  | case1 arr hr j c h p ih =>
    rw [foldUInPlace]
    simp only [h, ↓reduceDIte]
    have hj := USize.lt_iff_toNat_lt.1 h
    have hj₁ := USize.toNat_add_one_of_lt h
    have hidx := hr.toNat_add h
    have hvi := hv.toNat_add h
    obtain ⟨ih₁, ih₂, ih₃⟩ := ih
    rw [hj₁] at ih₂ ih₃
    rw [R.size_uset] at ih₁
    have hv' : LA.get (foldUInPlace n (subMulStep v vs n hv x)
        (R.uset arr (rs + j) p.1 (hr.uset_bound h)) rs (hr.of_uset ..) (j + 1) p.2).1
          (rs.toNat + j.toNat) = p.1 := by
      rw [ih₂ _ (.inl (by lia)), R.get_uset]
      simp [hidx]
    have hr' : LimbArray.valAt (R.uset arr (rs + j) p.1 (hr.uset_bound h))
        (rs.toNat + (j.toNat + 1)) (n.toNat - (j.toNat + 1)) =
          LimbArray.valAt arr (rs.toNat + (j.toNat + 1)) (n.toNat - (j.toNat + 1)) :=
      valAt_uset_of _ _ _ _ _ _ (by rw [hidx]; lia)
    have hz : R.uget arr (rs + j) (hr.uset_bound h) = LA.get arr (rs.toNat + j.toNat) := by
      rw [R.uget_eq, hidx]
    have hy : R.uget v (vs + j) (hv.uset_bound h) = LA.get v (vs.toNat + j.toNat) := by
      rw [R.uget_eq, hvi]
    have hl := R.val_subMulC (R.uget arr (rs + j) (hr.uset_bound h))
      (R.uget v (vs + j) (hv.uset_bound h)) x c
    rw [hz, hy] at hl
    refine ⟨ih₁, fun i hi => ?_, ?_⟩
    · rw [ih₂ i (by lia), R.get_uset]
      simp only [hidx]
      split <;> lia
    · rw [hr'] at ih₃
      obtain ⟨k, hk⟩ : ∃ k, n.toNat - j.toNat = k + 1 := ⟨n.toNat - j.toNat - 1, by lia⟩
      rw [show n.toNat - (j.toNat + 1) = k by lia, ← Nat.add_assoc, ← Nat.add_assoc] at ih₃
      rw [hk, LimbArray.valAt_succ, LimbArray.valAt_succ, LimbArray.valAt_succ, hv', Nat.mul_succ,
        Nat.pow_add]
      generalize foldUInPlace n (subMulStep v vs n hv x) (R.uset arr (rs + j) p.1 (hr.uset_bound h))
        rs (hr.of_uset ..) (j + 1) p.2 = q at *
      simp only [p, subMulStep, hz, hy] at *
      generalize LimbArray.valAt q.1 _ _ = V at *
      generalize LimbArray.valAt arr (rs.toNat + j.toNat + 1) k = X at *
      generalize LimbArray.valAt v (vs.toNat + j.toNat + 1) k = Y at *
      generalize LA.val q.2 = c' at *
      generalize 2 ^ (LA.w * k) = P at *
      generalize 2 ^ LA.w = B at *
      grind
  | case2 arr hr j c h =>
    rw [foldUInPlace]
    have : n.toNat - j.toNat = 0 := by have := USize.lt_iff_toNat_lt (a := j) (b := n); lia
    simp [h, this]

public theorem addVFold_spec (arr : A) (rs : USize) (v : A) (vs n : USize)
    (hv : LoopBound v vs n) (hr : LoopBound arr rs n) (j : USize) (c : L) :
    LA.size (foldUInPlace n (addVStep v vs n hv) arr rs hr j c).1 = LA.size arr ∧
      (∀ i, (i < rs.toNat + j.toNat ∨ rs.toNat + n.toNat ≤ i) →
        LA.get (foldUInPlace n (addVStep v vs n hv) arr rs hr j c).1 i = LA.get arr i) ∧
      LimbArray.valAt (foldUInPlace n (addVStep v vs n hv) arr rs hr j c).1
          (rs.toNat + j.toNat) (n.toNat - j.toNat) +
          2 ^ (LA.w * (n.toNat - j.toNat)) *
            LA.val (foldUInPlace n (addVStep v vs n hv) arr rs hr j c).2 =
        LimbArray.valAt arr (rs.toNat + j.toNat) (n.toNat - j.toNat) +
          LimbArray.valAt v (vs.toNat + j.toNat) (n.toNat - j.toNat) + LA.val c := by
  induction arr, hr, j, c using foldUInPlace.induct (R := R) n (addVStep v vs n hv) rs with
  | case1 arr hr j c h p ih =>
    rw [foldUInPlace]
    simp only [h, ↓reduceDIte]
    have hj := USize.lt_iff_toNat_lt.1 h
    have hj₁ := USize.toNat_add_one_of_lt h
    have hidx := hr.toNat_add h
    have hvi := hv.toNat_add h
    obtain ⟨ih₁, ih₂, ih₃⟩ := ih
    rw [hj₁] at ih₂ ih₃
    rw [R.size_uset] at ih₁
    have hv' : LA.get (foldUInPlace n (addVStep v vs n hv)
        (R.uset arr (rs + j) p.1 (hr.uset_bound h)) rs (hr.of_uset ..) (j + 1) p.2).1
          (rs.toNat + j.toNat) = p.1 := by
      rw [ih₂ _ (.inl (by lia)), R.get_uset]
      simp [hidx]
    have hr' : LimbArray.valAt (R.uset arr (rs + j) p.1 (hr.uset_bound h))
        (rs.toNat + (j.toNat + 1)) (n.toNat - (j.toNat + 1)) =
          LimbArray.valAt arr (rs.toNat + (j.toNat + 1)) (n.toNat - (j.toNat + 1)) :=
      valAt_uset_of _ _ _ _ _ _ (by rw [hidx]; lia)
    have hz : R.uget arr (rs + j) (hr.uset_bound h) = LA.get arr (rs.toNat + j.toNat) := by
      rw [R.uget_eq, hidx]
    have hy : R.uget v (vs + j) (hv.uset_bound h) = LA.get v (vs.toNat + j.toNat) := by
      rw [R.uget_eq, hvi]
    have hl := R.val_addC (R.uget arr (rs + j) (hr.uset_bound h))
      (R.uget v (vs + j) (hv.uset_bound h)) c
    rw [hz, hy] at hl
    refine ⟨ih₁, fun i hi => ?_, ?_⟩
    · rw [ih₂ i (by lia), R.get_uset]
      simp only [hidx]
      split <;> lia
    · rw [hr'] at ih₃
      obtain ⟨k, hk⟩ : ∃ k, n.toNat - j.toNat = k + 1 := ⟨n.toNat - j.toNat - 1, by lia⟩
      rw [show n.toNat - (j.toNat + 1) = k by lia, ← Nat.add_assoc] at ih₃
      rw [hk, LimbArray.valAt_succ, LimbArray.valAt_succ, LimbArray.valAt_succ, hv', Nat.mul_succ,
        Nat.pow_add]
      generalize foldUInPlace n (addVStep v vs n hv) (R.uset arr (rs + j) p.1 (hr.uset_bound h))
        rs (hr.of_uset ..) (j + 1) p.2 = q at *
      simp only [p, addVStep, hz, hy] at *
      generalize LimbArray.valAt q.1 _ _ = V at *
      generalize LimbArray.valAt arr (rs.toNat + j.toNat + 1) k = X at *
      generalize LimbArray.valAt v (vs.toNat + j.toNat + 1) k = Y at *
      generalize LA.val q.2 = c' at *
      generalize 2 ^ (LA.w * k) = P at *
      generalize 2 ^ LA.w = B at *
      grind
  | case2 arr hr j c h =>
    rw [foldUInPlace]
    have : n.toNat - j.toNat = 0 := by have := USize.lt_iff_toNat_lt (a := j) (b := n); lia
    simp [h, this]

/-! ## Adding back -/

variable [F : WordFolds A L]

/-- The window of `n + 1` limbs of `w` from limb `i`, within it, as a loop bound. -/
public abbrev WinB (w : A) (i n : USize) : Prop :=
  i.toNat + n.toNat + 1 ≤ LA.size w ∧ i.toNat + n.toNat + 1 < USize.size

omit R in
public theorem WinB.top {w : A} {i n : USize} (h : WinB w i n) :
    (i + n).toNat = i.toNat + n.toNat :=
  USize.toNat_add_of_lt (by lia)

omit R in
public theorem WinB.of_size {w w' : A} {i n : USize} (h : WinB w i n)
    (e : LA.size w' = LA.size w) : WinB w' i n := by
  simp only [WinB, e]; exact h

/--
Adds `v` back to the window of `n + 1` limbs of `w` from limb `i`, decreasing `q`, while the borrow
`b` out of the window is not zero.
-/
@[expose, specialize]
public def addBack (w v : A) (vs n : USize) (hv : LoopBound v vs n) (i : USize) (hw : WinB w i n)
    (q b : L) : A × L :=
  if _h : ¬R.isZero b = true ∧ ¬R.isZero q = true then
    F.foldThen n (addVStep v vs n hv) w i ⟨by lia, by lia⟩ 0 R.zero fun w' hw' c =>
      have hi : (i + n).toNat < LA.size w' := by rw [hw', WinB.top hw]; lia
      let top := R.uget w' (i + n) hi
      addBack (R.uset w' (i + n) (R.add top c) hi) v vs n hv i
        (WinB.of_size (WinB.of_size hw hw') (R.size_uset ..)) (R.sub q R.one)
        (R.sub b (R.addh R.zero top c))
  else (w, q)
termination_by LA.val q
decreasing_by
  have : LA.val q ≠ 0 := fun e => _h.2 ((R.isZero_iff q).2 e)
  rw [val_sub_one q (by lia)]
  lia

public theorem size_addBack (w v : A) (vs n : USize) (hv : LoopBound v vs n) (i : USize)
    (hw : WinB w i n) (q b : L) : LA.size (addBack w v vs n hv i hw q b).1 = LA.size w := by
  induction w, hw, q, b using addBack.induct (R := R) n i with
  | case1 w hw q b h ih =>
    rw [addBack, dite_eq_left_of_eq_true (eq_true h), foldThen_eq']
    exact (ih _ (size_foldUInPlace ..) _).trans ((R.size_uset ..).trans (size_foldUInPlace ..))
  | case2 w hw q b h =>
    rw [addBack, dite_eq_right_of_eq_false (eq_false h)]

private theorem addBack_spec (w v : A) (vs n : USize) (hv : LoopBound v vs n) (i : USize)
    (hw : WinB w i n) (q b : L) (hv₀ : 0 < LimbArray.valAt v vs.toNat n.toNat) (W : Nat)
    (hW : W < 2 ^ (LA.w * (n.toNat + 1)))
    (hq : W / LimbArray.valAt v vs.toNat n.toNat ≤ LA.val q)
    (hS : LimbArray.valAt w i.toNat (n.toNat + 1) + LimbArray.valAt v vs.toNat n.toNat * LA.val q =
      W + 2 ^ (LA.w * (n.toNat + 1)) * LA.val b) :
    (∀ j, (j < i.toNat ∨ i.toNat + n.toNat + 1 ≤ j) →
        LA.get (addBack w v vs n hv i hw q b).1 j = LA.get w j) ∧
      LimbArray.valAt (addBack w v vs n hv i hw q b).1 i.toNat (n.toNat + 1) =
        W % LimbArray.valAt v vs.toNat n.toNat ∧
      LA.val (addBack w v vs n hv i hw q b).2 = W / LimbArray.valAt v vs.toNat n.toNat := by
  generalize hV : LimbArray.valAt v vs.toNat n.toNat = V at hv₀ hq hS ⊢
  induction w, hw, q, b using addBack.induct (R := R) n i with
  | case1 w hw q b h ih =>
    generalize hG : addBack w v vs n hv i hw q b = G
    rw [addBack, dite_eq_left_of_eq_true (eq_true h)] at hG
    obtain ⟨a, f₁, c, e, hG⟩ := foldThen_cases hG
    have hlb : LoopBound w i n := ⟨by lia, by lia⟩
    obtain ⟨-, f₂, f₃⟩ := addVFold_spec w i v vs n hv hlb 0 R.zero
    rw [e] at f₂ f₃
    simp only [USize.toNat_zero, Nat.add_zero, Nat.sub_zero, R.val_zero, hV] at f₂ f₃
    have IH := ih a f₁ c
    dsimp only at IH hG
    rw [hG] at IH
    have htop := WinB.top hw
    have hti : (i + n).toNat < LA.size a := by rw [f₁, htop]; lia
    -- The top limb with the carry, and the carry out of the window.
    have hpt : LA.get a (i.toNat + n.toNat) = LA.get w (i.toNat + n.toNat) :=
      f₂ _ (.inr (Nat.le_refl _))
    have hug : R.uget a (i + n) hti = LA.get w (i.toNat + n.toNat) := by
      rw [R.uget_eq, htop, hpt]
    have hc := incr_step (A := A) (LA.get w (i.toNat + n.toNat)) c
    have hP : 2 ^ (LA.w * (n.toNat + 1)) = 2 ^ (LA.w * n.toNat) * 2 ^ LA.w := by
      rw [Nat.mul_succ, Nat.pow_add]
    have hnew : LimbArray.valAt (R.uset a (i + n) (R.add (R.uget a (i + n) hti) c) hti)
        i.toNat (n.toNat + 1) + 2 ^ (LA.w * (n.toNat + 1)) *
          LA.val (R.addh R.zero (R.uget a (i + n) hti) c) =
        LimbArray.valAt w i.toNat (n.toNat + 1) + V := by
      rw [LimbArray.valAt_add, LimbArray.valAt_one, R.get_uset, valAt_uset_of _ _ _ _ _ _
        (by rw [htop]; lia)]
      simp only [htop, ↓reduceIte, hug]
      rw [LimbArray.valAt_add w i.toNat n.toNat 1, LimbArray.valAt_one, hP]
      generalize LA.val (R.add (LA.get w (i.toNat + n.toNat)) c) = s at *
      generalize LA.val (R.addh R.zero (LA.get w (i.toNat + n.toNat)) c) = c' at *
      generalize LA.val c = c₀ at *
      generalize LA.val (LA.get w (i.toNat + n.toNat)) = t at *
      generalize LimbArray.valAt a i.toNat n.toNat = L at *
      generalize LimbArray.valAt w i.toNat n.toNat = L₀ at *
      generalize 2 ^ (LA.w * n.toNat) = Bn at *
      generalize 2 ^ LA.w = B at *
      grind
    have hun : ∀ j, (j < i.toNat ∨ i.toNat + n.toNat + 1 ≤ j) →
        LA.get (R.uset a (i + n) (R.add (R.uget a (i + n) hti) c) hti) j = LA.get w j := by
      intro j hj
      rw [R.get_uset, ite_eq_right_iff.2 (fun e => by rw [htop] at e; lia), f₂ j (by lia)]
    have hS' := LimbArray.valAt_lt w i.toNat (n.toNat + 1)
    have hS'' := LimbArray.valAt_lt (R.uset a (i + n) (R.add (R.uget a (i + n) hti) c) hti)
      i.toNat (n.toNat + 1)
    have hq₀ : LA.val q ≠ 0 := fun e => h.2 ((R.isZero_iff q).2 e)
    have hb₀ : LA.val b ≠ 0 := fun e => h.1 ((R.isZero_iff b).2 e)
    have hq1 : LA.val (R.sub q R.one) = LA.val q - 1 := val_sub_one q (by lia)
    have hbl := LA.val_lt b
    have hccl := LA.val_lt (R.addh R.zero (R.uget a (i + n) hti) c)
    generalize R.addh R.zero (R.uget a (i + n) hti) c = cc at hnew hccl IH
    generalize R.uset a (i + n) (R.add (R.uget a (i + n) hti) c) hti = p' at hnew hun hS'' IH
    generalize 2 ^ (LA.w * (n.toNat + 1)) = P at *
    -- `v q > W` while the borrow is not zero, so `q` stays above the quotient.
    have hvq : W < V * LA.val q := by
      have := Nat.mul_le_mul_left P (show 1 ≤ LA.val b by lia)
      lia
    have hq' : W / V ≤ LA.val q - 1 := by
      have := (Nat.div_lt_iff_lt_mul hv₀).2 (by rw [Nat.mul_comm]; exact hvq)
      lia
    -- The carry is at most the borrow, since the window stays a natural number.
    have hcb : LA.val cc ≤ LA.val b := by
      refine Nat.le_of_not_lt fun hlt => ?_
      have := Nat.mul_le_mul_left P (show LA.val b + 1 ≤ LA.val cc from hlt)
      rw [Nat.mul_add, Nat.mul_one] at this
      have : V ≤ V * LA.val q := Nat.le_mul_of_pos_right _ (by lia)
      lia
    have hsub : LA.val (R.sub b cc) = LA.val b - LA.val cc := by
      rw [R.val_sub, show LA.val b + (2 ^ LA.w - LA.val cc) =
        (LA.val b - LA.val cc) + 2 ^ LA.w * 1 by lia, Nat.add_mul_mod_self_left,
        Nat.mod_eq_of_lt (by lia)]
    obtain ⟨i₂, i₃, i₄⟩ := IH (by rw [hq1]; exact hq') (by
      rw [hq1, hsub]
      have := Nat.mul_le_mul_left P hcb
      have e₁ : V * (LA.val q - 1) = V * LA.val q - V := by rw [Nat.mul_sub, Nat.mul_one]
      have e₂ : P * (LA.val b - LA.val cc) = P * LA.val b - P * LA.val cc := Nat.mul_sub ..
      have := Nat.le_mul_of_pos_right V (show 0 < LA.val q by lia)
      rw [e₁, e₂]
      generalize V * LA.val q = VQ at *
      generalize P * LA.val b = PB at *
      generalize P * LA.val cc = PC at *
      lia)
    exact ⟨fun j hj => (i₂ j hj).trans (hun j hj), i₃, i₄⟩
  | case2 w hw q b h =>
    rw [addBack, dite_eq_right_of_eq_false (eq_false h)]
    have hS' := LimbArray.valAt_lt w i.toNat (n.toNat + 1)
    generalize 2 ^ (LA.w * (n.toNat + 1)) = P at *
    have hb : LA.val b = 0 := by
      by_cases hb : R.isZero b = true
      · exact (R.isZero_iff b).1 hb
      · have hq0 : R.isZero q = true := Classical.byContradiction fun hq0 => h ⟨hb, hq0⟩
        rw [(R.isZero_iff q).1 hq0, Nat.mul_zero, Nat.add_zero] at hS
        rcases Nat.eq_zero_or_pos (LA.val b) with h0 | h0
        · exact h0
        · have := Nat.mul_le_mul_left P (show 1 ≤ LA.val b from h0); lia
    rw [hb, Nat.mul_zero, Nat.add_zero] at hS
    have hle : LA.val q ≤ W / V := (Nat.le_div_iff_mul_le hv₀).2 (by rw [Nat.mul_comm]; lia)
    have hqe : LA.val q = W / V := Nat.le_antisymm hle hq
    refine ⟨fun _ _ => rfl, ?_, hqe⟩
    have := Nat.div_add_mod W V
    rw [← hqe] at this
    lia

/-! ## One step -/

/-- The top limbs bound the quotient: `Q V ≤ W` gives `Q V₂ ≤ W₃` for the top parts above `P`. -/
private theorem est_bound {Q V W Vlo Wlo V₂ W₃ P : Nat} (hV : V = Vlo + P * V₂)
    (hW : W = Wlo + P * W₃) (hWlo : Wlo < P) (hQ : Q * V ≤ W) : Q * V₂ ≤ W₃ := by
  have h₁ : P * (Q * V₂) ≤ Q * V := by
    rw [hV, Nat.mul_add, Nat.mul_left_comm]; exact Nat.le_add_left _ _
  have h₂ : P * (Q * V₂) < P * (W₃ + 1) := by rw [Nat.mul_add, Nat.mul_one]; lia
  have := Nat.lt_of_mul_lt_mul_left h₂
  lia

omit R F in
/-- Three limbs from `lo`. -/
private theorem valAt_three (a : A) (lo : Nat) :
    LimbArray.valAt a lo 3 = (LA.val (LA.get a (lo + 2)) * 2 ^ LA.w + LA.val (LA.get a (lo + 1))) *
      2 ^ LA.w + LA.val (LA.get a lo) := by
  simp only [LimbArray.valAt_succ, LimbArray.valAt_zero, Nat.mul_zero, Nat.add_zero, Nat.add_assoc]
  grind

omit R F in
/-- Two limbs from `lo`. -/
private theorem valAt_two (a : A) (lo : Nat) :
    LimbArray.valAt a lo 2 = LA.val (LA.get a (lo + 1)) * 2 ^ LA.w + LA.val (LA.get a lo) := by
  simp only [LimbArray.valAt_succ, LimbArray.valAt_zero, Nat.mul_zero, Nat.add_zero]
  grind

private theorem ite_pos {α : Type} {c : Prop} [Decidable c] (h : c) {a b : α} :
    (if c then a else b) = a := by
  simp [h]

private theorem toNat_two : (2 : USize).toNat = 2 := by
  rw [USize.toNat_ofNat, Nat.mod_eq_of_lt (by cases USize.size_eq <;> simp_all [USize.size])]

/-- The indices of the top three limbs of a window of `n + 1 ≥ 3` limbs. -/
public theorem top3 {i n : USize} (hn : 2 ≤ n.toNat) (hU : i.toNat + n.toNat < USize.size) :
    (i + n).toNat = i.toNat + n.toNat ∧ (i + (n - 1)).toNat = i.toNat + n.toNat - 1 ∧
      (i + (n - 2)).toNat = i.toNat + n.toNat - 2 := by
  have h₁ : (n - 1).toNat = n.toNat - 1 :=
    by rw [USize.toNat_sub_of_le _ _ (USize.le_iff_toNat_le.2 (by rw [USize.toNat_one]; lia)),
      USize.toNat_one]
  have h₂ : (n - 2).toNat = n.toNat - 2 :=
    by rw [USize.toNat_sub_of_le _ _ (USize.le_iff_toNat_le.2 (by rw [toNat_two]; lia)), toNat_two]
  refine ⟨USize.toNat_add_of_lt hU, ?_, ?_⟩
  · rw [USize.toNat_add_of_lt (by rw [h₁]; lia), h₁]; lia
  · rw [USize.toNat_add_of_lt (by rw [h₂]; lia), h₂]; lia

/--
One step of the division, without allocating: subtracts `q v`, for the estimate `q`, from limbs
`i` to `i + n - 1` of `w` by the in-place fold, and when the borrow out equals the top limb
`i + n` of the window, which is then the common case of an exact estimate, writes `q` there.
Otherwise the window went negative and `addBack` corrects it. Afterwards limbs `i` to `i + n - 1`
hold the remainder of the window by `v` and limb `i + n` the quotient limb.
-/
@[expose, specialize]
public def divStepIn (w v : A) (vs n : USize) (hv : LoopBound v vs n) (v₁ v₂ dv : L) (i : USize) :
    A :=
  if h : WinB w i n ∧ 2 ≤ n.toNat then
    have ht := top3 h.2 (by lia)
    let q := qEstD A dv (R.uget w (i + n) (by rw [ht.1]; lia))
      (R.uget w (i + (n - 1)) (by rw [ht.2.1]; lia)) (R.uget w (i + (n - 2)) (by rw [ht.2.2]; lia))
      v₁ v₂
    F.foldThen n (subMulStep v vs n hv q) w i ⟨by lia, by lia⟩ 0 R.zero fun w' hw' b =>
      have hti : (i + n).toNat < LA.size w' := by rw [hw', ht.1]; lia
      let top := R.uget w' (i + n) hti
      if R.eqB b top then R.uset w' (i + n) q hti
      else
        let p := addBack (R.uset w' (i + n) (R.sub top b) hti) v vs n hv i
          (WinB.of_size (WinB.of_size h.1 hw') (R.size_uset ..)) q R.one
        R.uset p.1 (i + n) p.2 (by rw [size_addBack, R.size_uset]; exact hti)
  else w

set_option maxHeartbeats 1000000 in
private theorem divStepIn_spec (w v : A) (vs n : USize) (hv : LoopBound v vs n) (v₁ v₂ dv : L)
    (i : USize) (hn₂ : 2 ≤ n.toNat) (hk : WinB w i n)
    (hv₀ : 0 < LimbArray.valAt v vs.toNat n.toNat)
    (hv₁ : v₁ = LA.get v (vs.toNat + n.toNat - 1)) (hv₂ : v₂ = LA.get v (vs.toNat + n.toNat - 2))
    (hW : LimbArray.valAt w i.toNat (n.toNat + 1) <
      LimbArray.valAt v vs.toNat n.toNat * 2 ^ LA.w) :
    LA.size (divStepIn w v vs n hv v₁ v₂ dv i) = LA.size w ∧
      (∀ j, (j < i.toNat ∨ i.toNat + n.toNat + 1 ≤ j) →
        LA.get (divStepIn w v vs n hv v₁ v₂ dv i) j = LA.get w j) ∧
      LimbArray.valAt (divStepIn w v vs n hv v₁ v₂ dv i) i.toNat n.toNat =
        LimbArray.valAt w i.toNat (n.toNat + 1) % LimbArray.valAt v vs.toNat n.toNat ∧
      LA.val (LA.get (divStepIn w v vs n hv v₁ v₂ dv i) (i.toNat + n.toNat)) =
        LimbArray.valAt w i.toNat (n.toNat + 1) / LimbArray.valAt v vs.toNat n.toNat := by
  have ht := top3 hn₂ (show i.toNat + n.toNat < USize.size by lia)
  generalize hG : divStepIn w v vs n hv v₁ v₂ dv i = G
  rw [divStepIn, dite_eq_left_of_eq_true (eq_true ⟨hk, hn₂⟩)] at hG
  dsimp only at hG
  obtain ⟨q, hq, hG⟩ : ∃ q, q = qEstD A dv (R.uget w (i + n) (by rw [ht.1]; lia))
      (R.uget w (i + (n - 1)) (by rw [ht.2.1]; lia)) (R.uget w (i + (n - 2)) (by rw [ht.2.2]; lia))
      v₁ v₂ ∧ F.foldThen n (subMulStep v vs n hv q) w i ⟨by lia, by lia⟩ 0 R.zero
        (fun w' hw' b =>
          if R.eqB b (R.uget w' (i + n) (by rw [hw', ht.1]; lia)) then
            R.uset w' (i + n) q (by rw [hw', ht.1]; lia)
          else
            R.uset (addBack (R.uset w' (i + n) (R.sub (R.uget w' (i + n) (by rw [hw', ht.1]; lia)) b)
              (by rw [hw', ht.1]; lia)) v vs n hv i
              (WinB.of_size (WinB.of_size hk hw') (R.size_uset ..)) q R.one).1 (i + n)
              (addBack (R.uset w' (i + n) (R.sub (R.uget w' (i + n) (by rw [hw', ht.1]; lia)) b)
              (by rw [hw', ht.1]; lia)) v vs n hv i
              (WinB.of_size (WinB.of_size hk hw') (R.size_uset ..)) q R.one).2
              (by rw [size_addBack, R.size_uset, hw', ht.1]; lia)) = G := ⟨_, rfl, hG⟩
  rw [R.uget_eq, R.uget_eq, R.uget_eq, ht.1, ht.2.1, ht.2.2] at hq
  generalize hV : LimbArray.valAt v vs.toNat n.toNat = V at hv₀ hW ⊢
  generalize hWv : LimbArray.valAt w i.toNat (n.toNat + 1) = W at hW ⊢
  have hvlt : V < 2 ^ (LA.w * n.toNat) := hV ▸ LimbArray.valAt_lt ..
  -- The estimate is never too small.
  have hQβ : W / V < 2 ^ LA.w := (Nat.div_lt_iff_lt_mul hv₀).2 (by rw [Nat.mul_comm]; exact hW)
  have hvn : V = LimbArray.valAt v vs.toNat (n.toNat - 2) +
      2 ^ (LA.w * (n.toNat - 2)) * (LA.val v₁ * 2 ^ LA.w + LA.val v₂) := by
    rw [← hV, show n.toNat = n.toNat - 2 + 2 by lia, LimbArray.valAt_add, valAt_two,
      show vs.toNat + (n.toNat - 2) + 1 = vs.toNat + (n.toNat - 2 + 2) - 1 by lia,
      show vs.toNat + (n.toNat - 2) = vs.toNat + (n.toNat - 2 + 2) - 2 by lia,
      ← show n.toNat = n.toNat - 2 + 2 by lia, ← hv₁, ← hv₂]
  have hwn : W = LimbArray.valAt w i.toNat (n.toNat - 2) + 2 ^ (LA.w * (n.toNat - 2)) *
      ((LA.val (LA.get w (i.toNat + n.toNat)) * 2 ^ LA.w +
        LA.val (LA.get w (i.toNat + n.toNat - 1))) * 2 ^ LA.w +
          LA.val (LA.get w (i.toNat + n.toNat - 2))) := by
    rw [← hWv, show n.toNat + 1 = n.toNat - 2 + 3 by lia, LimbArray.valAt_add, valAt_three,
      show i.toNat + (n.toNat - 2) + 2 = i.toNat + n.toNat by lia,
      show i.toNat + (n.toNat - 2) + 1 = i.toNat + n.toNat - 1 by lia,
      show i.toNat + (n.toNat - 2) = i.toNat + n.toNat - 2 by lia]
  have hge := qEstD_ge dv (LA.get w (i.toNat + n.toNat)) (LA.get w (i.toNat + n.toNat - 1))
    (LA.get w (i.toNat + n.toNat - 2)) v₁ v₂ (W / V) hQβ
    (est_bound hvn hwn (LimbArray.valAt_lt ..) (Nat.div_mul_le_self W V))
  rw [← hq] at hge
  -- The product subtracted from the low `n` limbs of the window.
  have hr : LoopBound w i n := ⟨by lia, by lia⟩
  obtain ⟨a, f₁, b, e, hG⟩ := foldThen_cases hG
  obtain ⟨-, f₂, f₃⟩ := subMulFold_spec w i v vs n hv hr q 0 R.zero
  rw [e] at f₂ f₃
  simp only [USize.toNat_zero, Nat.add_zero, Nat.sub_zero, R.val_zero, hV] at f₂ f₃
  have htop : LA.get a (i.toNat + n.toNat) = LA.get w (i.toNat + n.toNat) :=
    f₂ _ (.inr (Nat.le_refl _))
  have hWs : W = LimbArray.valAt w i.toNat n.toNat +
      2 ^ (LA.w * n.toNat) * LA.val (LA.get w (i.toNat + n.toNat)) := by
    rw [← hWv, LimbArray.valAt_add, LimbArray.valAt_one]
  have hlow := LimbArray.valAt_lt a i.toNat n.toNat
  -- `q ≥ W / v` bounds the remainder: `W - q v < v` when it is not negative.
  have hdm := Nat.div_add_mod W V
  have hmod := Nat.mod_lt W hv₀
  have hqv : V * (W / V) ≤ V * LA.val q := Nat.mul_le_mul_left _ hge
  have hti : (i + n).toNat < LA.size a := by rw [f₁, ht.1]; lia
  have hug : R.uget a (i + n) hti = LA.get w (i.toNat + n.toNat) := by rw [R.uget_eq, ht.1, htop]
  have hB4 := four_le (R := R)
  split at hG
  · rename_i hb
    subst hG
    -- The estimate was exact: the window is `W - q v`, which is the remainder.
    rw [R.eqB_iff, hug] at hb
    rw [hb] at f₃
    have hle : LA.val q * V ≤ W := by rw [hWs]; lia
    have hq' : LA.val q = W / V := Nat.le_antisymm ((Nat.le_div_iff_mul_le hv₀).2 hle) hge
    refine ⟨by rw [R.size_uset, f₁], fun j hj => ?_, ?_, ?_⟩
    · rw [R.get_uset, ite_eq_right_iff.2 (fun e => by rw [ht.1] at e; lia), f₂ j (by lia)]
    · rw [LimbArray.valAt_congr (b := a) _ fun j _ hj => by
        rw [R.get_uset, ite_eq_right_iff.2 (fun e => by rw [ht.1] at e; lia)]]
      rw [hq'] at f₃
      lia
    · rw [R.get_uset, ite_pos (by rw [ht.1]), hq']
  · rename_i hb
    subst hG
    rw [R.eqB_iff, hug] at hb
    -- The window went negative: the borrow exceeds the top limb.
    have hbt : LA.val (LA.get w (i.toNat + n.toNat)) < LA.val b := by
      rcases Nat.lt_or_ge (LA.val (LA.get w (i.toNat + n.toNat))) (LA.val b) with h | h
      · exact h
      · exfalso
        rcases Nat.lt_or_ge (LA.val b) (LA.val (LA.get w (i.toNat + n.toNat))) with h' | h'
        · have := Nat.mul_le_mul_left (2 ^ (LA.w * n.toNat))
            (show LA.val b + 1 ≤ LA.val (LA.get w (i.toNat + n.toNat)) from h')
          rw [Nat.mul_add, Nat.mul_one] at this
          lia
        · exact hb (by lia)
    have hsub : LA.val (R.sub (LA.get w (i.toNat + n.toNat)) b) =
        LA.val (LA.get w (i.toNat + n.toNat)) + 2 ^ LA.w - LA.val b := by
      have := LA.val_lt b
      rw [R.val_sub, Nat.mod_eq_of_lt (by lia)]
      lia
    have hS : LimbArray.valAt (R.uset a (i + n) (R.sub (R.uget a (i + n) hti) b) hti) i.toNat
        (n.toNat + 1) + V * LA.val q = W + 2 ^ (LA.w * (n.toNat + 1)) * LA.val R.one := by
      rw [LimbArray.valAt_add, LimbArray.valAt_one, R.get_uset, ite_pos (by rw [ht.1]), hug, hsub,
        valAt_uset_of _ _ _ _ _ _ (by rw [ht.1]; lia), hWs, R.val_one,
        show LA.w * (n.toNat + 1) = LA.w * n.toNat + LA.w by rw [Nat.mul_succ], Nat.pow_add]
      have := Nat.mul_le_mul_left (2 ^ (LA.w * n.toNat)) (Nat.le_of_lt hbt)
      rw [Nat.mul_sub, Nat.mul_add]
      have := LA.val_lt b
      have := Nat.mul_le_mul_left (2 ^ (LA.w * n.toNat)) (Nat.le_of_lt this)
      generalize 2 ^ (LA.w * n.toNat) * LA.val b = Pb at *
      generalize 2 ^ (LA.w * n.toNat) * 2 ^ LA.w = PB at *
      generalize 2 ^ (LA.w * n.toNat) * LA.val (LA.get w (i.toNat + n.toNat)) = Pt at *
      lia
    have hk' : WinB (R.uset a (i + n) (R.sub (R.uget a (i + n) hti) b) hti) i n :=
      WinB.of_size (WinB.of_size hk f₁) (R.size_uset ..)
    obtain ⟨a₂, a₃, a₄⟩ := addBack_spec (R.uset a (i + n) (R.sub (R.uget a (i + n) hti) b) hti)
      v vs n hv i hk' q R.one (by rw [hV]; exact hv₀) W
      (by rw [← hWv]; exact LimbArray.valAt_lt ..) (by rw [hV]; exact hge) (by rw [hV]; exact hS)
    rw [hV] at a₃ a₄
    refine ⟨by rw [R.size_uset, size_addBack, R.size_uset, f₁], fun j hj => ?_, ?_, ?_⟩
    · rw [R.get_uset, ite_eq_right_iff.2 (fun e => by rw [ht.1] at e; lia), a₂ j hj, R.get_uset,
        ite_eq_right_iff.2 (fun e => by rw [ht.1] at e; lia), f₂ j (by lia)]
    · rw [valAt_uset_of _ _ _ _ _ _ (by rw [ht.1]; lia),
        LimbArray.valAt_mod _ _ (Nat.le_add_right n.toNat 1), a₃]
      exact Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le hmod (by
        rw [← hV]; exact Nat.le_of_lt (LimbArray.valAt_lt ..)))
    · rw [R.get_uset, ite_pos (by rw [ht.1]), a₄]

private theorem toNat_pred {i : USize} (hi : i ≠ 0) : (i - 1).toNat = i.toNat - 1 := by
  have : i.toNat ≠ 0 := fun e => hi (USize.toNat_inj.1 (by rw [e]; rfl))
  rw [USize.toNat_sub_of_le _ _ (USize.le_iff_toNat_le.2 (by rw [USize.toNat_one]; lia)),
    USize.toNat_one]

/--
Divides limbs `0` to `i + n - 1` of `w` by `v` of `n` limbs, with the top limbs `v₁` and `v₂`,
from window `i - 1` down to window `0`, in place: the quotient limb of window `j` goes to limb
`j + n`, so that the quotient ends in limbs `n` to `n + i - 1` and the remainder in limbs `0` to
`n - 1`.
-/
@[expose, specialize]
public def divLoopIn (w v : A) (vs n : USize) (hv : LoopBound v vs n) (v₁ v₂ dv : L) (i : USize) :
    A :=
  if hi : i = 0 then w
  else divLoopIn (divStepIn w v vs n hv v₁ v₂ dv (i - 1)) v vs n hv v₁ v₂ dv (i - 1)
termination_by i.toNat
decreasing_by
  have := toNat_pred hi
  have : i.toNat ≠ 0 := fun e => hi (USize.toNat_inj.1 (by rw [e]; rfl))
  lia

public theorem divLoopIn_spec (w v : A) (vs n : USize) (hv : LoopBound v vs n) (v₁ v₂ dv : L)
    (i : USize) (hn₂ : 2 ≤ n.toNat) (hk : i.toNat + n.toNat ≤ LA.size w)
    (hU : LA.size w < USize.size) (hv₀ : 0 < LimbArray.valAt v vs.toNat n.toNat)
    (hv₁ : v₁ = LA.get v (vs.toNat + n.toNat - 1)) (hv₂ : v₂ = LA.get v (vs.toNat + n.toNat - 2))
    (hR : LimbArray.valAt w 0 (i.toNat + n.toNat) <
      LimbArray.valAt v vs.toNat n.toNat * 2 ^ (LA.w * i.toNat)) :
    LA.size (divLoopIn w v vs n hv v₁ v₂ dv i) = LA.size w ∧
      (∀ j, i.toNat + n.toNat ≤ j → LA.get (divLoopIn w v vs n hv v₁ v₂ dv i) j = LA.get w j) ∧
      LimbArray.valAt v vs.toNat n.toNat *
          LimbArray.valAt (divLoopIn w v vs n hv v₁ v₂ dv i) n.toNat i.toNat +
          LimbArray.valAt (divLoopIn w v vs n hv v₁ v₂ dv i) 0 n.toNat =
        LimbArray.valAt w 0 (i.toNat + n.toNat) ∧
      LimbArray.valAt (divLoopIn w v vs n hv v₁ v₂ dv i) 0 n.toNat <
        LimbArray.valAt v vs.toNat n.toNat := by
  generalize hV : LimbArray.valAt v vs.toNat n.toNat = V at hv₀ hR ⊢
  induction w, i using divLoopIn.induct (R := R) (F := F) v vs n hv v₁ v₂ dv with
  | case1 w =>
    refine ⟨by rw [divLoopIn, dite_eq_left_of_eq_true (eq_true rfl)],
      fun _ _ => by rw [divLoopIn, dite_eq_left_of_eq_true (eq_true rfl)], ?_, ?_⟩
    · rw [divLoopIn, dite_eq_left_of_eq_true (eq_true rfl)]; simp
    · rw [divLoopIn, dite_eq_left_of_eq_true (eq_true rfl)]; simpa using hR
  | case2 w i hi ih =>
    rw [divLoopIn, dite_eq_right hi]
    have hp := toNat_pred hi
    have hi₀ : i.toNat ≠ 0 := fun e => hi (USize.toNat_inj.1 (by rw [e]; rfl))
    -- The window `i - 1` of `R`, and the limbs below it.
    have hsplit : LimbArray.valAt w 0 (i.toNat + n.toNat) = LimbArray.valAt w 0 (i.toNat - 1) +
        2 ^ (LA.w * (i.toNat - 1)) * LimbArray.valAt w (i.toNat - 1) (n.toNat + 1) := by
      rw [show i.toNat + n.toNat = (i.toNat - 1) + (n.toNat + 1) by lia, LimbArray.valAt_add,
        Nat.zero_add]
    have hlo := LimbArray.valAt_lt w 0 (i.toNat - 1)
    have hWlt : LimbArray.valAt w (i.toNat - 1) (n.toNat + 1) < V * 2 ^ LA.w := by
      have e : 2 ^ (LA.w * i.toNat) = 2 ^ (LA.w * (i.toNat - 1)) * 2 ^ LA.w := by
        rw [← Nat.pow_add, ← Nat.mul_succ, Nat.succ_eq_add_one, Nat.sub_add_cancel (by lia)]
      rw [hsplit, e] at hR
      refine Nat.lt_of_mul_lt_mul_left (a := 2 ^ (LA.w * (i.toNat - 1))) ?_
      rw [Nat.mul_left_comm]
      have : V * (2 ^ (LA.w * (i.toNat - 1)) * 2 ^ LA.w) =
          2 ^ (LA.w * (i.toNat - 1)) * (V * 2 ^ LA.w) := by rw [Nat.mul_left_comm]
      lia
    obtain ⟨s₁, s₂, s₃, s₄⟩ := divStepIn_spec w v vs n hv v₁ v₂ dv (i - 1) hn₂
      ⟨by rw [hp]; lia, by rw [hp]; lia⟩ (by rw [hV]; exact hv₀) hv₁ hv₂
      (by rw [hp, hV]; exact hWlt)
    rw [hp] at s₂
    rw [hp, hV] at s₃ s₄
    have hlo' : LimbArray.valAt (divStepIn w v vs n hv v₁ v₂ dv (i - 1)) 0 (i.toNat - 1) =
        LimbArray.valAt w 0 (i.toNat - 1) :=
      LimbArray.valAt_congr _ fun j _ hj => s₂ j (.inl (by lia))
    have hR' : LimbArray.valAt (divStepIn w v vs n hv v₁ v₂ dv (i - 1)) 0
        ((i - 1).toNat + n.toNat) = LimbArray.valAt w 0 (i.toNat - 1) +
          2 ^ (LA.w * (i.toNat - 1)) * (LimbArray.valAt w (i.toNat - 1) (n.toNat + 1) % V) := by
      rw [hp, LimbArray.valAt_add, Nat.zero_add, hlo', s₃]
    obtain ⟨i₁, i₂, i₃, i₄⟩ := ih (by rw [s₁, hp]; lia) (by rw [s₁]; exact hU) (by
      rw [hR']
      have hm := Nat.mod_lt (LimbArray.valAt w (i.toNat - 1) (n.toNat + 1)) hv₀
      rw [hp]
      generalize LimbArray.valAt w (i.toNat - 1) (n.toNat + 1) % V = r at *
      generalize 2 ^ (LA.w * (i.toNat - 1)) = P at *
      have := Nat.mul_le_mul_left P (show r + 1 ≤ V from hm)
      rw [Nat.mul_add, Nat.mul_one] at this
      rw [Nat.mul_comm V P]
      lia)
    clear ih
    rw [hp] at i₂ i₃ hR'
    have hqtop : LA.val (LA.get (divLoopIn (divStepIn w v vs n hv v₁ v₂ dv (i - 1)) v vs n hv v₁ v₂
        dv (i - 1)) (n.toNat + (i.toNat - 1))) =
          LimbArray.valAt w (i.toNat - 1) (n.toNat + 1) / V := by
      rw [i₂ _ (by lia), Nat.add_comm, s₄]
    refine ⟨i₁.trans s₁, fun j hj => ?_, ?_, i₄⟩
    · rw [i₂ j (by lia), s₂ j (.inr (by lia))]
    · have e₁ := LimbArray.valAt_add (divLoopIn (divStepIn w v vs n hv v₁ v₂ dv (i - 1)) v vs n hv
        v₁ v₂ dv (i - 1)) n.toNat (i.toNat - 1) 1
      rw [Nat.sub_add_cancel (show 1 ≤ i.toNat by lia), LimbArray.valAt_one, hqtop] at e₁
      rw [e₁, hsplit]
      rw [hR'] at i₃
      have := Nat.div_add_mod (LimbArray.valAt w (i.toNat - 1) (n.toNat + 1)) V
      generalize LimbArray.valAt (divLoopIn (divStepIn w v vs n hv v₁ v₂ dv (i - 1)) v vs n hv v₁
        v₂ dv (i - 1)) n.toNat (i.toNat - 1) = Q at *
      generalize LimbArray.valAt (divLoopIn (divStepIn w v vs n hv v₁ v₂ dv (i - 1)) v vs n hv v₁
        v₂ dv (i - 1)) 0 n.toNat = Rn at *
      generalize LimbArray.valAt w (i.toNat - 1) (n.toNat + 1) / V = q at *
      generalize LimbArray.valAt w (i.toNat - 1) (n.toNat + 1) % V = r at *
      generalize LimbArray.valAt w (i.toNat - 1) (n.toNat + 1) = W at *
      generalize 2 ^ (LA.w * (i.toNat - 1)) = P at *
      subst this
      grind

end MPN.Schoolbook
