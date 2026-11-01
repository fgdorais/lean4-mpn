/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import MPN.WordArray
public import MPN.Generic.Sqrt

/-!
# The square root of a double limb

`sqrt2W hi lo` is `⌊√N⌋` for `N = hi β + lo`, by Newton's iteration on limbs, the base case of
Zimmermann's recursion like GMP's `mpn_sqrtrem2`. The iteration starts from `2ᵉ` with
`e = ⌊log₂ N / 2⌋ + 1`, just above the root, so that it converges quadratically from the first
step; each step is the average of `x` and `N / x` by one `div2`.
-/

namespace MPN.WordArray

variable {A L : Type} [LA : LimbArray A L] [R : WordArray A L]

/-- `x / 2`, by a shift. -/
private theorem val_shr_one (x : L) : LA.val (R.shr x R.one) = LA.val x / 2 := by
  have := R.w_ge
  rw [R.val_shr, R.val_one, Nat.mod_eq_of_lt (by lia), Nat.pow_one]

/-- `x % 2`, by a mask. -/
private theorem val_land_one (x : L) : LA.val (R.land x R.one) = LA.val x % 2 := by
  rw [R.val_land, R.val_one, Nat.and_one_is_mod]

variable (A) in
/-- The average `⌊(x + q) / 2⌋` of two limbs, without overflow. -/
@[inline, expose] public def avgW (x q : L) : L :=
  R.add (R.add (R.shr x R.one) (R.shr q R.one)) (R.mul (R.land x R.one) (R.land q R.one))

private theorem val_avgW (x q : L) : LA.val (avgW A x q) = (LA.val x + LA.val q) / 2 := by
  have hx := LA.val_lt x; have hq := LA.val_lt q
  have hB := four_le (R := R)
  have h₁ := Nat.mod_lt (LA.val x) (show 0 < 2 by decide)
  have h₂ := Nat.mod_lt (LA.val q) (show 0 < 2 by decide)
  have hm : (LA.val x % 2) * (LA.val q % 2) ≤ 1 := by
    have := Nat.mul_le_mul (Nat.le_of_lt_succ h₁) (Nat.le_of_lt_succ h₂); lia
  simp only [avgW, R.val_add, R.val_mul, val_shr_one, val_land_one]
  have hs : LA.val x / 2 + LA.val q / 2 + 1 < 2 ^ LA.w := by
    have : 2 ^ LA.w = 2 * (2 ^ LA.w / 2) := by
      rw [Nat.mul_div_cancel' (Nat.pow_dvd_pow 2 (show 1 ≤ LA.w by have := R.w_ge; lia))]
    lia
  rw [Nat.mod_eq_of_lt (show LA.val x / 2 + LA.val q / 2 < 2 ^ LA.w by lia),
    Nat.mod_eq_of_lt (show LA.val x % 2 * (LA.val q % 2) < 2 ^ LA.w by lia),
    Nat.mod_eq_of_lt (show LA.val x / 2 + LA.val q / 2 + LA.val x % 2 * (LA.val q % 2) < 2 ^ LA.w by
      lia)]
  rcases Nat.mod_two_eq_zero_or_one (LA.val x) with h | h <;>
    rcases Nat.mod_two_eq_zero_or_one (LA.val q) with h' | h' <;>
    simp only [h, h', Nat.mul_zero, Nat.mul_one] <;> lia

variable (A) in
/--
Newton's iteration for `⌊√N⌋`, `N = hi β + lo`, from `x ≥ ⌊√N⌋`, while it decreases: the next
step is the average of `x` and `N / x`. When `hi ≥ x`, `x` is already `⌊√N⌋`, since `⌊√N⌋ ≥ hi`.
-/
@[expose, specialize] public def sqrtIterW (hi lo x : L) : L :=
  if R.ltB hi x then
    let y := avgW A x (R.div2 hi lo x)
    if R.ltB y x then sqrtIterW hi lo y else x
  else x
termination_by LA.val x
decreasing_by exact (R.ltB_iff ..).1 (by assumption)

private theorem sqrtIterW_eq (hi lo x : L)
    (hx : _root_.Nat.sqrt (LA.val hi * 2 ^ LA.w + LA.val lo) ≤ LA.val x) :
    LA.val (sqrtIterW A hi lo x) = _root_.Nat.sqrt (LA.val hi * 2 ^ LA.w + LA.val lo) := by
  induction x using sqrtIterW.induct A (R := R) hi lo with
  | case1 x h y hy ih =>
    rw [sqrtIterW, ite_eq_left h]
    simp only [y] at hy ⊢
    rw [ite_eq_left hy]
    apply ih
    have h' := (R.ltB_iff ..).1 h
    rw [val_avgW, R.val_div2 _ _ _ h']
    exact le_newton (by lia) (Nat.sqrt_le _)
  | case2 x h y hy =>
    rw [sqrtIterW, ite_eq_left h]
    simp only [y] at hy ⊢
    rw [ite_eq_right hy]
    have h' := (R.ltB_iff ..).1 h
    have hy' : ¬(LA.val x + (LA.val hi * 2 ^ LA.w + LA.val lo) / LA.val x) / 2 < LA.val x := by
      rw [← R.val_div2 _ _ _ h', ← val_avgW]; exact fun e => hy ((R.ltB_iff ..).2 e)
    -- `N / x ≥ x`, so `x² ≤ N`.
    have hxx : LA.val x * LA.val x ≤ LA.val hi * 2 ^ LA.w + LA.val lo :=
      (Nat.le_div_iff_mul_le (by lia)).1 (by lia)
    exact Nat.le_antisymm (le_sqrt_of hxx) hx
  | case3 x h =>
    rw [sqrtIterW, ite_eq_right h]
    -- `hi² ≤ N`, so `hi ≤ ⌊√N⌋ ≤ x ≤ hi`.
    have hle : LA.val hi ≤ _root_.Nat.sqrt (LA.val hi * 2 ^ LA.w + LA.val lo) :=
      le_sqrt_of (by
        have := Nat.mul_le_mul_left (LA.val hi) (Nat.le_of_lt (LA.val_lt hi))
        lia)
    have : LA.val x ≤ LA.val hi := Nat.le_of_not_lt fun e => h ((R.ltB_iff ..).2 e)
    lia

variable (A) in
/-- `⌊log₂ (hi β + lo)⌋`. -/
@[inline, expose] public def log2two (hi lo : L) : Nat :=
  if R.isZero hi then R.log2 lo else LA.w + R.log2 hi

private theorem log2two_eq (hi lo : L) :
    log2two A hi lo = (LA.val hi * 2 ^ LA.w + LA.val lo).log2 := by
  unfold log2two
  split
  · rename_i h
    rw [(R.isZero_iff _).1 h, Nat.zero_mul, Nat.zero_add, R.log2_eq]
  · rename_i h
    have h0 : LA.val hi ≠ 0 := fun e => h ((R.isZero_iff _).2 e)
    have hle : 2 ^ LA.w ≤ LA.val hi * 2 ^ LA.w + LA.val lo := by
      have := Nat.mul_le_mul_right (2 ^ LA.w) (Nat.one_le_iff_ne_zero.2 h0); lia
    rw [log2_div_add hle, R.log2_eq, Nat.add_comm LA.w]
    congr 2
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ (Nat.two_pow_pos _),
      Nat.div_eq_of_lt (LA.val_lt lo), Nat.zero_add]

variable (A) in
/-- `⌊√N⌋` of a double limb `N = hi β + lo`, from `2ᵉ` with `e = ⌊log₂ N / 2⌋ + 1`. -/
@[expose] public def sqrt2W (hi lo : L) : L :=
  let e := log2two A hi lo / 2 + 1
  sqrtIterW A hi lo
    (if e < LA.w then R.shl R.one (R.ofUSize e.toUSize) else R.sub R.zero R.one)

public theorem val_sqrt2W (hi lo : L) :
    LA.val (sqrt2W A hi lo) = _root_.Nat.sqrt (LA.val hi * 2 ^ LA.w + LA.val lo) := by
  apply sqrtIterW_eq
  have hN : LA.val hi * 2 ^ LA.w + LA.val lo < 2 ^ LA.w * 2 ^ LA.w := by
    have := LA.val_lt hi; have := LA.val_lt lo
    have := Nat.mul_le_mul_right (2 ^ LA.w) (show LA.val hi + 1 ≤ 2 ^ LA.w by lia)
    lia
  have hB := four_le (R := R)
  have hL := log2two_eq (A := A) hi lo
  generalize LA.val hi * 2 ^ LA.w + LA.val lo = N at hN hL ⊢
  split
  · rename_i he
    generalize log2two A hi lo = l at he hL
    have hwU : LA.w < USize.size := by rw [← R.toNat_wU]; exact USize.toNat_lt_size _
    have hpow : 2 ^ (l / 2 + 1) < 2 ^ LA.w := Nat.pow_lt_pow_right (by decide) he
    have hv : LA.val (R.ofUSize (l / 2 + 1).toUSize) = l / 2 + 1 := by
      have := Nat.lt_two_pow_self (n := LA.w)
      rw [R.val_ofUSize, Nat.toUSize_eq, USize.toNat_ofNat_of_lt' (by lia),
        Nat.mod_eq_of_lt (by lia)]
    rw [R.val_shl, R.val_one, hv, Nat.mod_eq_of_lt he, Nat.one_mul, Nat.mod_eq_of_lt hpow]
    refine Nat.le_of_lt (sqrt_lt_of ?_)
    -- `N < 2^(log₂ N + 1) ≤ 2^(2 e)`.
    have := Nat.lt_log2_self (n := N)
    rw [← hL] at this
    rw [← Nat.pow_add]
    exact Nat.lt_of_lt_of_le this (Nat.pow_le_pow_right (by decide) (by lia))
  · rw [R.val_sub, R.val_zero, R.val_one, Nat.zero_add, Nat.mod_eq_of_lt (by lia)]
    exact Nat.le_pred_of_lt (sqrt_lt_of hN)

end MPN.WordArray
