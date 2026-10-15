/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bignum.Div.Basecase
public import Bignum.Bits

/-!
# Division by two limbs

`divRem2 a d₁ d₀` divides `a` by the two-limb number `d = d₁ β + d₀`, like GMP's `mpn_divrem_2`:
the divisor is normalized to a word `V = d 2^s` with its top bit set, `a` is shifted left by `s`
bits, and one pass from the top limb down divides the remainder so far, a word below `V`, followed
by the next limb, by `V`. The remainder shifted back is `a % d`.

Each step estimates the quotient limb with `qEstimate3`, from the top three limbs of the window
and both limbs of `V`, which is exact for a divisor of two limbs; `div2Fix` then decreases it while
it is too large, which never happens but needs no proof that it doesn't: the estimate is never too
small, so the loop stops exactly at the quotient. The comparison and the remainder use words only:
`q V = ph β + a₀` against `W = R β + x`.
-/

open ScalarArray

namespace Bignum

/--
Decreases `q` while `q (vt β + vs)` exceeds `R β + x`, then returns `q` with the remainder
`R β + x - q (vt β + vs)`, all in words.
-/
def div2Fix (vt vs : UInt32) (R : UInt64) (x q : UInt32) : UInt32 × UInt64 :=
  let a := q.toUInt64 * vs.toUInt64
  let ph := q.toUInt64 * vt.toUInt64 + (a >>> 32)
  let a₀ := a.toUInt32
  if q ≠ 0 ∧ (R < ph ∨ (R = ph ∧ x < a₀)) then
    div2Fix vt vs R x (q - 1)
  else
    (q, ((R - ph) <<< 32) + x.toUInt64 - a₀.toUInt64)
termination_by q.toNat
decreasing_by
  rw [UInt32.toNat_sub_of_le _ _ (by
    rw [UInt32.le_iff_toNat_le]
    have : q.toNat ≠ 0 := fun h => ‹q ≠ 0 ∧ _›.1 (UInt32.toNat_inj.1 (by simpa using h))
    simp; omega)]
  have : q.toNat ≠ 0 := fun h => ‹q ≠ 0 ∧ _›.1 (UInt32.toNat_inj.1 (by simpa using h))
  simp; omega

/-- `div2Fix` divides `W = R β + x` by `V = vt β + vs` when it starts at or above the quotient. -/
private theorem div2Fix_spec (vt vs : UInt32) (R : UInt64) (x q : UInt32) (V W : Nat)
    (hV : V = vt.toNat * 2 ^ 32 + vs.toNat) (hW : W = R.toNat * 2 ^ 32 + x.toNat)
    (hVpos : 0 < V) (hq : W / V ≤ q.toNat) :
    (div2Fix vt vs R x q).1.toNat = W / V ∧ (div2Fix vt vs R x q).2.toNat = W % V := by
  induction q using div2Fix.induct vt vs R x with
  | case1 q a ph a₀ hc ih =>
    rw [div2Fix]
    simp only [a, ph, a₀] at hc
    rw [ite_eq_left hc]
    have hq0 : q.toNat ≠ 0 := fun h => hc.1 (UInt32.toNat_inj.1 (by simpa using h))
    have hvt := vt.toNat_lt
    have hvs := vs.toNat_lt
    have hq32 := q.toNat_lt
    have hx := x.toNat_lt
    have hav : (q.toUInt64 * vs.toUInt64).toNat = q.toNat * vs.toNat := by
      rw [UInt64.toNat_mul, UInt32.toNat_toUInt64, UInt32.toNat_toUInt64]
      exact Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le (Nat.mul_lt_mul'' hq32 hvs) (by decide))
    have hqv : (q.toUInt64 * vt.toUInt64).toNat = q.toNat * vt.toNat := by
      rw [UInt64.toNat_mul, UInt32.toNat_toUInt64, UInt32.toNat_toUInt64]
      exact Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le (Nat.mul_lt_mul'' hq32 hvt) (by decide))
    have hle₁ : q.toNat * vt.toNat ≤ (2 ^ 32 - 1) * (2 ^ 32 - 1) :=
      Nat.mul_le_mul (by omega) (by omega)
    have hle₂ : q.toNat * vs.toNat / 2 ^ 32 < 2 ^ 32 := by
      rw [Nat.div_lt_iff_lt_mul (by decide)]
      exact Nat.lt_of_lt_of_le (Nat.mul_lt_mul'' hq32 hvs) (by decide)
    have hph : (q.toUInt64 * vt.toUInt64 + ((q.toUInt64 * vs.toUInt64) >>> 32)).toNat =
        q.toNat * vt.toNat + q.toNat * vs.toNat / 2 ^ 32 := by
      rw [UInt64.toNat_add, hqv, UInt64.toNat_shiftRight, hav]
      simp only [UInt64.reduceToNat, Nat.reduceMod, Nat.shiftRight_eq_div_pow]
      exact Nat.mod_eq_of_lt (by omega)
    have ha₀ : ((q.toUInt64 * vs.toUInt64).toUInt32).toNat = q.toNat * vs.toNat % 2 ^ 32 := by
      rw [UInt64.toNat_toUInt32, hav]
    -- `q V = ph β + a₀`, and the condition says `W < q V`.
    have hP : q.toNat * V = (q.toNat * vt.toNat + q.toNat * vs.toNat / 2 ^ 32) * 2 ^ 32 +
        q.toNat * vs.toNat % 2 ^ 32 := by
      have := Nat.div_add_mod (q.toNat * vs.toNat) (2 ^ 32)
      rw [hV, Nat.mul_add, Nat.add_mul, ← Nat.mul_assoc]
      omega
    have hlt : W < q.toNat * V := by
      have h2 := hc.2
      simp only [UInt64.lt_iff_toNat_lt, UInt32.lt_iff_toNat_lt, hph, ha₀] at h2
      rcases h2 with h2 | ⟨h2, h3⟩
      · rw [hP, hW]; omega
      · have hR' : R.toNat = q.toNat * vt.toNat + q.toNat * vs.toNat / 2 ^ 32 := by
          rw [h2, hph]
        rw [hP, hW, hR']; omega
    have hdiv : W / V < q.toNat := (Nat.div_lt_iff_lt_mul hVpos).2 (by
      rw [Nat.mul_comm] at hlt; first | exact hlt | (rw [Nat.mul_comm]; exact hlt))
    apply ih
    rw [UInt32.toNat_sub_of_le _ _ (by rw [UInt32.le_iff_toNat_le]; simp; omega)]
    simp only [UInt32.reduceToNat]
    omega
  | case2 q a ph a₀ hc =>
    rw [div2Fix]
    simp only [a, ph, a₀] at hc
    rw [ite_eq_right hc]
    have hvt := vt.toNat_lt
    have hvs := vs.toNat_lt
    have hq32 := q.toNat_lt
    have hx := x.toNat_lt
    have hR := R.toNat_lt
    have hav : (q.toUInt64 * vs.toUInt64).toNat = q.toNat * vs.toNat := by
      rw [UInt64.toNat_mul, UInt32.toNat_toUInt64, UInt32.toNat_toUInt64]
      exact Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le (Nat.mul_lt_mul'' hq32 hvs) (by decide))
    have hqv : (q.toUInt64 * vt.toUInt64).toNat = q.toNat * vt.toNat := by
      rw [UInt64.toNat_mul, UInt32.toNat_toUInt64, UInt32.toNat_toUInt64]
      exact Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le (Nat.mul_lt_mul'' hq32 hvt) (by decide))
    have hle₁ : q.toNat * vt.toNat ≤ (2 ^ 32 - 1) * (2 ^ 32 - 1) :=
      Nat.mul_le_mul (by omega) (by omega)
    have hle₂ : q.toNat * vs.toNat / 2 ^ 32 < 2 ^ 32 := by
      rw [Nat.div_lt_iff_lt_mul (by decide)]
      exact Nat.lt_of_lt_of_le (Nat.mul_lt_mul'' hq32 hvs) (by decide)
    have hph : (q.toUInt64 * vt.toUInt64 + ((q.toUInt64 * vs.toUInt64) >>> 32)).toNat =
        q.toNat * vt.toNat + q.toNat * vs.toNat / 2 ^ 32 := by
      rw [UInt64.toNat_add, hqv, UInt64.toNat_shiftRight, hav]
      simp only [UInt64.reduceToNat, Nat.reduceMod, Nat.shiftRight_eq_div_pow]
      exact Nat.mod_eq_of_lt (by omega)
    have ha₀ : ((q.toUInt64 * vs.toUInt64).toUInt32).toNat = q.toNat * vs.toNat % 2 ^ 32 := by
      rw [UInt64.toNat_toUInt32, hav]
    have hP : q.toNat * V = (q.toNat * vt.toNat + q.toNat * vs.toNat / 2 ^ 32) * 2 ^ 32 +
        q.toNat * vs.toNat % 2 ^ 32 := by
      have := Nat.div_add_mod (q.toNat * vs.toNat) (2 ^ 32)
      rw [hV, Nat.mul_add, Nat.add_mul, ← Nat.mul_assoc]
      omega
    generalize q.toNat * vt.toNat + q.toNat * vs.toNat / 2 ^ 32 = PH at hph hP
    generalize q.toNat * vs.toNat % 2 ^ 32 = A₀ at ha₀ hP
    have hA₀ : A₀ < 2 ^ 32 := by rw [← ha₀]; exact UInt32.toNat_lt _
    -- Not too large: `q V ≤ W`, so `q` is the quotient.
    have hge : q.toNat * V ≤ W := by
      by_cases hq0 : q = 0
      · rw [hq0, UInt32.toNat_zero, Nat.zero_mul]; exact Nat.zero_le _
      · have h2 : ¬(R < q.toUInt64 * vt.toUInt64 + ((q.toUInt64 * vs.toUInt64) >>> 32) ∨
            (R = q.toUInt64 * vt.toUInt64 + ((q.toUInt64 * vs.toUInt64) >>> 32) ∧
              x < (q.toUInt64 * vs.toUInt64).toUInt32)) := fun h => hc ⟨hq0, h⟩
        simp only [UInt64.lt_iff_toNat_lt, UInt32.lt_iff_toNat_lt, hph, ha₀, not_or,
          not_and, Nat.not_lt] at h2
        have h3 : PH ≤ R.toNat := h2.1
        rw [hP, hW]
        by_cases he : R.toNat = PH
        · have := h2.2 (UInt64.toNat_inj.1 (by rw [he, hph]))
          omega
        · omega
    have hqq : q.toNat = W / V :=
      Nat.le_antisymm ((Nat.le_div_iff_mul_le hVpos).2 hge) hq
    refine ⟨hqq, ?_⟩
    -- The remainder `W - q V` is below `V < 2⁶⁴`, so the word arithmetic doesn't wrap.
    have hmod : W % V = W - q.toNat * V := by
      rw [hqq, Nat.mod_eq_sub_mul_div, Nat.mul_comm]
    have hrem := Nat.mod_lt W hVpos
    have hV64 : V ≤ 2 ^ 64 := by rw [hV]; omega
    have hRph : PH ≤ R.toNat := by rw [hP, hW] at hge; omega
    rw [hmod]
    rw [hmod, hP, hW] at hrem
    rw [hP, hW]
    rw [UInt64.toNat_sub, UInt64.toNat_add, UInt64.toNat_shiftLeft,
      UInt64.toNat_sub_of_le _ _ (by rw [UInt64.le_iff_toNat_le, hph]; exact hRph), hph,
      UInt32.toNat_toUInt64, UInt32.toNat_toUInt64, ha₀]
    simp only [UInt64.reduceToNat, Nat.reduceMod, Nat.shiftLeft_eq]
    omega

/--
`min ⌊R / vt⌋ (β - 1)`, the first estimate of a quotient limb (`qEstimate` of the two limbs of
`R`). It tests the high half instead of comparing with `2³²`: the kernel would otherwise unfold
the literal while checking the loop that uses it.
-/
@[inline] def div2Est (R : UInt64) (vt : UInt32) : UInt32 :=
  let e := R / vt.toUInt64
  if e >>> 32 = 0 then e.toUInt32 else 0xFFFFFFFF

private theorem toNat_div2Est (R : UInt64) (vt : UInt32) :
    (div2Est R vt).toNat = min (R.toNat / vt.toNat) (2 ^ 32 - 1) := by
  have he : (R / vt.toUInt64).toNat = R.toNat / vt.toNat := by
    rw [UInt64.toNat_div, UInt32.toNat_toUInt64]
  unfold div2Est
  simp only
  split
  · rename_i h
    have h' : (R / vt.toUInt64).toNat / 2 ^ 32 = 0 := by
      have := congrArg UInt64.toNat h
      rw [UInt64.toNat_shiftRight] at this
      simpa [Nat.shiftRight_eq_div_pow] using this
    rw [he] at h'
    rw [UInt64.toNat_toUInt32, he]
    have : R.toNat / vt.toNat < 2 ^ 32 := by
      rcases Nat.lt_or_ge (R.toNat / vt.toNat) (2 ^ 32) with h'' | h''
      · exact h''
      · have := Nat.div_le_div_right (c := 2 ^ 32) h''; simp at this; omega
    omega
  · rename_i h
    have h' : (R / vt.toUInt64).toNat / 2 ^ 32 ≠ 0 := by
      intro h''
      apply h
      apply UInt64.toNat_inj.1
      rw [UInt64.toNat_shiftRight]
      simpa [Nat.shiftRight_eq_div_pow] using h''
    rw [he] at h'
    have : 2 ^ 32 ≤ R.toNat / vt.toNat := by
      rcases Nat.lt_or_ge (R.toNat / vt.toNat) (2 ^ 32) with h'' | h''
      · exact absurd (Nat.div_eq_of_lt h'') h'
      · exact h''
    simp only [UInt32.reduceToNat]
    omega

/-- One step: the quotient limb and remainder of `R β + x` by `vt β + vs`, for `R < vt β + vs`. -/
@[inline] def div2Step (vt vs : UInt32) (R : UInt64) (x : UInt32) : UInt32 × UInt64 :=
  let wt := (R >>> 32).toUInt32
  let wn := R.toUInt32
  div2Fix vt vs R x (qEstimate3 (div2Est R vt) wt wn x vt vs)

private theorem div2Step_spec (vt vs : UInt32) (R : UInt64) (x : UInt32) (hvt : 0 < vt.toNat)
    (hR : R.toNat < vt.toNat * 2 ^ 32 + vs.toNat) :
    (div2Step vt vs R x).1.toNat =
        (R.toNat * 2 ^ 32 + x.toNat) / (vt.toNat * 2 ^ 32 + vs.toNat) ∧
      (div2Step vt vs R x).2.toNat =
        (R.toNat * 2 ^ 32 + x.toNat) % (vt.toNat * 2 ^ 32 + vs.toNat) := by
  have hR64 := R.toNat_lt
  have hx := x.toNat_lt
  have hwt : ((R >>> 32).toUInt32).toNat = R.toNat / 2 ^ 32 := by
    rw [UInt64.toNat_toUInt32, UInt64.toNat_shiftRight]
    simp only [UInt64.reduceToNat, Nat.reduceMod, Nat.shiftRight_eq_div_pow]
    exact Nat.mod_eq_of_lt (by omega)
  have hwn : (R.toUInt32).toNat = R.toNat % 2 ^ 32 := UInt64.toNat_toUInt32 _
  have hRsplit : R.toNat / 2 ^ 32 * 2 ^ 32 + R.toNat % 2 ^ 32 = R.toNat := by
    have := Nat.div_add_mod R.toNat (2 ^ 32); omega
  obtain ⟨V, hVdef⟩ : ∃ V, vt.toNat * 2 ^ 32 + vs.toNat = V := ⟨_, rfl⟩
  obtain ⟨W, hW⟩ : ∃ W, R.toNat * 2 ^ 32 + x.toNat = W := ⟨_, rfl⟩
  rw [hVdef] at hR ⊢
  rw [hW]
  have hVpos : 0 < V := by omega
  -- The quotient `Q` is at most both estimates.
  have hQV : W / V * V ≤ W := Nat.div_mul_le_self W V
  have hQβ : W / V < 2 ^ 32 := by
    rw [Nat.div_lt_iff_lt_mul hVpos]
    have := Nat.mul_le_mul_right (2 ^ 32) (show R.toNat + 1 ≤ V by omega)
    rw [Nat.succ_mul] at this
    rw [Nat.mul_comm (2 ^ 32) V]
    omega
  have hQ₀ : W / V * vt.toNat ≤ R.toNat := by
    -- `Q vt β ≤ Q V ≤ W < (R + 1) β`.
    have h₁ : W / V * vt.toNat * 2 ^ 32 ≤ W / V * V := by
      rw [Nat.mul_assoc]
      exact Nat.mul_le_mul_left _ (by omega)
    have h₂ : W / V * vt.toNat * 2 ^ 32 < (R.toNat + 1) * 2 ^ 32 := by
      rw [Nat.succ_mul]; omega
    exact Nat.le_of_lt_succ (Nat.lt_of_mul_lt_mul_right h₂)
  have hest := toNat_div2Est R vt
  have hle : (div2Est R vt).toNat * vt.toNat ≤
      ((R >>> 32).toUInt32).toNat * 2 ^ 32 + (R.toUInt32).toNat := by
    rw [hwt, hwn, hRsplit, hest]
    exact Nat.le_trans (Nat.mul_le_mul_right _ (Nat.min_le_left _ _)) (Nat.div_mul_le_self _ _)
  have h₀ : W / V ≤ (div2Est R vt).toNat := by
    rw [hest]
    exact Nat.le_min.2 ⟨(Nat.le_div_iff_mul_le hvt).2 hQ₀, by omega⟩
  have h₁ : W / V * (vt.toNat * 2 ^ 32 + vs.toNat) ≤
      (((R >>> 32).toUInt32).toNat * 2 ^ 32 + (R.toUInt32).toNat) * 2 ^ 32 + x.toNat := by
    rw [hwt, hwn, hRsplit, hW, hVdef]
    exact hQV
  have hq := qEstimate3_ge _ _ _ x vt vs (W / V) hle h₀ h₁
  exact div2Fix_spec vt vs R x _ V W hVdef.symm hW.symm hVpos hq

/--
The loop of `foldrInPlace` with `div2Step`: below index `k` the limbs of `A` are untouched, above
it they hold the quotient `W` of the limbs of `A` from `k` on by `V`, and the carry is the
remainder.
-/
private theorem div2_loop (vt vs : UInt32) (V : Nat) (hV : vt.toNat * 2 ^ 32 + vs.toNat = V)
    (hvt : 0 < vt.toNat) (A : List UInt32) (n : Nat)
    (hn : n = A.length) (s : UInt32Array.Slice) (hs : s.size = n) (k : Nat) (hk : k ≤ n)
    (r : UInt64) (W : List UInt32) (h0 : s.start = 0) (hl : s.array.toList = A.take k ++ W)
    (hW : W.length = A.length - k) (hv : ofLimbs W * V + r.toNat = ofLimbs (A.drop k))
    (hr : r.toNat < V) :
    let p := UInt32Array.Slice.foldrInPlace.loop n (fun _ _ x r => div2Step vt vs r x) s hs k hk r
    ofLimbs p.1.array.toList * V + p.2.toNat = ofLimbs A ∧ p.2.toNat < V := by
  induction k generalizing s r W with
  | zero =>
    simp only [UInt32Array.Slice.foldrInPlace.loop]
    rw [hl, List.take_zero, List.nil_append]
    rw [List.drop_zero] at hv
    exact ⟨hv, hr⟩
  | succ k ih =>
    rw [UInt32Array.Slice.foldrInPlace.loop]
    have hkA : k < A.length := by omega
    have hsa : k < s.array.size := by
      have := s.stop_le_array_size; have := s.size_eq; have := s.start_le_stop; omega
    have hsk : s[k]'(by omega) = A[k] := by
      have h := List.getElem_of_eq hl (i := k) (by simpa using hsa)
      rw [List.getElem_append_left (by simp; omega), List.getElem_take,
        UInt32Array.getElem_toList] at h
      rw [UInt32Array.Slice.getElem_eq]
      simpa [h0] using h
    have hdrop := List.drop_eq_getElem_cons hkA
    obtain ⟨h₁, h₂⟩ := div2Step_spec vt vs r (s[k]'(by omega)) hvt (by rw [hV]; exact hr)
    rw [hV] at h₁ h₂
    refine ih _ _ _ _ ((div2Step vt vs r (s[k]'(by omega))).1 :: W) ?_ ?_ ?_ ?_ ?_
    · rw [UInt32Array.Slice.start_set, h0]
    · rw [UInt32Array.Slice.array_set, UInt32Array.toList_set, hl, h0, Nat.zero_add,
        List.take_succ_eq_append_getElem hkA, List.append_assoc,
        List.set_append_right _ _ (by simp; omega)]
      simp [Nat.min_eq_left (Nat.le_of_lt hkA)]
    · simp only [List.length_cons]; omega
    · -- `q V + β W V + r' = r β + x + β W V = x + β (W V + r)`.
      rw [ofLimbs_cons, hdrop, ofLimbs_cons, ← hv, h₁, h₂, hsk]
      have := Nat.div_add_mod (r.toNat * 2 ^ 32 + A[k].toNat) V
      generalize (r.toNat * 2 ^ 32 + A[k].toNat) / V = q at *
      generalize (r.toNat * 2 ^ 32 + A[k].toNat) % V = m at *
      grind
    · rw [h₂]; exact Nat.mod_lt _ (by omega)

/-- The quotient limbs of `x` by `vt β + vs` in place, from the top limb down, and the remainder
shifted right by `s`. -/
def divRem2Limbs (x : UInt32Array) (vt vs : UInt32) (s : UInt64) : UInt32Array × UInt64 :=
  x.toSlice.foldrInPlaceThen (0 : UInt64) (fun _ _ v R => div2Step vt vs R v)
    (fun r R => (r.array, R >>> s))

/--
`a / d` as limbs, untrimmed, and `a % d` as a word, for `d = d₁ β + d₀` with `d₁ ≠ 0`, like GMP's
`mpn_divrem_2`.
-/
public def divRem2 (a : UInt32Array.Slice) (d₁ d₀ : UInt32) : UInt32Array × UInt64 :=
  let s := 31 - d₁.toNat.log2
  let D : UInt64 := ((d₁.toUInt64 <<< 32) + d₀.toUInt64) <<< s.toUInt64
  divRem2Limbs (shiftLeft a s) (D >>> 32).toUInt32 D.toUInt32 s.toUInt64

/-- `divRem2` divides: `a = q d + r` with `r < d`. -/
public theorem divRem2_spec (a : UInt32Array.Slice) (d₁ d₀ : UInt32) (hd : d₁ ≠ 0) :
    toNat (divRem2 a d₁ d₀).1 * (d₁.toNat * 2 ^ 32 + d₀.toNat) + (divRem2 a d₁ d₀).2.toNat =
        toNat a ∧
      (divRem2 a d₁ d₀).2.toNat < d₁.toNat * 2 ^ 32 + d₀.toNat := by
  simp only [divRem2, divRem2Limbs, UInt32Array.Slice.foldrInPlaceThen_eq,
    UInt32Array.Slice.foldrInPlace]
  have hd₁ : d₁.toNat ≠ 0 := fun h => hd (UInt32.toNat_inj.1 (by simpa using h))
  have hd₁β := d₁.toNat_lt
  have hd₀β := d₀.toNat_lt
  have hl : d₁.toNat.log2 < 32 := (Nat.log2_lt hd₁).2 hd₁β
  have hlt := Nat.lt_log2_self (n := d₁.toNat)
  generalize d₁.toNat.log2 = l at hl hlt
  -- `d 2^s < 2^(l + 1) β 2^(31 - l) = 2⁶⁴`.
  have hD64 : (d₁.toNat * 2 ^ 32 + d₀.toNat) * 2 ^ (31 - l) < 2 ^ 64 := by
    have h₁ : d₁.toNat * 2 ^ 32 + d₀.toNat < 2 ^ (l + 1) * 2 ^ 32 := by
      have := Nat.mul_le_mul_right (2 ^ 32) (show d₁.toNat + 1 ≤ 2 ^ (l + 1) by omega)
      rw [Nat.succ_mul] at this
      omega
    have h₂ : 2 ^ (l + 1) * 2 ^ 32 * 2 ^ (31 - l) = 2 ^ 64 := by
      rw [← Nat.pow_add, ← Nat.pow_add]; congr 1; omega
    rw [← h₂]
    exact Nat.mul_lt_mul_of_pos_right h₁ (Nat.two_pow_pos _)
  have hs64 : (31 - l).toUInt64.toNat = 31 - l := by
    simp only [Nat.toUInt64, UInt64.toNat_ofNat']
    exact Nat.mod_eq_of_lt (by omega)
  have hd : ((d₁.toUInt64 <<< 32) + d₀.toUInt64).toNat = d₁.toNat * 2 ^ 32 + d₀.toNat := by
    rw [UInt64.toNat_add, UInt64.toNat_shiftLeft, UInt32.toNat_toUInt64, UInt32.toNat_toUInt64]
    simp only [UInt64.reduceToNat, Nat.reduceMod, Nat.shiftLeft_eq]
    omega
  have hD : (((d₁.toUInt64 <<< 32) + d₀.toUInt64) <<< (31 - l).toUInt64).toNat =
      (d₁.toNat * 2 ^ 32 + d₀.toNat) * 2 ^ (31 - l) := by
    rw [UInt64.toNat_shiftLeft, hd, hs64, Nat.mod_eq_of_lt (show 31 - l < 64 by omega),
      Nat.shiftLeft_eq, Nat.mod_eq_of_lt hD64]
  generalize ((d₁.toUInt64 <<< 32) + d₀.toUInt64) <<< (31 - l).toUInt64 = D at hD
  obtain ⟨d, hdd⟩ : ∃ d, d₁.toNat * 2 ^ 32 + d₀.toNat = d := ⟨_, rfl⟩
  rw [hdd] at hD hD64 ⊢
  have hdpos : 2 ^ 32 ≤ d := by
    rw [← hdd]
    exact Nat.le_add_right_of_le (Nat.le_mul_of_pos_left _ (by omega))
  -- `vt β + vs = D`, with `vt ≠ 0`.
  have hvt : ((D >>> 32).toUInt32).toNat = D.toNat / 2 ^ 32 := by
    rw [UInt64.toNat_toUInt32, UInt64.toNat_shiftRight]
    simp only [UInt64.reduceToNat, Nat.reduceMod, Nat.shiftRight_eq_div_pow]
    have := D.toNat_lt
    exact Nat.mod_eq_of_lt (by omega)
  have hvs : (D.toUInt32).toNat = D.toNat % 2 ^ 32 := UInt64.toNat_toUInt32 _
  have hV : ((D >>> 32).toUInt32).toNat * 2 ^ 32 + (D.toUInt32).toNat = D.toNat := by
    rw [hvt, hvs]; exact Nat.div_add_mod' _ _
  have hDge : 2 ^ 32 ≤ D.toNat := by
    rw [hD]; exact Nat.le_trans hdpos (Nat.le_mul_of_pos_right _ (Nat.two_pow_pos _))
  have hvt0 : 0 < ((D >>> 32).toUInt32).toNat := by rw [hvt]; exact Nat.div_pos hDge (by decide)
  -- The loop over the shifted limbs.
  generalize hx : shiftLeft a (31 - l) = x
  have hxv : ofLimbs x.toList = toNat a * 2 ^ (31 - l) := by
    rw [← toNat_toSlice, ← hx, toNat_shiftLeft]
  have h := div2_loop (D >>> 32).toUInt32 D.toUInt32 D.toNat hV hvt0 x.toList _ (by simp)
    x.toSlice rfl _ (Nat.le_refl _) 0 [] (by simp) (by rw [List.take_of_length_le (by simp)]; simp)
    (by simp) (by rw [List.drop_of_length_le (by simp)]; simp) (by simp; omega)
  rw [hxv, hD] at h
  obtain ⟨h₁, h₂⟩ := h
  generalize (UInt32Array.Slice.foldrInPlace.loop _ (fun _ _ x r =>
    div2Step (D >>> 32).toUInt32 D.toUInt32 r x) _ _ _ _ (0 : UInt64)) = p at h₁ h₂ ⊢
  rw [toNat_toSlice]
  -- `a 2^s = Q d 2^s + R` with `R < d 2^s`, so `R = (a - Q d) 2^s`.
  generalize ofLimbs p.1.array.toList = Q at h₁ ⊢
  have hR : (p.2 >>> (31 - l).toUInt64).toNat = p.2.toNat / 2 ^ (31 - l) := by
    rw [UInt64.toNat_shiftRight, hs64, Nat.mod_eq_of_lt (show 31 - l < 64 by omega),
      Nat.shiftRight_eq_div_pow]
  rw [hR]
  generalize p.2.toNat = R at h₁ h₂
  have hP : 0 < 2 ^ (31 - l) := Nat.two_pow_pos _
  have hQd : Q * d ≤ toNat a := by
    have : Q * d * 2 ^ (31 - l) ≤ toNat a * 2 ^ (31 - l) := by
      rw [← h₁, Nat.mul_assoc]; omega
    exact Nat.le_of_mul_le_mul_right this hP
  have hRv : R = (toNat a - Q * d) * 2 ^ (31 - l) := by
    rw [Nat.sub_mul, ← h₁, Nat.mul_assoc]; omega
  rw [hRv, Nat.mul_div_cancel _ hP]
  refine ⟨by omega, ?_⟩
  have : (toNat a - Q * d) * 2 ^ (31 - l) < d * 2 ^ (31 - l) := by rw [← hRv]; exact h₂
  exact Nat.lt_of_mul_lt_mul_right this

/-- A number of two limbs is `s₀ + β s₁`. -/
public theorem toNat_of_size_eq_two {s : UInt32Array.Slice} (h : s.size = 2) :
    toNat s = (s.getD 0 0).toNat + 2 ^ 32 * (s.getD 1 0).toNat := by
  rw [toNat, ← List.take_of_length_le (l := s.copy.toList) (i := 2) (by simp [h]),
    ofLimbs_take_add_one_getD, ofLimbs_take_add_one_getD, getD_eq_getD_toList_copy,
    getD_eq_getD_toList_copy]
  simp

/-- The limbs of a word, trimmed. -/
public def ofWord64 (w : UInt64) : UInt32Array :=
  trim (((UInt32Array.emptyWithCapacity 2).push w.toUInt32).push (w >>> 32).toUInt32)

@[simp] public theorem toNat_ofWord64 (w : UInt64) : toNat (ofWord64 w) = w.toNat := by
  rw [ofWord64, toNat_trim, toNat_toSlice]
  simp only [UInt32Array.toList_push, UInt32Array.emptyWithCapacity_eq_empty,
    UInt32Array.toList_empty, List.nil_append, List.cons_append, ofLimbs_cons, ofLimbs_nil,
    UInt64.toNat_toUInt32, UInt64.toNat_shiftRight, Nat.shiftRight_eq_div_pow]
  have := w.toNat_lt
  simp only [UInt64.reduceToNat, Nat.reduceMod]
  omega

public theorem isTrimmed_ofWord64 (w : UInt64) : isTrimmed (ofWord64 w) = true := isTrimmed_trim _

end Bignum
