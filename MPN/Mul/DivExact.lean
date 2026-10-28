/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import MPN.Bits

/-!
# Exact division by small constants

The interpolations of the Toom algorithms divide exactly by `2`, `3`, `4` and `5`. By a power of
two it is a shift. By an odd `d` it is a multiplication by the inverse of `d` modulo `β` from the
bottom limb up, like GMP's
`mpn_divexact_by3`, without the hardware divider.
-/

open ScalarArray

namespace MPN

/-- `x / 2`, which is exact when `x` is even: `x` shifted right by one bit in place. -/
public def divExact2 (x : UInt32Array) : UInt32Array := shrLimbs x (1 : Nat).toUInt64

public theorem toNat_divExact2 (x : UInt32Array) (X : Nat) (hx : toNat x = 2 * X) :
    toNat (divExact2 x) = X := by
  rw [divExact2, toNat_shrLimbs _ _ (by decide), hx, Nat.pow_one, Nat.mul_div_cancel_left _
    (by decide)]

/-- `x / 4`, which is exact when `4` divides `x`: `x` shifted right by two bits in place. -/
public def divExact4 (x : UInt32Array) : UInt32Array := shrLimbs x (2 : Nat).toUInt64

public theorem toNat_divExact4 (x : UInt32Array) (X : Nat) (hx : toNat x = 4 * X) :
    toNat (divExact4 x) = X := by
  rw [divExact4, toNat_shrLimbs _ _ (by decide), hx, show (2 : Nat) ^ 2 = 4 by rfl,
    Nat.mul_div_cancel_left _ (by decide)]

/--
One limb of an exact division by an odd `d` whose inverse modulo `β` is `inv`: the quotient limb
`q` is `(v - c) inv` modulo `β`, so that `d q + c = v + β c'`, where the carry out `c'` is the
high limb of `d q` plus the borrow of `v - c`.
-/
@[inline] def divOddStep (d inv v c : UInt32) : UInt32 × UInt32 :=
  let t := v.toUInt64 - c.toUInt64
  let q := t.toUInt32 * inv
  (q, ((q.toUInt64 * d.toUInt64) >>> 32).toUInt32 + (t >>> 63).toUInt32)

private theorem divOddStep_spec (d inv v c : UInt32) (hinv : d.toNat * inv.toNat % 2 ^ 32 = 1)
    (hc : c.toNat ≤ d.toNat) :
    d.toNat * (divOddStep d inv v c).1.toNat + c.toNat =
        v.toNat + 2 ^ 32 * (divOddStep d inv v c).2.toNat ∧
      (divOddStep d inv v c).2.toNat ≤ d.toNat := by
  have := v.toNat_lt
  have hd := d.toNat_lt
  have hd0 : 0 < d.toNat := by
    rcases Nat.eq_zero_or_pos d.toNat with h | h
    · rw [h, Nat.zero_mul] at hinv; simp at hinv
    · exact h
  simp only [divOddStep, UInt32.toNat_mul, UInt32.toNat_add, UInt64.toNat_toUInt32,
    UInt64.toNat_sub, UInt64.toNat_mul, UInt64.toNat_shiftRight, UInt32.toNat_toUInt64,
    Nat.shiftRight_eq_div_pow, UInt64.reduceToNat, Nat.reducePow, Nat.reduceMod]
  simp only [Nat.reducePow] at hinv
  -- `t = v - c` as a 64-bit word: its low limb `s` and its borrow `b`.
  generalize ht : (18446744073709551616 - c.toNat + v.toNat) % 18446744073709551616 = t
  have hsb : t % 4294967296 + c.toNat = v.toNat + 4294967296 * (t / 9223372036854775808) ∧
      t / 9223372036854775808 ≤ 1 := by
    lia
  -- `d q ≡ s` modulo `β`, since `d inv ≡ 1`.
  have hq : d.toNat * (t % 4294967296 * inv.toNat % 4294967296) % 4294967296 =
      t % 4294967296 := by
    rw [Nat.mul_mod, Nat.mod_mod, ← Nat.mul_mod, ← Nat.mul_assoc, Nat.mul_comm d.toNat,
      Nat.mul_assoc, Nat.mul_mod, hinv, Nat.mul_one, Nat.mod_mod,
      Nat.mod_eq_of_lt (Nat.mod_lt _ (by decide))]
  have hqlt := Nat.mod_lt (t % 4294967296 * inv.toNat) (show 0 < 4294967296 by decide)
  generalize t % 4294967296 * inv.toNat % 4294967296 = q at *
  generalize t % 4294967296 = s at *
  generalize t / 9223372036854775808 = b at *
  -- `d q = β h + s` with `h < d`.
  have hm : q * d.toNat < 18446744073709551616 := by
    have := Nat.mul_lt_mul'' hqlt hd
    simpa using this
  have hdm := Nat.div_add_mod (d.toNat * q) 4294967296
  rw [hq] at hdm
  have hh : d.toNat * q / 4294967296 < d.toNat := by
    rw [Nat.div_lt_iff_lt_mul (by decide)]
    have := Nat.mul_lt_mul_of_pos_right hqlt hd0
    rw [Nat.mul_comm d.toNat q, Nat.mul_comm d.toNat]
    exact this
  rw [Nat.mul_comm q d.toNat] at hm ⊢
  generalize d.toNat * q / 4294967296 = h at *
  generalize d.toNat * q = m at *
  rw [Nat.mod_eq_of_lt hm, Nat.mod_eq_of_lt (show m / 4294967296 < 4294967296 by lia),
    Nat.mod_eq_of_lt (show b < 4294967296 by lia)]
  have hmh : m / 4294967296 = h := by lia
  rw [hmh, Nat.mod_eq_of_lt (show h + b < 4294967296 by lia)]
  lia

/--
The loop of `foldlInPlace` with `divOddStep`: the first `k` limbs hold `W`, the rest still hold
`O` from `k` on, and `d W = (the first k limbs of O) + βᵏ c`.
-/
private theorem divOdd_loop (d inv : UInt32) (hinv : d.toNat * inv.toNat % 2 ^ 32 = 1)
    (O : List UInt32) (n : Nat) (hn : n = O.length) (r : UInt32Array.Slice)
    (hs : r.size = n) (k : Nat) (c : UInt32) (W : List UInt32) (h0 : r.start = 0)
    (hl : r.array.toList = W ++ O.drop k) (hW : W.length = k) (hkn : k ≤ n)
    (hv : d.toNat * ofLimbs W = ofLimbs (O.take k) + 2 ^ (32 * k) * c.toNat)
    (hc : c.toNat ≤ d.toNat) :
    ∃ W', (UInt32Array.Slice.foldlInPlace.loop n (fun _ _ v c => divOddStep d inv v c) r hs k
        c).1.array.toList = W' ∧ W'.length = n ∧
      d.toNat * ofLimbs W' = ofLimbs O + 2 ^ (32 * n) * (UInt32Array.Slice.foldlInPlace.loop n
        (fun _ _ v c => divOddStep d inv v c) r hs k c).2.toNat ∧
      (UInt32Array.Slice.foldlInPlace.loop n
        (fun _ _ v c => divOddStep d inv v c) r hs k c).2.toNat ≤ d.toNat := by
  induction hd : n - k generalizing k r c W with
  | zero =>
    have hk : k = n := by lia
    subst hk
    rw [UInt32Array.Slice.foldlInPlace.loop, dite_eq_right (by lia)]
    refine ⟨W, ?_, hW, ?_, hc⟩
    · rw [hl, List.drop_of_length_le (by lia), List.append_nil]
    · rw [hv, List.take_of_length_le (by lia)]
  | succ e ih =>
    have hk : k < n := by lia
    have hkO : k < O.length := by lia
    rw [UInt32Array.Slice.foldlInPlace.loop, dite_eq_left hk]
    have hsa : k < r.array.size := by
      have := r.stop_le_array_size; have := r.size_eq; have := r.start_le_stop; lia
    have hdrop := List.drop_eq_getElem_cons hkO
    have hl' := hl
    rw [hdrop] at hl'
    have hrk : r[k]'(by lia) = O[k] := by
      have h := List.getElem_of_eq hl' (i := k) (by simpa using hsa)
      rw [List.getElem_append_right (by lia)] at h
      simp only [hW, Nat.sub_self, List.getElem_cons_zero, UInt32Array.getElem_toList] at h
      rw [UInt32Array.Slice.getElem_eq]
      simpa [h0] using h
    obtain ⟨h₁, h₂⟩ := divOddStep_spec d inv (r[k]'(by lia)) c hinv hc
    refine ih _ _ (k + 1) _ (W ++ [(divOddStep d inv (r[k]'(by lia)) c).1]) ?_ ?_ ?_ (by lia)
      ?_ h₂ (by lia)
    · rw [UInt32Array.Slice.start_set, h0]
    · rw [UInt32Array.Slice.array_set, UInt32Array.toList_set, hl', h0,
        List.set_append_right _ _ (by simp; lia)]
      simp [hW]
      rw [hdrop]
      rfl
    · simp [hW]
    · rw [ofLimbs_concat, hW, List.take_succ_eq_append_getElem hkO, ofLimbs_append, ofLimbs_cons,
        ofLimbs_nil, Nat.mul_zero, Nat.add_zero, List.length_take,
        Nat.min_eq_left (Nat.le_of_lt hkO), ← hrk, Nat.mul_succ, Nat.pow_add]
      generalize (divOddStep d inv (r[k]'(by lia)) c).1.toNat = q at *
      generalize (divOddStep d inv (r[k]'(by lia)) c).2.toNat = c' at *
      generalize (r[k]'(by lia)).toNat = v at *
      generalize ofLimbs W = A at *
      generalize ofLimbs (O.take k) = T at *
      generalize 2 ^ (32 * k) = P at *
      generalize (2 : Nat) ^ 32 = B at *
      generalize d.toNat = D at *
      -- `D (A + P q) = T + P c + P (v + B c' - c) = T + P v + P B c'`.
      have e : D * (A + P * q) + P * c.toNat = T + P * v + P * B * c' + P * c.toNat := by
        have := congrArg (P * ·) h₁
        simp only [Nat.mul_add] at this
        grind
      lia

/--
`x / d`, which is exact when `d` divides `x`, for an odd `d` with inverse `inv` modulo `β`: one
pass from the bottom limb up with `divOddStep`, in place with
`foldlInPlaceThen`, where `divRem1` divides from the top limb down with the hardware divider.
-/
@[inline] public def divExactOdd (x : UInt32Array) (d inv : UInt32) : UInt32Array :=
  x.toSlice.foldlInPlaceThen (0 : UInt32) (fun _ _ v c => divOddStep d inv v c)
    (fun r _ => r.array)

@[simp] public theorem size_divExactOdd (x : UInt32Array) (d inv : UInt32) :
    (divExactOdd x d inv).size = x.size := by
  rw [divExactOdd, UInt32Array.Slice.foldlInPlaceThen_eq]
  simp

public theorem toNat_divExactOdd (x : UInt32Array) (d inv : UInt32)
    (hinv : d.toNat * inv.toNat % 2 ^ 32 = 1) (hodd : d.toNat % 2 = 1) (X : Nat)
    (hx : toNat x = d.toNat * X) : toNat (divExactOdd x d inv) = X := by
  rw [divExactOdd, UInt32Array.Slice.foldlInPlaceThen_eq, UInt32Array.Slice.foldlInPlace,
    toNat_toSlice]
  obtain ⟨W, hl, hW, hv, hcd⟩ := divOdd_loop d inv hinv x.toList x.toSlice.size (by simp)
    x.toSlice rfl 0 0 [] (by simp) (by simp) rfl (Nat.zero_le _) (by simp) (by simp)
  rw [hl]
  generalize (UInt32Array.Slice.foldlInPlace.loop _ (fun _ _ v (c : UInt32) => divOddStep d inv v c)
    _ _ 0 (0 : UInt32)).2 = cc at hv hcd
  generalize cc.toNat = c at hv hcd
  rw [toNat_toSlice] at hx
  rw [hx] at hv
  have hQ := ofLimbs_lt W
  rw [hW] at hQ
  simp only [UInt32Array.size_toSlice, Nat.min_self, Nat.sub_zero] at hQ hv
  -- `d` is odd, so coprime to `βⁿ`.
  have hcop : Nat.Coprime d.toNat (2 ^ (32 * x.size)) := by
    apply Nat.Coprime.pow_right
    rw [Nat.Coprime, Nat.gcd_comm, Nat.gcd_rec, hodd]
    rfl
  have hD : 0 < d.toNat := by lia
  generalize 2 ^ (32 * x.size) = P at *
  generalize d.toNat = D at *
  -- `D (W - X) = P c` with `W < P`, so `c < D`, and `D` divides `c`, so `c = 0`.
  have hcD : c < D := by
    rcases Nat.lt_or_ge c D with h | h
    · exact h
    · have : P * D ≤ P * c := Nat.mul_le_mul_left P h
      have : D * ofLimbs W < D * P := Nat.mul_lt_mul_of_pos_left hQ (by lia)
      lia
  have hdvd : D ∣ P * c := ⟨ofLimbs W - X, by rw [Nat.mul_sub]; lia⟩
  have hc0 : c = 0 := Nat.eq_zero_of_dvd_of_lt (hcop.dvd_of_dvd_mul_left hdvd) hcD
  subst hc0
  rw [Nat.mul_zero, Nat.add_zero] at hv
  exact Nat.eq_of_mul_eq_mul_left hD hv

/-- `x / 3`, exact when `3` divides `x`, with `3⁻¹ = 0xAAAAAAAB` modulo `β`. -/
public def divExact3 (x : UInt32Array) : UInt32Array := divExactOdd x 3 0xAAAAAAAB

public theorem toNat_divExact3 (x : UInt32Array) (X : Nat) (hx : toNat x = 3 * X) :
    toNat (divExact3 x) = X :=
  toNat_divExactOdd x 3 0xAAAAAAAB (by decide) (by decide) X hx

/-- `x / 5`, exact when `5` divides `x`, with `5⁻¹ = 0xCCCCCCCD` modulo `β`. -/
public def divExact5 (x : UInt32Array) : UInt32Array := divExactOdd x 5 0xCCCCCCCD

public theorem toNat_divExact5 (x : UInt32Array) (X : Nat) (hx : toNat x = 5 * X) :
    toNat (divExact5 x) = X :=
  toNat_divExactOdd x 5 0xCCCCCCCD (by decide) (by decide) X hx

/-- `x / 7`, exact when `7` divides `x`, with `7⁻¹ = 0xB6DB6DB7` modulo `β`. -/
public def divExact7 (x : UInt32Array) : UInt32Array := divExactOdd x 7 0xB6DB6DB7

public theorem toNat_divExact7 (x : UInt32Array) (X : Nat) (hx : toNat x = 7 * X) :
    toNat (divExact7 x) = X :=
  toNat_divExactOdd x 7 0xB6DB6DB7 (by decide) (by decide) X hx

/-- `x / 9`, exact when `9` divides `x`, with `9⁻¹ = 0x38E38E39` modulo `β`. -/
public def divExact9 (x : UInt32Array) : UInt32Array := divExactOdd x 9 0x38E38E39

public theorem toNat_divExact9 (x : UInt32Array) (X : Nat) (hx : toNat x = 9 * X) :
    toNat (divExact9 x) = X :=
  toNat_divExactOdd x 9 0x38E38E39 (by decide) (by decide) X hx

/-- `x / 8`, which is exact when `8` divides `x`: `x` shifted right by three bits in place. -/
public def divExact8 (x : UInt32Array) : UInt32Array := shrLimbs x (3 : Nat).toUInt64

public theorem toNat_divExact8 (x : UInt32Array) (X : Nat) (hx : toNat x = 8 * X) :
    toNat (divExact8 x) = X := by
  rw [divExact8, toNat_shrLimbs _ _ (by decide), hx, show (2 : Nat) ^ 3 = 8 by rfl,
    Nat.mul_div_cancel_left _ (by decide)]

/-- `x / 6`, exact when `6` divides `x`: by `2`, then by `3`. -/
public def divExact6 (x : UInt32Array) : UInt32Array := divExact3 (divExact2 x)

public theorem toNat_divExact6 (x : UInt32Array) (X : Nat) (hx : toNat x = 6 * X) :
    toNat (divExact6 x) = X :=
  toNat_divExact3 _ _ (toNat_divExact2 _ _ (by rw [hx]; lia))

/-- `x / (2ˢ d)`, exact when `2ˢ d` divides `x`: a shift by `s < 32` bits, then by the odd `d`. -/
public def divExactShiftOdd (x : UInt32Array) (s : Nat) (d inv : UInt32) : UInt32Array :=
  divExactOdd (shrLimbs x s.toUInt64) d inv

public theorem toNat_divExactShiftOdd (x : UInt32Array) (s : Nat) (hs : s < 32) (d inv : UInt32)
    (hinv : d.toNat * inv.toNat % 2 ^ 32 = 1) (hodd : d.toNat % 2 = 1) (X : Nat)
    (hx : toNat x = 2 ^ s * d.toNat * X) : toNat (divExactShiftOdd x s d inv) = X := by
  apply toNat_divExactOdd _ d inv hinv hodd
  rw [toNat_shrLimbs _ _ hs, hx, Nat.mul_assoc, Nat.mul_div_cancel_left _ (Nat.two_pow_pos s)]

/-- `x / 24`, exact when `24` divides `x`: by `8`, then by `3`. -/
public def divExact24 (x : UInt32Array) : UInt32Array := divExactShiftOdd x 3 3 0xAAAAAAAB

public theorem toNat_divExact24 (x : UInt32Array) (X : Nat) (hx : toNat x = 24 * X) :
    toNat (divExact24 x) = X :=
  toNat_divExactShiftOdd x 3 (by decide) 3 0xAAAAAAAB (by decide) (by decide) X (by rw [hx]; rfl)

/-- `x / 120`, exact when `120` divides `x`: by `8`, then by `15`. -/
public def divExact120 (x : UInt32Array) : UInt32Array := divExactShiftOdd x 3 15 0xEEEEEEEF

public theorem toNat_divExact120 (x : UInt32Array) (X : Nat) (hx : toNat x = 120 * X) :
    toNat (divExact120 x) = X :=
  toNat_divExactShiftOdd x 3 (by decide) 15 0xEEEEEEEF (by decide) (by decide) X (by rw [hx]; rfl)

/-- `x / 720`, exact when `720` divides `x`: by `16`, then by `45`. -/
public def divExact720 (x : UInt32Array) : UInt32Array := divExactShiftOdd x 4 45 0xA4FA4FA5

public theorem toNat_divExact720 (x : UInt32Array) (X : Nat) (hx : toNat x = 720 * X) :
    toNat (divExact720 x) = X :=
  toNat_divExactShiftOdd x 4 (by decide) 45 0xA4FA4FA5 (by decide) (by decide) X (by rw [hx]; rfl)

/-- `x / 5040`, exact when `5040` divides `x`: by `16`, then by `315`. -/
public def divExact5040 (x : UInt32Array) : UInt32Array := divExactShiftOdd x 4 315 0xF2FF2FF3

public theorem toNat_divExact5040 (x : UInt32Array) (X : Nat) (hx : toNat x = 5040 * X) :
    toNat (divExact5040 x) = X :=
  toNat_divExactShiftOdd x 4 (by decide) 315 0xF2FF2FF3 (by decide) (by decide) X
    (by rw [hx]; rfl)

/-- `x / 40320`, exact when `40320` divides `x`: by `128`, then by `315`. -/
public def divExact40320 (x : UInt32Array) : UInt32Array := divExactShiftOdd x 7 315 0xF2FF2FF3

public theorem toNat_divExact40320 (x : UInt32Array) (X : Nat) (hx : toNat x = 40320 * X) :
    toNat (divExact40320 x) = X :=
  toNat_divExactShiftOdd x 7 (by decide) 315 0xF2FF2FF3 (by decide) (by decide) X
    (by rw [hx]; rfl)

end MPN
