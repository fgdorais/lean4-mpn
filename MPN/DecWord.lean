/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import MPN.Trim
public import MPN.MulLimbW
public import MPN.Div.ByLimb

/-!
# The array operations of decimal strings, for limbs of any width

The operations that `DecOps` asks of a width's arrays, on any `WordArray`: `isZeroA` (by `ltA`),
`divRem1A`, the quotient and the remainder by a limb (by `divRem1W` into new limbs), `mod1A`, the
remainder alone (by `mod1W`, which writes no quotient), and `mulAddA`,
`a m + v` (by `mul1W` into new limbs), the arrays trimmed to `k` limbs. Past the sizes of the
fast paths they compute from the values, which never happens.
-/

namespace MPN.WordArray

open LimbArray

variable {A L : Type} [LA : LimbArray A L] [R : WordArray A L] [F : WordFolds A L]

omit F in
/-- Whether `a` is zero, from its top limb down. -/
@[inline, expose] public def isZeroA (a : A) : Bool := !ltA (R.zeros 0) a

omit F in
public theorem isZeroA_iff (a : A) : isZeroA a = true ↔ valAt a 0 (LA.size a) = 0 := by
  rw [isZeroA, Bool.not_eq_true', ← Bool.not_eq_true, ltA_iff, R.size_zeros, valAt_zero]
  lia

variable (A) in
/-- A limb of value `v % 2ʷ`. -/
@[inline, expose] public def limbOf (v : Nat) : L := LA.get (LA.set (R.zeros 1) 0 v) 0

omit F in
public theorem val_limbOf (v : Nat) : LA.val (limbOf A v) = v % 2 ^ LA.w :=
  LA.val_get_set_self _ _ _ (by rw [R.size_zeros]; lia)

omit F in
/-- `a / d` and `a % d`, the quotient trimmed to `k` limbs, by `divRem1W` with the thresholds `t`
and `tu` into new limbs. -/
@[inline, expose] public def divRem1A (k : Nat) (t tu : USize) (a : A) (d : L) : A × L :=
  if h : fitsU (LA.size a) then
    let p := divRem1W A t tu (R.zeros (LA.size a)) 0 a 0 (LA.size a).toUSize
      (zeros_bound' (lt_of_fitsU h)) (full_bound a (lt_of_fitsU h)) d
    (trimTo k p.1, p.2)
  else
    (trimTo k (ofNatW (R := R) (valAt a 0 (LA.size a) / LA.val d)),
      limbOf A (valAt a 0 (LA.size a) % LA.val d))

omit F in
public theorem divRem1A_spec (k : Nat) (t tu : USize) (a : A) (d : L) (hd : 0 < LA.val d) :
    valAt (divRem1A k t tu a d).1 0 (LA.size (divRem1A k t tu a d).1) =
        valAt a 0 (LA.size a) / LA.val d ∧
      LA.val (divRem1A k t tu a d).2 = valAt a 0 (LA.size a) % LA.val d := by
  unfold divRem1A
  split
  · rename_i h
    have hU := lt_of_fitsU h
    have e := toNat_toUSize_of_lt hU
    obtain ⟨d₁, -, d₃, d₄⟩ := divRem1W_spec t tu (R.zeros (LA.size a)) 0 a 0
      (LA.size a).toUSize (zeros_bound' hU) (full_bound a hU) d hd
    simp only [USize.toNat_zero, e] at d₃
    rw [R.size_zeros] at d₁
    dsimp only
    rw [valAt_trimTo, d₁]
    generalize divRem1W A t tu (R.zeros (LA.size a)) 0 a 0 (LA.size a).toUSize
      (zeros_bound' hU) (full_bound a hU) d = q at d₁ d₃ d₄ ⊢
    have hq : valAt a 0 (LA.size a) / LA.val d = valAt q.1 0 (LA.size a) := by
      rw [← d₃, Nat.mul_add_div hd, Nat.div_eq_of_lt d₄, Nat.add_zero]
    have hr : valAt a 0 (LA.size a) % LA.val d = LA.val q.2 := by
      rw [← d₃, Nat.mul_add_mod, Nat.mod_eq_of_lt d₄]
    exact ⟨hq.symm, hr.symm⟩
  · dsimp only
    rw [valAt_trimTo, valAt_ofNatW, val_limbOf, Nat.mod_eq_of_lt]
    · exact ⟨rfl, rfl⟩
    · exact Nat.lt_of_lt_of_le (Nat.mod_lt _ hd) (Nat.le_of_lt (LA.val_lt d))

omit F in
/--
`divRem1A` in place: the quotient written over `a` (`divRem1In`) and trimmed to `k` limbs, which
takes no new array when `a` is held once, as by `chunksLoop` on its own quotients.
-/
@[inline, expose] public def divRem1InA (k : Nat) (t : USize) (a : A) (d : L) : A × L :=
  if h : fitsU (LA.size a) then
    let p := divRem1In A t a 0 (LA.size a).toUSize (full_bound a (lt_of_fitsU h)) d
    (trimTo k p.1, p.2)
  else
    (trimTo k (ofNatW (R := R) (valAt a 0 (LA.size a) / LA.val d)),
      limbOf A (valAt a 0 (LA.size a) % LA.val d))

omit F in
public theorem divRem1InA_spec (k : Nat) (t : USize) (a : A) (d : L) (hd : 0 < LA.val d) :
    valAt (divRem1InA k t a d).1 0 (LA.size (divRem1InA k t a d).1) =
        valAt a 0 (LA.size a) / LA.val d ∧
      LA.val (divRem1InA k t a d).2 = valAt a 0 (LA.size a) % LA.val d := by
  unfold divRem1InA
  split
  · rename_i h
    have hU := lt_of_fitsU h
    have e := toNat_toUSize_of_lt hU
    obtain ⟨d₁, d₃, d₄⟩ := divRem1In_spec t a 0 (LA.size a).toUSize (full_bound a hU) d hd
    simp only [USize.toNat_zero, e] at d₃
    dsimp only
    rw [valAt_trimTo, d₁]
    generalize divRem1In A t a 0 (LA.size a).toUSize (full_bound a hU) d = q at d₁ d₃ d₄ ⊢
    have hq : valAt a 0 (LA.size a) / LA.val d = valAt q.1 0 (LA.size a) := by
      rw [← d₃, Nat.mul_add_div hd, Nat.div_eq_of_lt d₄, Nat.add_zero]
    have hr : valAt a 0 (LA.size a) % LA.val d = LA.val q.2 := by
      rw [← d₃, Nat.mul_add_mod, Nat.mod_eq_of_lt d₄]
    exact ⟨hq.symm, hr.symm⟩
  · dsimp only
    rw [valAt_trimTo, valAt_ofNatW, val_limbOf, Nat.mod_eq_of_lt]
    · exact ⟨rfl, rfl⟩
    · exact Nat.lt_of_lt_of_le (Nat.mod_lt _ hd) (Nat.le_of_lt (LA.val_lt d))

omit F in
/-- `a % d`, by `mod1W` with the thresholds `t` and `tu`, without the quotient. -/
@[inline, expose] public def mod1A (t tu : USize) (a : A) (d : L) : L :=
  if h : fitsU (LA.size a) then
    mod1W A t tu a 0 (LA.size a).toUSize (full_bound a (lt_of_fitsU h)) d
  else limbOf A (valAt a 0 (LA.size a) % LA.val d)

omit F in
public theorem val_mod1A (t tu : USize) (a : A) (d : L) (hd : 0 < LA.val d) :
    LA.val (mod1A t tu a d) = valAt a 0 (LA.size a) % LA.val d := by
  unfold mod1A
  split
  · rename_i h
    rw [mod1W_spec _ _ _ _ _ _ _ hd, USize.toNat_zero, toNat_toUSize_of_lt (lt_of_fitsU h)]
  · rw [val_limbOf, Nat.mod_eq_of_lt]
    exact Nat.lt_of_lt_of_le (Nat.mod_lt _ hd) (Nat.le_of_lt (LA.val_lt d))

/-- `a m + v`, trimmed to `k` limbs, by `mul1W` with the carry in `v`, into new limbs. -/
@[inline, expose] public def mulAddA (k : Nat) (a : A) (m v : L) : A :=
  if h : fitsU (LA.size a + 1) then
    let p := mul1W (R.zeros (LA.size a + 1)) 0 a 0 (LA.size a).toUSize m v
      (by
        have := zeros_bound' (R := R) (lt_of_fitsU h)
        exact ⟨by rw [R.size_zeros, toNat_toUSize_of_lt (by have := lt_of_fitsU h; lia)]; simp,
          by rw [toNat_toUSize_of_lt (by have := lt_of_fitsU h; lia)]; have := lt_of_fitsU h
             simp; lia⟩)
      (full_bound a (by have := lt_of_fitsU h; lia))
    trimTo k (R.uset p.1 (LA.size a).toUSize p.2
      (by rw [(mul1W_spec ..).1, R.size_zeros, toNat_toUSize_of_lt (by have := lt_of_fitsU h; lia)]
          lia))
  else trimTo k (ofNatW (R := R) (valAt a 0 (LA.size a) * LA.val m + LA.val v))

public theorem mulAddA_spec (k : Nat) (a : A) (m v : L) :
    valAt (mulAddA k a m v) 0 (LA.size (mulAddA k a m v)) =
      valAt a 0 (LA.size a) * LA.val m + LA.val v := by
  unfold mulAddA
  split
  · rename_i h
    have hU := lt_of_fitsU h
    have e := toNat_toUSize_of_lt (show LA.size a < USize.size by lia)
    obtain ⟨p₁, p₂, p₃⟩ := mul1W_spec (R.zeros (LA.size a + 1)) 0 a 0 (LA.size a).toUSize m v
      ⟨by rw [R.size_zeros, e]; simp, by rw [e]; simp; lia⟩ (full_bound a (by lia))
    simp only [USize.toNat_zero, e] at p₂ p₃
    simp only [R.size_zeros] at p₁
    dsimp only
    rw [valAt_trimTo]
    simp only [R.size_uset, p₁]
    rw [valAt_add, valAt_one, Nat.zero_add, R.get_uset, e]
    simp only [↓reduceIte]
    rw [valAt_uset_of _ _ _ _ _ _ (.inr (by rw [e]; lia))]
    exact p₃
  · rw [valAt_trimTo, valAt_ofNatW]

omit R F in
/-- The value of limbs that are zero from `u` on is that of their low `u` limbs. -/
public theorem valAt_of_zeros_from (a : A) (u n : Nat) (hn : u ≤ n)
    (hz : ∀ i, u ≤ i → LA.val (LA.get a i) = 0) : valAt a 0 n = valAt a 0 u := by
  obtain ⟨k, rfl⟩ : ∃ k, n = u + k := ⟨n - u, by lia⟩
  rw [valAt_add, valAt_eq_zero k (fun i h _ => hz i (by lia)), Nat.mul_zero, Nat.add_zero]

/--
`a m + v` for limbs `a` that are zero from `u` on, and the limb from which the result is zero: in
place when `u` is below the size of `a`, by one pass over its `u + 1` low limbs, and otherwise by
`mulAddA` into new limbs.
-/
@[inline, expose] public def mulAddInA (k : Nat) (a : A) (u : Nat) (m v : L) : A × Nat :=
  if h : u < LA.size a ∧ fitsU (LA.size a) = true then
    (F.foldThen (u + 1).toUSize (fun _ _ z c => R.mulAdd2 z m R.zero c) a 0
      (by
        have := lt_of_fitsU h.2
        have e : (u + 1).toUSize.toNat = u + 1 := toNat_toUSize_of_lt (by lia)
        exact ⟨by rw [e]; simp; lia, by rw [e]; simp; lia⟩) 0 v fun arr _ _ => arr, u + 1)
  else
    let r := mulAddA k a m v
    (r, LA.size r)

public theorem mulAddInA_spec (k : Nat) (a : A) (u : Nat) (m v : L) (hu : u ≤ LA.size a)
    (hz : ∀ i, u ≤ i → LA.val (LA.get a i) = 0) :
    (mulAddInA k a u m v).2 ≤ LA.size (mulAddInA k a u m v).1 ∧
      (∀ i, (mulAddInA k a u m v).2 ≤ i → LA.val (LA.get (mulAddInA k a u m v).1 i) = 0) ∧
      valAt (mulAddInA k a u m v).1 0 (LA.size (mulAddInA k a u m v).1) =
        valAt a 0 (LA.size a) * LA.val m + LA.val v := by
  unfold mulAddInA
  split
  · rename_i h
    have hU := lt_of_fitsU h.2
    have e : (u + 1).toUSize.toNat = u + 1 := toNat_toUSize_of_lt (by lia)
    have hb : LoopBound a 0 (u + 1).toUSize := ⟨by rw [e]; simp; lia, by rw [e]; simp; lia⟩
    rw [F.foldThen_eq, foldUInPlaceThen]
    dsimp only
    obtain ⟨q, hq⟩ : ∃ q, foldUInPlace (u + 1).toUSize (fun _ _ z c => R.mulAdd2 z m R.zero c) a 0
        hb 0 v = q := ⟨_, rfl⟩
    obtain ⟨i₁, -, i₂, i₃⟩ := foldUInPlace_spec1 (u + 1).toUSize
      (fun _ _ z c => R.mulAdd2 z m R.zero c) a 0 LA.val (fun _ => 0) 1 0 0 (LA.val m) 0
      (fun _ => True) (fun _ _ _ _ _ => trivial)
      (fun j h z c _ => by
        have := R.val_mulAdd2 z m R.zero c
        rw [R.val_zero] at this
        rw [Nat.mul_comm (LA.val m)]
        lia) a 0 hb 0 v trivial
    rw [hq] at i₁ i₂ i₃
    rw [hq]
    simp only [USize.toNat_zero, e, Nat.zero_add, Nat.sub_zero, Nat.one_mul, Nat.zero_mul,
      Nat.add_zero, Nat.mul_zero] at i₁ i₂ i₃
    have hau : valAt a 0 (u + 1) = valAt a 0 u :=
      valAt_of_zeros_from a u (u + 1) (by lia) hz
    have hsz : valAt a 0 (LA.size a) = valAt a 0 u := valAt_of_zeros_from a u _ hu hz
    -- the carry out is zero: the product fits in `u + 1` limbs
    have hlt : valAt a 0 u * LA.val m + LA.val v < 2 ^ (LA.w * (u + 1)) := by
      have h₁ := valAt_lt a 0 u
      have h₂ := LA.val_lt m
      have h₃ := LA.val_lt v
      rw [Nat.mul_succ, Nat.pow_add]
      generalize 2 ^ (LA.w * u) = P at h₁ ⊢
      generalize 2 ^ LA.w = W at h₂ h₃ ⊢
      have : valAt a 0 u * LA.val m ≤ (P - 1) * (W - 1) :=
        Nat.mul_le_mul (by lia) (by lia)
      have : (P - 1) * (W - 1) + (W - 1) = P * (W - 1) := by
        rw [← Nat.succ_mul]; congr 1; lia
      have : P * (W - 1) < P * W := (Nat.mul_lt_mul_left (by lia)).2 (by lia)
      lia
    have hc : LA.val q.2 = 0 := by
      rw [hau] at i₃
      rcases Nat.eq_zero_or_pos (LA.val q.2) with h0 | h0
      · exact h0
      · have : 2 ^ (LA.w * (u + 1)) ≤ 2 ^ (LA.w * (u + 1)) * LA.val q.2 := Nat.le_mul_of_pos_right _ h0
        lia
    have htop : ∀ i, u + 1 ≤ i → LA.val (LA.get q.1 i) = 0 := fun i hi => by
      rw [i₂ i (.inr hi)]; exact hz i (by lia)
    refine ⟨by rw [i₁]; lia, htop, ?_⟩
    rw [valAt_of_zeros_from q.1 (u + 1) _ (by rw [i₁]; lia) htop, hsz]
    rw [hc, Nat.mul_zero, Nat.add_zero, hau, Nat.mul_comm] at i₃
    rw [i₃, Nat.mul_comm]
  · dsimp only
    exact ⟨Nat.le_refl _, fun i hi => R.val_get_ge _ _ hi, mulAddA_spec k a m v⟩

end MPN.WordArray
