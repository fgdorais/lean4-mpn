/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import MPN.Bits

/-!
# Division by a limb

`divRem1 r a d` writes the limbs of `a / d` into `r` and returns `a % d`, like GMP's
`mpn_divrem_1`, from the top limb down: each step divides the remainder so far, followed by the
next limb, by `d`. The remainder stays below `d`, so this two-limb number is below `d β` and its
quotient fits in a limb. For a normalized `d` the steps are `div21`, Möller and Granlund's step
with a precomputed reciprocal, checked; otherwise, or if a check failed, `UInt64.div2`.
-/

open ScalarArray UInt64Array

namespace MPN

private theorem ne_zero_toNat {j : USize} (hj : ¬j = 0) : j.toNat ≠ 0 :=
  fun e => hj (USize.toNat_inj.1 (by rw [e]; rfl))

/--
Divides `c βʲ` plus limbs `0` to `j - 1` of `a` by `d`, from limb `j - 1` down, writing the
quotient limbs into `arr` from limb `rs` on, and returns the remainder.
-/
public def divRem1Loop (arr : UInt64Array) (rs : USize) (a : USlice) (d : UInt64) (j : USize)
    (ha : j ≤ a.size) (hr : LoopBound arr rs j) (c : UInt64) : UInt64Array × UInt64 :=
  if hj : j = 0 then (arr, c)
  else
    have hp := toNat_pred hj
    have hj₀ := ne_zero_toNat hj
    have hlt : j - 1 < a.size := by
      have := USize.le_iff_toNat_le.1 ha
      rw [USize.lt_iff_toNat_lt]; lia
    have hi : (rs + (j - 1)).toNat < arr.size := by
      rw [USize.toNat_add_of_lt (by lia), hp]; lia
    let x := a[j - 1]'hlt
    let q := UInt64.div2 c x d
    divRem1Loop (arr.uset (rs + (j - 1)) q hi) rs a d (j - 1) (USize.le_of_lt hlt)
      ⟨by rw [size_uset, hp]; lia, by rw [hp]; lia⟩ (x - q * d)
termination_by j.toNat
decreasing_by have := toNat_pred hj; have := ne_zero_toNat hj; lia

private theorem divRem1Loop_frame (arr : UInt64Array) (rs : USize) (a : USlice) (d : UInt64)
    (j : USize) (ha : j ≤ a.size) (hr : LoopBound arr rs j) (c : UInt64) :
    (divRem1Loop arr rs a d j ha hr c).1.size = arr.size ∧
      (∀ i, (i < rs.toNat ∨ rs.toNat + j.toNat ≤ i) →
        (divRem1Loop arr rs a d j ha hr c).1[i]! = arr[i]!) := by
  induction arr, j, ha, hr, c using divRem1Loop.induct rs a d with
  | case1 arr ha hr c =>
    rw [divRem1Loop]
    simp
  | case2 arr j ha hr c hj hp hj₀ hlt hi x q ih =>
    rw [divRem1Loop, dite_eq_right hj]
    obtain ⟨i₁, i₂⟩ := ih
    have hidx : (rs + (j - 1)).toNat = rs.toNat + (j.toNat - 1) := by
      rw [USize.toNat_add_of_lt (by lia), hp]
    rw [hp] at i₂
    simp only [size_uset] at i₁
    refine ⟨i₁, fun i hi' => ?_⟩
    rw [i₂ i (by lia), getElem!_uset]
    simp only [hidx]
    split <;> lia

private theorem divRem1Loop_spec (arr : UInt64Array) (rs : USize) (a : USlice) (d : UInt64)
    (j : USize) (ha : j ≤ a.size) (hr : LoopBound arr rs j) (c : UInt64)
    (hc : c.toNat < d.toNat) :
    (divRem1Loop arr rs a d j ha hr c).1.size = arr.size ∧
      (∀ i, (i < rs.toNat ∨ rs.toNat + j.toNat ≤ i) →
        (divRem1Loop arr rs a d j ha hr c).1[i]! = arr[i]!) ∧
      d.toNat * (divRem1Loop arr rs a d j ha hr c).1.valAt rs.toNat j.toNat +
          (divRem1Loop arr rs a d j ha hr c).2.toNat =
        c.toNat * 2 ^ (64 * j.toNat) + a.array.valAt a.start.toNat j.toNat ∧
      (divRem1Loop arr rs a d j ha hr c).2.toNat < d.toNat := by
  induction arr, j, ha, hr, c using divRem1Loop.induct rs a d with
  | case1 arr ha hr c =>
    rw [divRem1Loop]
    simp [hc]
  | case2 arr j ha hr c hj hp hj₀ hlt hi x q ih =>
    rw [divRem1Loop, dite_eq_right hj]
    dsimp only
    obtain ⟨hrem, hdq⟩ := UInt64.toNat_div2_rem c x d hc
    have hrem' : (x - q * d).toNat < d.toNat := by
      rw [hrem]; exact Nat.mod_lt _ (by lia)
    obtain ⟨i₁, i₂, i₃, i₄⟩ := ih hrem'
    have hidx : (rs + (j - 1)).toNat = rs.toNat + (j.toNat - 1) := by
      rw [USize.toNat_add_of_lt (by lia), hp]
    rw [hp] at i₂ i₃
    simp only [size_uset] at i₁
    have hout := i₂ (rs.toNat + (j.toNat - 1)) (.inr (Nat.le_refl _))
    rw [getElem!_uset, hidx] at hout
    simp only [↓reduceIte] at hout
    have hlo : (arr.uset (rs + (j - 1)) q hi).valAt rs.toNat (j.toNat - 1) =
        arr.valAt rs.toNat (j.toNat - 1) := valAt_uset_of _ _ _ _ _ _ (by rw [hidx]; lia)
    refine ⟨i₁, fun i hi' => ?_, ?_, i₄⟩
    · rw [i₂ i (by lia), getElem!_uset]
      simp only [hidx]
      split <;> lia
    · have e : j.toNat = (j.toNat - 1) + 1 := by lia
      have hx : x = a.array[a.start.toNat + (j.toNat - 1)]! := by
        show a[j - 1]'hlt = _
        rw [USlice.getElem_eq_getElem!, hp]
      rw [e, UInt64Array.valAt_add, UInt64Array.valAt_add, valAt_one, valAt_one, hout, ← hx,
        show 64 * (j.toNat - 1 + 1) = 64 * (j.toNat - 1) + 64 by lia, Nat.pow_add]
      simp only [q] at i₃ hdq ⊢
      generalize (divRem1Loop _ _ _ _ _ _ _ _).1.valAt _ _ = V at *
      generalize (divRem1Loop _ _ _ _ _ _ _ _).2.toNat = r at *
      generalize (x - UInt64.div2 c x d * d).toNat = r₁ at *
      generalize (UInt64.div2 c x d).toNat = q₁ at *
      generalize a.array.valAt _ (j.toNat - 1) = A at *
      generalize 2 ^ (64 * (j.toNat - 1)) = P at *
      grind

/-! ## A step with a precomputed reciprocal

For a normalized `d`, with its top bit set, GMP divides without the hardware divider, by Möller and
Granlund's 2-by-1 step (`udiv_qr_2by1`): with the reciprocal `v = ⌊(β² - 1) / d⌋ - β`, one double
product and two corrections give the quotient limb and the remainder. `div21` checks its result
exactly, `q d + r = R β + x` with `r < d`, by one more double product off the dependency chain, so
that neither the reciprocal nor the error bound of the step needs a proof. A failed check gives
the remainder `d`, which makes every later check fail too, so that the loop checks the last
remainder once and divides again with `UInt64.div2` if it is not below `d`, which never happens.
-/

/-- The reciprocal `⌊(β² - 1) / d⌋ - β` of a normalized `d`. -/
@[inline] public def recip21 (d : UInt64) : UInt64 := UInt64.div2 (~~~d) 0xFFFFFFFFFFFFFFFF d

/-- Whether `q d + r = R β + x` and `r < d`, exactly. -/
@[inline, expose] public def div21Ok (d R x q r : UInt64) : Bool :=
  UInt64.addh (UInt64.mulh q d) (q * d) r == R && q * d + r == x && r < d

/-- `(q, r)` when `div21Ok` holds, and the remainder `d` otherwise, without a branch. -/
@[inline, expose] public def div21Sel (d R x q r : UInt64) : UInt64 × UInt64 :=
  let ok := (div21Ok d R x q r).toUInt64
  (q * ok, r * ok + d * (1 - ok))

/--
One step of division by `d` with the reciprocal `v`: the quotient limb and remainder of `R β + x`
by `d`, for `R < d`, by Möller and Granlund's 2-by-1 step with its corrections as arithmetic, and
checked. A remainder of `d` or more means that the check failed, there or in an earlier step.
-/
@[inline, expose] public def div21 (v d R x : UInt64) : UInt64 × UInt64 :=
  let p := v * R
  let q₀ := p + x
  let q₁ := UInt64.addh (UInt64.mulh v R + R) p x + 1
  let r := x - q₁ * d
  let adj := (decide (q₀ < r)).toUInt64
  let q₂ := q₁ - adj
  let r₂ := r + (d &&& ((0 : UInt64) - adj))
  let fix := (decide (d ≤ r₂)).toUInt64
  div21Sel d R x (q₂ + fix) (r₂ - (d &&& ((0 : UInt64) - fix)))

private theorem div21Ok_spec (d R x q r : UInt64) (h : div21Ok d R x q r = true) :
    q.toNat * d.toNat + r.toNat = R.toNat * 2 ^ 64 + x.toNat ∧ r.toNat < d.toNat := by
  simp only [div21Ok, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
  obtain ⟨⟨h₁, h₂⟩, h₃⟩ := h
  refine ⟨?_, UInt64.lt_iff_toNat_lt.1 h₃⟩
  have e₁ := congrArg UInt64.toNat h₁
  have e₂ := congrArg UInt64.toNat h₂
  rw [UInt64.toNat_addh, UInt64.toNat_mulh, UInt64.toNat_mul] at e₁
  rw [UInt64.toNat_add, UInt64.toNat_mul] at e₂
  have hq := q.toNat_lt; have hd := d.toNat_lt; have hr := r.toNat_lt
  have hP := Nat.div_add_mod (q.toNat * d.toNat) (2 ^ 64)
  have hP' : q.toNat * d.toNat / 2 ^ 64 + 1 < 2 ^ 64 := by
    have := Nat.mul_le_mul (Nat.le_pred_of_lt hq) (Nat.le_pred_of_lt hd)
    have : q.toNat * d.toNat / 2 ^ 64 ≤ 2 ^ 64 - 2 := by
      rw [Nat.div_le_iff_le_mul_add_pred (by decide)]; simp at this ⊢; lia
    lia
  generalize q.toNat * d.toNat = P at *
  generalize R.toNat = Rn at *
  generalize x.toNat = xn at *
  generalize r.toNat = rn at *
  have hc : (P % 2 ^ 64 + rn) / 2 ^ 64 ≤ 1 := by
    rw [Nat.div_le_iff_le_mul_add_pred (by decide)]
    have := Nat.mod_lt P (show 0 < 2 ^ 64 by decide); lia
  rw [Nat.mod_eq_of_lt (by lia)] at e₁
  have hm := Nat.div_add_mod (P % 2 ^ 64 + rn) (2 ^ 64)
  rw [e₂] at hm
  generalize P / 2 ^ 64 = A at *
  generalize P % 2 ^ 64 = B at *
  generalize (B + rn) / 2 ^ 64 = C at *
  lia

/-- A selection with a remainder below `d` passed its check. -/
private theorem div21Sel_spec (d R x q r : UInt64) (h : (div21Sel d R x q r).2.toNat < d.toNat) :
    div21Ok d R x q r = true ∧ div21Sel d R x q r = (q, r) := by
  have h₀ : false.toUInt64 = 0 := rfl
  have h₁ : true.toUInt64 = 1 := rfl
  cases hok : div21Ok d R x q r
  · simp [div21Sel, hok, h₀] at h
  · simp [div21Sel, hok, h₁]

/-- A step that leaves a remainder below `d` divided `R β + x` by `d`, from `R < d`. -/
public theorem div21_spec (v d R x : UInt64) (h : (div21 v d R x).2.toNat < d.toNat) :
    R.toNat < d.toNat ∧
      d.toNat * (div21 v d R x).1.toNat + (div21 v d R x).2.toNat =
        R.toNat * 2 ^ 64 + x.toNat := by
  obtain ⟨q, r, e⟩ : ∃ q r, div21 v d R x = div21Sel d R x q r := ⟨_, _, rfl⟩
  rw [e] at h ⊢
  obtain ⟨hok, e⟩ := div21Sel_spec d R x q r h
  obtain ⟨h₁, h₂⟩ := div21Ok_spec d R x q r hok
  rw [e]
  refine ⟨?_, by dsimp only; rw [Nat.mul_comm]; exact h₁⟩
  have hq := q.toNat_lt; have hx := x.toNat_lt
  have : (q.toNat + 1) * d.toNat ≤ 2 ^ 64 * d.toNat := Nat.mul_le_mul_right _ hq
  refine Nat.lt_of_not_le fun hle => ?_
  have := Nat.mul_le_mul_right (2 ^ 64) hle
  rw [Nat.add_mul, Nat.one_mul] at *
  lia

/--
`divRem1Loop` with `div21` and the reciprocal `v` of a normalized `d`: a remainder of `d` or more
at the end means that a check failed.
-/
public def divRem1LoopR (arr : UInt64Array) (rs : USize) (a : USlice) (d v : UInt64) (j : USize)
    (ha : j ≤ a.size) (hr : LoopBound arr rs j) (c : UInt64) : UInt64Array × UInt64 :=
  if hj : j = 0 then (arr, c)
  else
    have hp := toNat_pred hj
    have hj₀ := ne_zero_toNat hj
    have hlt : j - 1 < a.size := by
      have := USize.le_iff_toNat_le.1 ha
      rw [USize.lt_iff_toNat_lt]; lia
    have hi : (rs + (j - 1)).toNat < arr.size := by
      rw [USize.toNat_add_of_lt (by lia), hp]; lia
    let p := div21 v d c (a[j - 1]'hlt)
    divRem1LoopR (arr.uset (rs + (j - 1)) p.1 hi) rs a d v (j - 1) (USize.le_of_lt hlt)
      ⟨by rw [size_uset, hp]; lia, by rw [hp]; lia⟩ p.2
termination_by j.toNat
decreasing_by have := toNat_pred hj; have := ne_zero_toNat hj; lia

private theorem divRem1LoopR_frame (arr : UInt64Array) (rs : USize) (a : USlice) (d v : UInt64)
    (j : USize) (ha : j ≤ a.size) (hr : LoopBound arr rs j) (c : UInt64) :
    (divRem1LoopR arr rs a d v j ha hr c).1.size = arr.size ∧
      (∀ i, (i < rs.toNat ∨ rs.toNat + j.toNat ≤ i) →
        (divRem1LoopR arr rs a d v j ha hr c).1[i]! = arr[i]!) := by
  induction arr, j, ha, hr, c using divRem1LoopR.induct rs a d v with
  | case1 arr ha hr c =>
    rw [divRem1LoopR]
    simp
  | case2 arr j ha hr c hj hp hj₀ hlt hi p ih =>
    rw [divRem1LoopR, dite_eq_right hj]
    obtain ⟨i₁, i₂⟩ := ih
    have hidx : (rs + (j - 1)).toNat = rs.toNat + (j.toNat - 1) := by
      rw [USize.toNat_add_of_lt (by lia), hp]
    rw [hp] at i₂
    simp only [size_uset] at i₁
    refine ⟨i₁, fun i hi' => ?_⟩
    rw [i₂ i (by lia), getElem!_uset]
    simp only [hidx]
    split <;> lia

/-- A final remainder below `d` means that every step passed its check. -/
private theorem divRem1LoopR_spec (arr : UInt64Array) (rs : USize) (a : USlice) (d v : UInt64)
    (j : USize) (ha : j ≤ a.size) (hr : LoopBound arr rs j) (c : UInt64)
    (hc : (divRem1LoopR arr rs a d v j ha hr c).2.toNat < d.toNat) :
    c.toNat < d.toNat ∧
      (∀ i, (i < rs.toNat ∨ rs.toNat + j.toNat ≤ i) →
        (divRem1LoopR arr rs a d v j ha hr c).1[i]! = arr[i]!) ∧
      d.toNat * (divRem1LoopR arr rs a d v j ha hr c).1.valAt rs.toNat j.toNat +
          (divRem1LoopR arr rs a d v j ha hr c).2.toNat =
        c.toNat * 2 ^ (64 * j.toNat) + a.array.valAt a.start.toNat j.toNat := by
  induction arr, j, ha, hr, c using divRem1LoopR.induct rs a d v with
  | case1 arr c ha hr =>
    rw [divRem1LoopR, dite_eq_left rfl] at hc ⊢
    simp only at hc
    simp [hc]
  | case2 arr j ha hr c hj hp hj₀ hlt hi p ih =>
    rw [divRem1LoopR, dite_eq_right hj] at hc ⊢
    dsimp only at hc ⊢
    obtain ⟨hp₂, i₂, i₃⟩ := ih hc
    obtain ⟨hcd, hstep⟩ := div21_spec v d c _ hp₂
    have hidx : (rs + (j - 1)).toNat = rs.toNat + (j.toNat - 1) := by
      rw [USize.toNat_add_of_lt (by lia), hp]
    rw [hp] at i₂ i₃
    have hout := i₂ (rs.toNat + (j.toNat - 1)) (.inr (Nat.le_refl _))
    rw [getElem!_uset, hidx] at hout
    simp only [↓reduceIte] at hout
    refine ⟨hcd, fun i hi' => ?_, ?_⟩
    · rw [i₂ i (by lia), getElem!_uset]
      simp only [hidx]
      split <;> lia
    · have e : j.toNat = (j.toNat - 1) + 1 := by lia
      have hx : a[j - 1]'hlt = a.array[a.start.toNat + (j.toNat - 1)]! := by
        rw [USlice.getElem_eq_getElem!, hp]
      rw [e, UInt64Array.valAt_add, UInt64Array.valAt_add, valAt_one, valAt_one, hout, ← hx,
        show 64 * (j.toNat - 1 + 1) = 64 * (j.toNat - 1) + 64 by lia, Nat.pow_add]
      simp only [p] at i₃ hstep ⊢
      generalize (divRem1LoopR _ _ _ _ _ _ _ _ _).1.valAt _ _ = V at *
      generalize (divRem1LoopR _ _ _ _ _ _ _ _ _).2.toNat = r at *
      generalize (div21 v d c (a[j - 1]'hlt)).2.toNat = r₁ at *
      generalize (div21 v d c (a[j - 1]'hlt)).1.toNat = q₁ at *
      generalize a.array.valAt _ (j.toNat - 1) = A at *
      generalize 2 ^ (64 * (j.toNat - 1)) = P at *
      grind

/-- `divRem1Loop` on all of `r` and `a`, from a remainder of `0`. -/
@[inline] def divRem1Slow (r a : USlice) (d : UInt64) : UInt64Array × UInt64 :=
  divRem1Loop r.array r.start a d (min a.size r.size) (USize.min_le_left ..)
    (r.loopBound (USize.min_le_right ..)) 0

/--
`divRem1` with `v` for the reciprocal `recip21 d` of a normalized `d`, for a divisor whose
reciprocal is known. Any `v` gives the right result: if a check fails, it divides again with
`UInt64.div2`.
-/
public def divRem1R (r a : USlice) (d v : UInt64) : UInt64Array × UInt64 :=
  let p := divRem1LoopR r.array r.start a d v (min a.size r.size) (USize.min_le_left ..)
    (r.loopBound (USize.min_le_right ..)) 0
  if p.2 < d then p else divRem1Slow r a d

/--
Writes the limbs of `a / d` into `r` and returns `a % d`, on the first `min r.size a.size` limbs,
like GMP's `mpn_divrem_1`. It requires `0 < d`. From 12 limbs and for a normalized `d` it takes
the steps with the reciprocal (`divRem1R`), which then pays for its division.
-/
public def divRem1 (r a : USlice) (d : UInt64) : UInt64Array × UInt64 :=
  if d >>> 63 = 1 ∧ 12 ≤ min a.size r.size then divRem1R r a d (recip21 d) else divRem1Slow r a d

private theorem divRem1Slow_frame (r a : USlice) (d : UInt64) :
    (divRem1Slow r a d).1.size = r.array.size ∧
      ∀ i, (i < r.start.toNat ∨ r.start.toNat + min a.size.toNat r.size.toNat ≤ i) →
        (divRem1Slow r a d).1[i]! = r.array[i]! :=
  ⟨(divRem1Loop_frame ..).1,
    fun i hi => (divRem1Loop_frame ..).2 i (by rw [USize.toNat_min]; exact hi)⟩

private theorem divRem1R_frame (r a : USlice) (d v : UInt64) :
    (divRem1R r a d v).1.size = r.array.size ∧
      ∀ i, (i < r.start.toNat ∨ r.start.toNat + min a.size.toNat r.size.toNat ≤ i) →
        (divRem1R r a d v).1[i]! = r.array[i]! := by
  rw [divRem1R]
  split
  · exact ⟨(divRem1LoopR_frame ..).1,
      fun i hi => (divRem1LoopR_frame ..).2 i (by rw [USize.toNat_min]; exact hi)⟩
  · exact divRem1Slow_frame r a d

private theorem divRem1_frame (r a : USlice) (d : UInt64) :
    (divRem1 r a d).1.size = r.array.size ∧
      ∀ i, (i < r.start.toNat ∨ r.start.toNat + min a.size.toNat r.size.toNat ≤ i) →
        (divRem1 r a d).1[i]! = r.array[i]! := by
  rw [divRem1]; split
  · exact divRem1R_frame ..
  · exact divRem1Slow_frame ..

/-- The value of the quotient and the remainder, when `r` holds all of `a`. -/
private def DivRem1Full (r a : USlice) (d : UInt64) (p : UInt64Array × UInt64) : Prop :=
  d.toNat * p.1.valAt r.start.toNat a.size.toNat + p.2.toNat = a.toNat ∧ p.2.toNat < d.toNat

private theorem divRem1Slow_full (r a : USlice) (d : UInt64) (hd : 0 < d.toNat)
    (har : a.size ≤ r.size) : DivRem1Full r a d (divRem1Slow r a d) := by
  have h := USize.le_iff_toNat_le.1 har
  obtain ⟨-, -, i₃, i₄⟩ := divRem1Loop_spec r.array r.start a d _ (USize.min_le_left ..)
    (r.loopBound (USize.min_le_right ..)) 0 (by rw [UInt64.toNat_zero]; exact hd)
  simp only [USize.toNat_min, show min a.size.toNat r.size.toNat = a.size.toNat by lia,
    UInt64.toNat_zero, Nat.zero_mul, Nat.zero_add] at i₃
  exact ⟨by rw [USlice.toNat_eq_valAt]; exact i₃, i₄⟩

private theorem divRem1R_full (r a : USlice) (d v : UInt64) (hd : 0 < d.toNat)
    (har : a.size ≤ r.size) : DivRem1Full r a d (divRem1R r a d v) := by
  have h := USize.le_iff_toNat_le.1 har
  rw [divRem1R]
  split
  · rename_i hlt
    have hlt' := UInt64.lt_iff_toNat_lt.1 hlt
    obtain ⟨-, -, i₃⟩ := divRem1LoopR_spec r.array r.start a d _ _ (USize.min_le_left ..)
      (r.loopBound (USize.min_le_right ..)) 0 hlt'
    simp only [USize.toNat_min, show min a.size.toNat r.size.toNat = a.size.toNat by lia,
      UInt64.toNat_zero, Nat.zero_mul, Nat.zero_add] at i₃
    exact ⟨by rw [USlice.toNat_eq_valAt]; exact i₃, hlt'⟩
  · exact divRem1Slow_full r a d hd har

private theorem divRem1_full (r a : USlice) (d : UInt64) (hd : 0 < d.toNat)
    (har : a.size ≤ r.size) : DivRem1Full r a d (divRem1 r a d) := by
  rw [divRem1]; split
  · exact divRem1R_full r a d _ hd har
  · exact divRem1Slow_full r a d hd har

@[simp] public theorem size_divRem1 (r a : USlice) (d : UInt64) :
    (divRem1 r a d).1.size = r.array.size := (divRem1_frame ..).1

/-- `divRem1` leaves the limbs of `r` outside the ones it writes unchanged. -/
public theorem getElem!_divRem1 (r a : USlice) (d : UInt64) (i : Nat)
    (hi : i < r.start.toNat ∨ r.start.toNat + min a.size.toNat r.size.toNat ≤ i) :
    (divRem1 r a d).1[i]! = r.array[i]! := (divRem1_frame ..).2 i hi

public theorem valAt_divRem1 (r a : USlice) (d : UInt64) (hd : 0 < d.toNat)
    (har : a.size ≤ r.size) :
    (divRem1 r a d).1.valAt r.start.toNat a.size.toNat = a.toNat / d.toNat := by
  obtain ⟨h₁, h₂⟩ := divRem1_full r a d hd har
  rw [← h₁, Nat.mul_add_div hd, Nat.div_eq_of_lt h₂, Nat.add_zero]

/-- The remainder of `divRem1` is `a % d`. -/
public theorem toNat_divRem1_snd (r a : USlice) (d : UInt64) (hd : 0 < d.toNat)
    (har : a.size ≤ r.size) :
    (divRem1 r a d).2.toNat = a.toNat % d.toNat := by
  obtain ⟨h₁, h₂⟩ := divRem1_full r a d hd har
  rw [← h₁, Nat.mul_add_mod, Nat.mod_eq_of_lt h₂]

@[simp] public theorem size_divRem1R (r a : USlice) (d v : UInt64) :
    (divRem1R r a d v).1.size = r.array.size := (divRem1R_frame ..).1

/-- `divRem1R` leaves the limbs of `r` outside the ones it writes unchanged. -/
public theorem getElem!_divRem1R (r a : USlice) (d v : UInt64) (i : Nat)
    (hi : i < r.start.toNat ∨ r.start.toNat + min a.size.toNat r.size.toNat ≤ i) :
    (divRem1R r a d v).1[i]! = r.array[i]! := (divRem1R_frame ..).2 i hi

public theorem valAt_divRem1R (r a : USlice) (d v : UInt64) (hd : 0 < d.toNat)
    (har : a.size ≤ r.size) :
    (divRem1R r a d v).1.valAt r.start.toNat a.size.toNat = a.toNat / d.toNat := by
  obtain ⟨h₁, h₂⟩ := divRem1R_full r a d v hd har
  rw [← h₁, Nat.mul_add_div hd, Nat.div_eq_of_lt h₂, Nat.add_zero]

/-- The remainder of `divRem1R` is `a % d`. -/
public theorem toNat_divRem1R_snd (r a : USlice) (d v : UInt64) (hd : 0 < d.toNat)
    (har : a.size ≤ r.size) :
    (divRem1R r a d v).2.toNat = a.toNat % d.toNat := by
  obtain ⟨h₁, h₂⟩ := divRem1R_full r a d v hd har
  rw [← h₁, Nat.mul_add_mod, Nat.mod_eq_of_lt h₂]

end MPN
