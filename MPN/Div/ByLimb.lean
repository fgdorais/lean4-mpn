/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import MPN.Bitwise

/-!
# Division by a limb, for limbs of any width

`divRem1W` writes the limbs of `a / d` into a window of `r` and returns `a % d`, like GMP's
`mpn_divrem_1`, from the top limb down (`divLoop`): each step divides the remainder so far,
followed by the next limb, by `d`. The remainder stays below `d`, so this two-limb number is below
`d β` and its quotient fits in a limb.

The step is `div2` (`divStep`), or for a normalized `d`, with its top bit set, Möller and
Granlund's 2-by-1 step with the precomputed reciprocal `⌊(β² - 1) / d⌋ - β` (`div21`, GMP's
`udiv_qr_2by1`), whose one double product and two corrections cost less than a hardware divider.
`div21` checks its result exactly, `q d + r = c β + x` with `r < d`, by one more double product
off the dependency chain, so that neither the reciprocal nor the error bound of the step needs a
proof. A failed check gives the remainder `d`, which makes every later check fail too, so that the
division checks the last remainder once and divides again with `div2` if it is not below `d`, which
never happens.
-/

namespace MPN.WordArray

variable {A L : Type} [LA : LimbArray A L] [R : WordArray A L]

/-! ## The steps -/

variable (A) in
/-- The quotient limb and remainder of `c β + x` by `d`, for `c < d`, by `div2`. -/
@[inline, expose] public def divStep (d c x : L) : L × L :=
  let q := R.div2 c x d
  (q, R.sub x (R.mul q d))

public theorem divStep_spec (d c x : L) (h : LA.val c < LA.val d) :
    LA.val (divStep A d c x).2 < LA.val d ∧
      LA.val d * LA.val (divStep A d c x).1 + LA.val (divStep A d c x).2 =
        LA.val c * 2 ^ LA.w + LA.val x := by
  obtain ⟨h₁, h₂⟩ := div2_rem (R := R) c x d h
  exact ⟨by rw [divStep, h₁]; exact Nat.mod_lt _ (by lia), h₂⟩

variable (A) in
/-- Whether `q d + r = c β + x` and `r < d`, exactly. -/
@[inline, expose] public def div21Ok (d c x q r : L) : Bool :=
  R.eqB (R.addh (R.mulh q d) (R.mul q d) r) c && R.eqB (R.add (R.mul q d) r) x && R.ltB r d

variable (A) in
/-- `(q, r)` when `div21Ok` holds, and the remainder `d` otherwise, without a branch. -/
@[inline, expose] public def div21Sel (d c x q r : L) : L × L :=
  let ok := R.ofBool (div21Ok A d c x q r)
  (R.mul q ok, R.add (R.mul r ok) (R.mul d (R.sub R.one ok)))

variable (A) in
/--
One step of division by `d` with the reciprocal `v`: the quotient limb and remainder of `c β + x`
by `d`, for `c < d`, by Möller and Granlund's 2-by-1 step with its corrections as arithmetic, and
checked. A remainder of `d` or more means that the check failed, there or in an earlier step.
-/
@[inline, expose] public def div21 (v d c x : L) : L × L :=
  let p := R.mul v c
  let q₀ := R.add p x
  let q₁ := R.add (R.addh (R.add (R.mulh v c) c) p x) R.one
  let r := R.sub x (R.mul q₁ d)
  let adj := R.ofBool (R.ltB q₀ r)
  let q₂ := R.sub q₁ adj
  let r₂ := R.add r (R.land d (R.sub R.zero adj))
  let fix := R.ofBool (!R.ltB r₂ d)
  div21Sel A d c x (R.add q₂ fix) (R.sub r₂ (R.land d (R.sub R.zero fix)))

variable (A) in
/-- The reciprocal `⌊(β² - 1) / d⌋ - β` of a normalized `d`. -/
@[inline, expose] public def recip21 (d : L) : L :=
  R.div2 (R.sub (R.sub R.zero R.one) d) (R.sub R.zero R.one) d

variable (A) in
/-- Whether the top bit of `d` is set. -/
@[inline, expose] public def isNorm (d : L) : Bool :=
  !R.ltB d (R.shl R.one (R.ofUSize (R.wU - 1)))

private theorem div21Ok_spec (d c x q r : L) (h : div21Ok A d c x q r = true) :
    LA.val q * LA.val d + LA.val r = LA.val c * 2 ^ LA.w + LA.val x ∧ LA.val r < LA.val d := by
  simp only [div21Ok, Bool.and_eq_true, R.eqB_iff, R.ltB_iff] at h
  obtain ⟨⟨e₁, e₂⟩, h₃⟩ := h
  refine ⟨?_, h₃⟩
  rw [R.val_addh, R.val_mulh, R.val_mul] at e₁
  rw [R.val_add, R.val_mul] at e₂
  have hq := LA.val_lt q; have hd := LA.val_lt d; have hr := LA.val_lt r
  have hB := four_le (R := R)
  have hP := Nat.div_add_mod (LA.val q * LA.val d) (2 ^ LA.w)
  have hP' : LA.val q * LA.val d / 2 ^ LA.w + 1 < 2 ^ LA.w := by
    have := Nat.mul_le_mul (Nat.le_pred_of_lt hq) (Nat.le_pred_of_lt hd)
    have : LA.val q * LA.val d / 2 ^ LA.w ≤ 2 ^ LA.w - 2 := by
      rw [Nat.div_le_iff_le_mul_add_pred (by lia)]
      have e : (2 ^ LA.w).pred * (2 ^ LA.w).pred = (2 ^ LA.w - 2) * 2 ^ LA.w + 1 := by
        simp only [Nat.pred_eq_sub_one]
        generalize 2 ^ LA.w = B at *
        obtain ⟨k, rfl⟩ : ∃ k, B = k + 2 := ⟨B - 2, by lia⟩
        simp only [Nat.add_sub_cancel]
        grind
      simp only [Nat.pred_eq_sub_one] at e this ⊢
      lia
    lia
  generalize LA.val q * LA.val d = P at *
  generalize LA.val c = Cn at *
  generalize LA.val x = xn at *
  generalize LA.val r = rn at *
  generalize 2 ^ LA.w = B at *
  have hc : (P % B + rn) / B ≤ 1 := carry_le (by have := Nat.mod_lt P (show 0 < B by lia); lia)
  rw [Nat.mod_eq_of_lt (by lia)] at e₁
  have hm := Nat.div_add_mod (P % B + rn) B
  rw [e₂] at hm
  generalize P / B = A' at *
  generalize P % B = B' at *
  generalize (B' + rn) / B = C at *
  subst e₁
  grind

/-- A selection with a remainder below `d` passed its check. -/
private theorem div21Sel_spec (d c x q r : L) (h : LA.val (div21Sel A d c x q r).2 < LA.val d) :
    div21Ok A d c x q r = true ∧ LA.val (div21Sel A d c x q r).1 = LA.val q ∧
      LA.val (div21Sel A d c x q r).2 = LA.val r := by
  have hB := four_le (R := R)
  have hq := LA.val_lt q; have hr := LA.val_lt r; have hd := LA.val_lt d
  cases hok : div21Ok A d c x q r
  · exfalso
    simp only [div21Sel, hok, R.val_add, R.val_mul, R.val_sub, R.val_ofBool, R.val_one,
      Bool.false_eq_true, ↓reduceIte, Nat.mul_zero, Nat.zero_mod, Nat.zero_add, Nat.sub_zero] at h
    rw [Nat.add_mod_right, Nat.mod_eq_of_lt (show 1 < 2 ^ LA.w by lia), Nat.mul_one,
      Nat.mod_eq_of_lt hd,
      Nat.mod_eq_of_lt hd] at h
    lia
  · refine ⟨rfl, ?_, ?_⟩
    · simp only [div21Sel, hok, R.val_mul, R.val_ofBool, ↓reduceIte, Nat.mul_one,
        Nat.mod_eq_of_lt hq]
    · simp only [div21Sel, hok, R.val_add, R.val_mul, R.val_sub, R.val_ofBool, R.val_one,
        ↓reduceIte, Nat.mul_one, Nat.mod_eq_of_lt hr]
      rw [Nat.add_sub_cancel' (by lia), Nat.mod_self, Nat.mul_zero, Nat.zero_mod, Nat.add_zero,
        Nat.mod_eq_of_lt hr]

/-- A step that leaves a remainder below `d` divided `c β + x` by `d`, from `c < d`. -/
public theorem div21_spec (v d c x : L) (h : LA.val (div21 A v d c x).2 < LA.val d) :
    LA.val c < LA.val d ∧
      LA.val d * LA.val (div21 A v d c x).1 + LA.val (div21 A v d c x).2 =
        LA.val c * 2 ^ LA.w + LA.val x := by
  obtain ⟨q, r, e⟩ : ∃ q r, div21 A v d c x = div21Sel A d c x q r := ⟨_, _, rfl⟩
  rw [e] at h ⊢
  obtain ⟨hok, e₁, e₂⟩ := div21Sel_spec d c x q r h
  obtain ⟨h₁, h₂⟩ := div21Ok_spec d c x q r hok
  rw [e₁, e₂]
  refine ⟨?_, by rw [Nat.mul_comm]; exact h₁⟩
  have hq := LA.val_lt q; have hx := LA.val_lt x
  have : (LA.val q + 1) * LA.val d ≤ 2 ^ LA.w * LA.val d := Nat.mul_le_mul_right _ hq
  refine Nat.lt_of_not_le fun hle => ?_
  have := Nat.mul_le_mul_right (2 ^ LA.w) hle
  rw [Nat.add_mul, Nat.one_mul] at *
  lia

/-! ## The loop -/

variable (A) in
/--
Divides `c βʲ` plus limbs `ao` to `ao + j - 1` of `a` by the steps `step`, from limb `ao + j - 1`
down, writing the quotient limbs into limbs `ro` to `ro + j - 1` of `r`, and returns the
remainder.
-/
@[expose, specialize]
public def divLoop (step : L → L → L × L) (r : A) (ro : USize) (a : A) (ao j : USize)
    (hr : LoopBound r ro j) (ha : LoopBound a ao j) (c : L) : A × L :=
  if hj : j = 0 then (r, c)
  else
    have hm := pos_of_ne hj
    let p := step c (R.uget a (ao + (j - 1)) (ha.uset_bound (pred_lt' hm)))
    divLoop step (R.uset r (ro + (j - 1)) p.1 (hr.uset_bound (pred_lt' hm))) ro a ao (j - 1)
      ((bound_pred hr hm).of_uset ..) (bound_pred ha hm) p.2
termination_by j.toNat
decreasing_by
  have := toNat_pred' (pos_of_ne hj)
  have := USize.lt_iff_toNat_lt.1 (pos_of_ne hj)
  lia

public theorem divLoop_frame (step : L → L → L × L) (r : A) (ro : USize) (a : A) (ao j : USize)
    (hr : LoopBound r ro j) (ha : LoopBound a ao j) (c : L) :
    LA.size (divLoop A step r ro a ao j hr ha c).1 = LA.size r ∧
      ∀ i, (i < ro.toNat ∨ ro.toNat + j.toNat ≤ i) →
        LA.get (divLoop A step r ro a ao j hr ha c).1 i = LA.get r i := by
  induction r, j, hr, ha, c using divLoop.induct A (R := R) step ro a ao with
  | case1 r hr ha c => rw [divLoop, dite_eq_left rfl]; exact ⟨rfl, fun _ _ => rfl⟩
  | case2 r j hr ha c hj hm p ih =>
    rw [divLoop, dite_eq_right hj]
    obtain ⟨i₁, i₂⟩ := ih
    refine ⟨by rw [i₁, R.size_uset], fun i hi => ?_⟩
    have hp := toNat_pred' hm
    have := USize.lt_iff_toNat_lt.1 hm
    rw [i₂ i (by rw [hp]; lia), R.get_uset,
      ite_eq_right (by rw [hr.toNat_add (pred_lt' hm), hp]; lia)]

/-- Under steps that keep a failure, a remainder below `d` at the end means one at the start. -/
public theorem divLoop_mono (step : L → L → L × L) (d : L)
    (hm : ∀ c x, LA.val (step c x).2 < LA.val d → LA.val c < LA.val d) (r : A) (ro : USize)
    (a : A) (ao j : USize) (hr : LoopBound r ro j) (ha : LoopBound a ao j) (c : L)
    (hf : LA.val (divLoop A step r ro a ao j hr ha c).2 < LA.val d) : LA.val c < LA.val d := by
  induction r, j, hr, ha, c using divLoop.induct A (R := R) step ro a ao with
  | case1 r hr ha c => rw [divLoop, dite_eq_left rfl] at hf; exact hf
  | case2 r j hr ha c hj hm' p ih =>
    rw [divLoop, dite_eq_right hj] at hf
    exact hm _ _ (ih hf)

/-- Under steps that keep a remainder below `d`, the remainder at the end is below `d`. -/
public theorem divLoop_fwd (step : L → L → L × L) (d : L)
    (hw : ∀ c x, LA.val c < LA.val d → LA.val (step c x).2 < LA.val d) (r : A) (ro : USize)
    (a : A) (ao j : USize) (hr : LoopBound r ro j) (ha : LoopBound a ao j) (c : L)
    (hc : LA.val c < LA.val d) : LA.val (divLoop A step r ro a ao j hr ha c).2 < LA.val d := by
  induction r, j, hr, ha, c using divLoop.induct A (R := R) step ro a ao with
  | case1 r hr ha c => rw [divLoop, dite_eq_left rfl]; exact hc
  | case2 r j hr ha c hj hm' p ih =>
    rw [divLoop, dite_eq_right hj]
    exact ih (hw _ _ hc)

/--
`divLoop` divides, when its steps do and either keep a remainder below `d` or keep a failure, and
its remainder at the end is below `d`.
-/
public theorem divLoop_spec (step : L → L → L × L) (d : L)
    (hs : ∀ c x, LA.val c < LA.val d → LA.val (step c x).2 < LA.val d →
      LA.val d * LA.val (step c x).1 + LA.val (step c x).2 = LA.val c * 2 ^ LA.w + LA.val x)
    (hk : (∀ c x, LA.val c < LA.val d → LA.val (step c x).2 < LA.val d) ∨
      (∀ c x, LA.val (step c x).2 < LA.val d → LA.val c < LA.val d))
    (r : A) (ro : USize) (a : A) (ao j : USize) (hr : LoopBound r ro j) (ha : LoopBound a ao j)
    (c : L) (hc : LA.val c < LA.val d)
    (hf : LA.val (divLoop A step r ro a ao j hr ha c).2 < LA.val d) :
    LA.val d * LimbArray.valAt (divLoop A step r ro a ao j hr ha c).1 ro.toNat j.toNat +
        LA.val (divLoop A step r ro a ao j hr ha c).2 =
      LA.val c * 2 ^ (LA.w * j.toNat) + LimbArray.valAt a ao.toNat j.toNat := by
  induction r, j, hr, ha, c using divLoop.induct A (R := R) step ro a ao with
  | case1 r hr ha c =>
    rw [divLoop, dite_eq_left rfl] at hf ⊢
    simp
  | case2 r j hr ha c hj hm p ih =>
    rw [divLoop, dite_eq_right hj] at hf ⊢
    have hp := toNat_pred' hm
    have hj₀ := USize.lt_iff_toNat_lt.1 hm
    have hc' : LA.val p.2 < LA.val d := by
      rcases hk with hw | hm'
      · exact hw _ _ hc
      · exact divLoop_mono step d hm' _ _ _ _ _ _ _ _ hf
    have i₁ := ih hc' hf
    rw [hp] at i₁
    have htop := (divLoop_frame step (R.uset r (ro + (j - 1)) p.1 (hr.uset_bound (pred_lt' hm)))
      ro a ao (j - 1) ((bound_pred hr hm).of_uset ..) (bound_pred ha hm) p.2).2
      (ro.toNat + (j.toNat - 1)) (.inr (by rw [hp]; exact Nat.le_refl _))
    rw [R.get_uset, ite_eq_left (by rw [hr.toNat_add (pred_lt' hm), hp])] at htop
    have hx : R.uget a (ao + (j - 1)) (ha.uset_bound (pred_lt' hm)) =
        LA.get a (ao.toNat + (j.toNat - 1)) := by
      rw [R.uget_eq, ha.toNat_add (pred_lt' hm), hp]
    have e : LA.val d * LA.val p.1 + LA.val p.2 =
        LA.val c * 2 ^ LA.w + LA.val (LA.get a (ao.toNat + (j.toNat - 1))) := by
      rw [← hx]; exact hs _ _ hc hc'
    clear ih hs hk
    obtain ⟨k, hk'⟩ : ∃ k, j.toNat = k + 1 := ⟨j.toNat - 1, by lia⟩
    rw [hk', Nat.add_sub_cancel] at i₁ htop e
    rw [hk', LimbArray.valAt_add, LimbArray.valAt_add, LimbArray.valAt_one,
      LimbArray.valAt_one, htop, Nat.mul_succ, Nat.pow_add]
    generalize divLoop A step _ ro a ao (j - 1) _ _ p.2 = q at *
    generalize LimbArray.valAt q.1 ro.toNat k = Q at *
    generalize LimbArray.valAt a ao.toNat k = X at *
    generalize 2 ^ (LA.w * k) = P at *
    generalize LA.val (LA.get a (ao.toNat + k)) = x at *
    generalize LA.val p.1 = q₁ at *
    generalize LA.val p.2 = r₁ at *
    generalize LA.val q.2 = F at *
    generalize 2 ^ LA.w = B at *
    grind

/-! ## Division by a limb -/

variable (A) in
/--
Writes the limbs of `a / d`, for limbs `ao` to `ao + n - 1` of `a`, into limbs `ro` to `ro + n - 1`
of `r` and returns `a % d`, like GMP's `mpn_divrem_1`. It requires `0 < d`. From `t` limbs and for
a normalized `d` it takes the steps with the reciprocal (`div21`), which then pays for its division;
if their remainder is not below `d`, a check failed, and it divides again by `div2`, into the
array of the first pass.
-/
@[inline, expose] public def divRem1W (t : USize) (r : A) (ro : USize) (a : A) (ao n : USize)
    (hr : LoopBound r ro n) (ha : LoopBound a ao n) (d : L) : A × L :=
  if isNorm A d && decide (t ≤ n) then
    let p := divLoop A (div21 A (recip21 A d) d) r ro a ao n hr ha R.zero
    if R.ltB p.2 d then p
    else divLoop A (divStep A d) p.1 ro a ao n (hr.of_size (divLoop_frame ..).1) ha R.zero
  else divLoop A (divStep A d) r ro a ao n hr ha R.zero

private theorem divRem1W_plain (r : A) (ro : USize) (a : A) (ao n : USize)
    (hr : LoopBound r ro n) (ha : LoopBound a ao n) (d : L) (hd : 0 < LA.val d) :
    let p := divLoop A (divStep A d) r ro a ao n hr ha R.zero
    LA.val d * LimbArray.valAt p.1 ro.toNat n.toNat + LA.val p.2 =
      LimbArray.valAt a ao.toNat n.toNat ∧ LA.val p.2 < LA.val d := by
  have hz : LA.val (R.zero : L) < LA.val d := by rw [R.val_zero]; exact hd
  have hw : ∀ c x, LA.val c < LA.val d → LA.val (divStep A d c x).2 < LA.val d :=
    fun c x h => (divStep_spec d c x h).1
  have hf := divLoop_fwd _ d hw r ro a ao n hr ha _ hz
  refine ⟨?_, hf⟩
  have := divLoop_spec _ d (fun c x h _ => (divStep_spec d c x h).2) (.inl hw) r ro a ao n hr ha
    _ hz hf
  rw [R.val_zero, Nat.zero_mul, Nat.zero_add] at this
  exact this

public theorem divRem1W_frame (t : USize) (r : A) (ro : USize) (a : A) (ao n : USize)
    (hr : LoopBound r ro n) (ha : LoopBound a ao n) (d : L) :
    LA.size (divRem1W A t r ro a ao n hr ha d).1 = LA.size r ∧
      ∀ i, (i < ro.toNat ∨ ro.toNat + n.toNat ≤ i) →
        LA.get (divRem1W A t r ro a ao n hr ha d).1 i = LA.get r i := by
  unfold divRem1W
  split
  · dsimp only
    obtain ⟨f₁, f₂⟩ := divLoop_frame (div21 A (recip21 A d) d) r ro a ao n hr ha R.zero
    split
    · exact ⟨f₁, f₂⟩
    · obtain ⟨g₁, g₂⟩ := divLoop_frame (divStep A d)
        (divLoop A (div21 A (recip21 A d) d) r ro a ao n hr ha R.zero).1 ro a ao n
        (hr.of_size f₁) ha R.zero
      exact ⟨by rw [g₁, f₁], fun i hi => by rw [g₂ i hi, f₂ i hi]⟩
  · exact divLoop_frame ..

public theorem divRem1W_spec (t : USize) (r : A) (ro : USize) (a : A) (ao n : USize)
    (hr : LoopBound r ro n) (ha : LoopBound a ao n) (d : L) (hd : 0 < LA.val d) :
    LA.size (divRem1W A t r ro a ao n hr ha d).1 = LA.size r ∧
      (∀ i, (i < ro.toNat ∨ ro.toNat + n.toNat ≤ i) →
        LA.get (divRem1W A t r ro a ao n hr ha d).1 i = LA.get r i) ∧
      LA.val d * LimbArray.valAt (divRem1W A t r ro a ao n hr ha d).1 ro.toNat n.toNat +
          LA.val (divRem1W A t r ro a ao n hr ha d).2 = LimbArray.valAt a ao.toNat n.toNat ∧
      LA.val (divRem1W A t r ro a ao n hr ha d).2 < LA.val d := by
  have hz : LA.val (R.zero : L) < LA.val d := by rw [R.val_zero]; exact hd
  refine ⟨(divRem1W_frame ..).1, (divRem1W_frame ..).2, ?_⟩
  unfold divRem1W
  split
  · dsimp only
    split
    · rename_i hlt
      have hlt' := (R.ltB_iff ..).1 hlt
      refine ⟨?_, hlt'⟩
      have := divLoop_spec _ d (fun c x _ h => (div21_spec _ d c x h).2)
        (.inr fun c x h => (div21_spec _ d c x h).1) r ro a ao n hr ha _ hz hlt'
      rw [R.val_zero, Nat.zero_mul, Nat.zero_add] at this
      exact this
    · exact divRem1W_plain _ ro a ao n _ ha d hd
  · exact divRem1W_plain r ro a ao n hr ha d hd

end MPN.WordArray
