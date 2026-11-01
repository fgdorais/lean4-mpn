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

The step is `div2Rem` (`divStep`), or for a normalized `d`, with its top bit set, Möller and
Granlund's 2-by-1 step with the precomputed reciprocal `⌊(β² - 1) / d⌋ - β` (`div21`, GMP's
`udiv_qr_2by1`), whose one double product and two corrections cost less than a hardware divider.
`div21` checks its result exactly, `q d + r = c β + x` with `r < d`, by one more double product
off the dependency chain, so that neither the reciprocal nor the error bound of the step needs a
proof. A failed check gives the remainder `d`, which makes every later check fail too, so that the
division checks the last remainder once and divides again with `div2Rem` if it is not below `d`,
which never happens.

For an unnormalized `d`, the same steps divide `a 2ˢ` by `d 2ˢ`, whose top bit is set, as in GMP:
`a` is shifted into the window of `r` (`lshiftW`) and divided there in place (`divLoopSelf`), and
the remainder is shifted back (`divRem1U`). Each branch has its own threshold, since the shift is
one more pass.
-/

namespace MPN.WordArray

variable {A L : Type} [LA : LimbArray A L] [R : WordArray A L]

/-! ## The steps -/

variable (A) in
/-- The quotient limb and remainder of `c β + x` by `d`, for `c < d`, by `div2Rem`. -/
@[inline, expose] public def divStep (d c x : L) : L × L := R.div2Rem c x d

public theorem divStep_spec (d c x : L) (h : LA.val c < LA.val d) :
    LA.val (divStep A d c x).2 < LA.val d ∧
      LA.val d * LA.val (divStep A d c x).1 + LA.val (divStep A d c x).2 =
        LA.val c * 2 ^ LA.w + LA.val x := by
  obtain ⟨h₁, h₂⟩ := R.val_div2Rem c x d h
  rw [divStep, h₁, h₂]
  exact ⟨Nat.mod_lt _ (by lia), Nat.div_add_mod ..⟩

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
/--
The reciprocal `⌊(β³ - 1) / (d₁ β + d₀)⌋ - β` of a normalized `d₁ β + d₀`, like GMP's
`invert_pi1`, for the 3-by-2 steps of schoolbook division (`Schoolbook.qEstR`), which check their
results, so that it needs no proof.
-/
@[expose] public def recip32 (d₁ d₀ : L) : L :=
  let v := recip21 A d₁
  let p := R.add (R.mul d₁ v) d₀
  let vp : L × L :=
    if R.ltB p d₀ then
      let mask := R.sub R.zero (R.ofBool (!R.ltB p d₁))
      (R.add (R.sub v R.one) mask, R.sub (R.sub p d₁) (R.land mask d₁))
    else (v, p)
  let v := vp.1
  let t₁ := R.mulh d₀ v
  let p := R.add vp.2 t₁
  if R.ltB p t₁ then
    if !R.ltB p d₁ && (R.ltB d₁ p || !R.ltB (R.mul d₀ v) d₀) then R.sub v (R.add R.one R.one)
    else R.sub v R.one
  else v

variable (A) in
/-- Whether the top bit of `d` is set. -/
@[inline, expose] public def isNorm (d : L) : Bool :=
  !R.ltB d (R.shl R.one (R.ofUSize (R.wU - 1)))

variable (A) in
/--
The reciprocal of the top limbs `v₁ v₂` of a divisor of `n` limbs for the steps of schoolbook
division from `t` limbs on, when `v₁` is normalized, or `0`, which takes the steps without it
(`Schoolbook.qEstD`).
-/
@[inline, expose] public def divRecip32 (t n : USize) (v₁ v₂ : L) : L :=
  if t ≤ n && isNorm A v₁ then recip32 A v₁ v₂ else R.zero

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

/-! ## The loop in place -/

variable (A) in
/--
Divides `c βʲ` plus limbs `ro` to `ro + j - 1` of `r` by the steps `step`, from limb `ro + j - 1`
down, in place: each step reads its limb and writes the quotient limb there. Returns the remainder.
-/
@[expose, specialize]
public def divLoopSelf (step : L → L → L × L) (r : A) (ro j : USize) (hr : LoopBound r ro j)
    (c : L) : A × L :=
  if hj : j = 0 then (r, c)
  else
    have hm := pos_of_ne hj
    let p := step c (R.uget r (ro + (j - 1)) (hr.uset_bound (pred_lt' hm)))
    divLoopSelf step (R.uset r (ro + (j - 1)) p.1 (hr.uset_bound (pred_lt' hm))) ro (j - 1)
      ((bound_pred hr hm).of_uset ..) p.2
termination_by j.toNat
decreasing_by
  have := toNat_pred' (pos_of_ne hj)
  have := USize.lt_iff_toNat_lt.1 (pos_of_ne hj)
  lia

public theorem divLoopSelf_frame (step : L → L → L × L) (r : A) (ro j : USize)
    (hr : LoopBound r ro j) (c : L) :
    LA.size (divLoopSelf A step r ro j hr c).1 = LA.size r ∧
      ∀ i, (i < ro.toNat ∨ ro.toNat + j.toNat ≤ i) →
        LA.get (divLoopSelf A step r ro j hr c).1 i = LA.get r i := by
  induction r, j, hr, c using divLoopSelf.induct A (R := R) step ro with
  | case1 r hr c => rw [divLoopSelf, dite_eq_left rfl]; exact ⟨rfl, fun _ _ => rfl⟩
  | case2 r j hr c hj hm p ih =>
    rw [divLoopSelf, dite_eq_right hj]
    obtain ⟨i₁, i₂⟩ := ih
    refine ⟨by rw [i₁, R.size_uset], fun i hi => ?_⟩
    have hp := toNat_pred' hm
    have := USize.lt_iff_toNat_lt.1 hm
    rw [i₂ i (by rw [hp]; lia), R.get_uset,
      ite_eq_right (by rw [hr.toNat_add (pred_lt' hm), hp]; lia)]

/-- `divLoop_mono` for `divLoopSelf`. -/
public theorem divLoopSelf_mono (step : L → L → L × L) (d : L)
    (hm : ∀ c x, LA.val (step c x).2 < LA.val d → LA.val c < LA.val d) (r : A) (ro j : USize)
    (hr : LoopBound r ro j) (c : L)
    (hf : LA.val (divLoopSelf A step r ro j hr c).2 < LA.val d) : LA.val c < LA.val d := by
  induction r, j, hr, c using divLoopSelf.induct A (R := R) step ro with
  | case1 r hr c => rw [divLoopSelf, dite_eq_left rfl] at hf; exact hf
  | case2 r j hr c hj hm' p ih =>
    rw [divLoopSelf, dite_eq_right hj] at hf
    exact hm _ _ (ih hf)

/-- `divLoop_spec` for `divLoopSelf`, under steps that keep a failure. -/
public theorem divLoopSelf_spec (step : L → L → L × L) (d : L)
    (hs : ∀ c x, LA.val c < LA.val d → LA.val (step c x).2 < LA.val d →
      LA.val d * LA.val (step c x).1 + LA.val (step c x).2 = LA.val c * 2 ^ LA.w + LA.val x)
    (hm : ∀ c x, LA.val (step c x).2 < LA.val d → LA.val c < LA.val d)
    (r : A) (ro j : USize) (hr : LoopBound r ro j) (c : L)
    (hf : LA.val (divLoopSelf A step r ro j hr c).2 < LA.val d) :
    LA.val d * LimbArray.valAt (divLoopSelf A step r ro j hr c).1 ro.toNat j.toNat +
        LA.val (divLoopSelf A step r ro j hr c).2 =
      LA.val c * 2 ^ (LA.w * j.toNat) + LimbArray.valAt r ro.toNat j.toNat := by
  induction r, j, hr, c using divLoopSelf.induct A (R := R) step ro with
  | case1 r hr c =>
    rw [divLoopSelf, dite_eq_left rfl] at hf ⊢
    simp
  | case2 r j hr c hj hm' p ih =>
    rw [divLoopSelf, dite_eq_right hj] at hf ⊢
    have hp := toNat_pred' hm'
    have hj₀ := USize.lt_iff_toNat_lt.1 hm'
    have hc' : LA.val p.2 < LA.val d := divLoopSelf_mono step d hm _ _ _ _ _ hf
    have hc : LA.val c < LA.val d := hm _ _ hc'
    have i₁ := ih hf
    rw [hp] at i₁
    have hidx := hr.toNat_add (pred_lt' hm')
    rw [hp] at hidx
    have hlow : LimbArray.valAt (R.uset r (ro + (j - 1)) p.1 (hr.uset_bound (pred_lt' hm')))
        ro.toNat (j.toNat - 1) = LimbArray.valAt r ro.toNat (j.toNat - 1) :=
      valAt_uset_of _ _ _ _ _ _ (.inr (by rw [hidx]; exact Nat.le_refl _))
    rw [hlow] at i₁
    have htop := (divLoopSelf_frame step
      (R.uset r (ro + (j - 1)) p.1 (hr.uset_bound (pred_lt' hm'))) ro (j - 1)
      ((bound_pred hr hm').of_uset ..) p.2).2
      (ro.toNat + (j.toNat - 1)) (.inr (by rw [hp]; exact Nat.le_refl _))
    rw [R.get_uset, ite_eq_left (by rw [hidx])] at htop
    have hx : R.uget r (ro + (j - 1)) (hr.uset_bound (pred_lt' hm')) =
        LA.get r (ro.toNat + (j.toNat - 1)) := by
      rw [R.uget_eq, hidx]
    have e : LA.val d * LA.val p.1 + LA.val p.2 =
        LA.val c * 2 ^ LA.w + LA.val (LA.get r (ro.toNat + (j.toNat - 1))) := by
      rw [← hx]; exact hs _ _ hc hc'
    clear ih hs hm
    obtain ⟨k, hk'⟩ : ∃ k, j.toNat = k + 1 := ⟨j.toNat - 1, by lia⟩
    rw [hk', Nat.add_sub_cancel] at i₁ htop e
    rw [hk', LimbArray.valAt_add, LimbArray.valAt_add, LimbArray.valAt_one,
      LimbArray.valAt_one, htop, Nat.mul_succ, Nat.pow_add]
    generalize divLoopSelf A step _ ro (j - 1) _ p.2 = q at *
    generalize LimbArray.valAt q.1 ro.toNat k = Q at *
    generalize LimbArray.valAt r ro.toNat k = X at *
    generalize 2 ^ (LA.w * k) = P at *
    generalize LA.val (LA.get r (ro.toNat + k)) = x at *
    generalize LA.val p.1 = q₁ at *
    generalize LA.val p.2 = r₁ at *
    generalize LA.val q.2 = F at *
    generalize 2 ^ LA.w = B at *
    grind

/-! ## Division by a limb -/

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

/-- The checks of `divRem1U`: the shift and the normalized divisor. -/
private theorem shift_checks (d s : L)
    (h : (R.ltB R.zero s && R.ltB s (R.ofUSize R.wU) && R.eqB (R.shr (R.shl d s) s) d) = true) :
    0 < LA.val s ∧ LA.val s < LA.w ∧ LA.val (R.shl d s) = LA.val d * 2 ^ LA.val s := by
  simp only [Bool.and_eq_true, R.ltB_iff, R.eqB_iff, R.val_zero, R.val_ofUSize, R.toNat_wU] at h
  obtain ⟨⟨h₁, h₂⟩, h₃⟩ := h
  have hw : LA.w < 2 ^ LA.w := Nat.lt_two_pow_self
  rw [Nat.mod_eq_of_lt hw] at h₂
  refine ⟨h₁, h₂, ?_⟩
  rw [R.val_shr, R.val_shl, Nat.mod_eq_of_lt h₂] at h₃
  rw [R.val_shl, Nat.mod_eq_of_lt h₂]
  have hle := Nat.mod_le (LA.val d * 2 ^ LA.val s) (2 ^ LA.w)
  have hge := Nat.div_mul_le_self (LA.val d * 2 ^ LA.val s % 2 ^ LA.w) (2 ^ LA.val s)
  rw [h₃] at hge
  lia

variable [F : WordFolds A L]

variable (A) in
/-- The shift `w - 1 - ⌊log₂ d⌋` that normalizes a nonzero `d`. -/
@[inline, expose] public def normShift (d : L) : L := R.ofUSize (R.wU - 1 - (R.log2 d).toUSize)

variable (A) in
/--
`a / d` and `a % d` like `divRem1W`, for an unnormalized `d`, by the steps with the reciprocal of
`d 2ˢ`, normalized: `a 2ˢ` goes into the window of `r` by `lshiftW`, with its top bits as the
first remainder, `divLoopSelf` divides it there in place, and the remainder is shifted back. The
shift is checked, `0 < s < w` and `(d 2ˢ) / 2ˢ = d`, and so is the remainder of the steps, with
`div2Rem` when a check fails, so that neither needs a proof.
-/
@[inline, expose] public def divRem1U (r : A) (ro : USize) (a : A) (ao n : USize)
    (hr : LoopBound r ro n) (ha : LoopBound a ao n) (d : L) : A × L :=
  let s := normShift A d
  let dn := R.shl d s
  if R.ltB R.zero s && R.ltB s (R.ofUSize R.wU) && R.eqB (R.shr dn s) d then
    let p := lshiftW r ro a ao n s hr ha
    let q := divLoopSelf A (div21 A (recip21 A dn) dn) p.1 ro n (hr.of_size (size_lshiftW ..)) p.2
    if R.ltB q.2 dn then (q.1, R.shr q.2 s)
    else
      divLoop A (divStep A d) q.1 ro a ao n
        (hr.of_size (by rw [(divLoopSelf_frame ..).1, size_lshiftW])) ha R.zero
  else divLoop A (divStep A d) r ro a ao n hr ha R.zero

variable (A) in
/--
Writes the limbs of `a / d`, for limbs `ao` to `ao + n - 1` of `a`, into limbs `ro` to `ro + n - 1`
of `r` and returns `a % d`, like GMP's `mpn_divrem_1`. It requires `0 < d`. From `t` limbs and for
a normalized `d` it takes the steps with the reciprocal (`div21`), which then pays for its division;
if their remainder is not below `d`, a check failed, and it divides again by `div2Rem`, into the
array of the first pass. From `tu` limbs and for an unnormalized `d` it takes the same steps on
`a 2ˢ` and `d 2ˢ` (`divRem1U`).
-/
@[inline, expose] public def divRem1W (t tu : USize) (r : A) (ro : USize) (a : A) (ao n : USize)
    (hr : LoopBound r ro n) (ha : LoopBound a ao n) (d : L) : A × L :=
  if isNorm A d && decide (t ≤ n) then
    let p := divLoop A (div21 A (recip21 A d) d) r ro a ao n hr ha R.zero
    if R.ltB p.2 d then p
    else divLoop A (divStep A d) p.1 ro a ao n (hr.of_size (divLoop_frame ..).1) ha R.zero
  else if !isNorm A d && decide (tu ≤ n) then divRem1U A r ro a ao n hr ha d
  else divLoop A (divStep A d) r ro a ao n hr ha R.zero

private theorem divRem1U_frame (r : A) (ro : USize) (a : A) (ao n : USize)
    (hr : LoopBound r ro n) (ha : LoopBound a ao n) (d : L) :
    LA.size (divRem1U A r ro a ao n hr ha d).1 = LA.size r ∧
      ∀ i, (i < ro.toNat ∨ ro.toNat + n.toNat ≤ i) →
        LA.get (divRem1U A r ro a ao n hr ha d).1 i = LA.get r i := by
  unfold divRem1U
  dsimp only
  split
  · rename_i hc
    obtain ⟨hs₀, hs, -⟩ := shift_checks d (normShift A d) hc
    obtain ⟨l₁, l₂, -⟩ := lshiftW_spec r ro a ao n (normShift A d) hr ha hs₀ hs
    obtain ⟨f₁, f₂⟩ := divLoopSelf_frame (div21 A (recip21 A (R.shl d (normShift A d)))
      (R.shl d (normShift A d))) (lshiftW r ro a ao n (normShift A d) hr ha).1 ro n
      (hr.of_size (size_lshiftW ..)) (lshiftW r ro a ao n (normShift A d) hr ha).2
    split
    · exact ⟨by rw [f₁, l₁], fun i hi => by rw [f₂ i hi, l₂ i hi]⟩
    · obtain ⟨g₁, g₂⟩ := divLoop_frame (divStep A d) _ ro a ao n
        (hr.of_size (by rw [f₁, size_lshiftW])) ha R.zero
      exact ⟨by rw [g₁, f₁, l₁], fun i hi => by rw [g₂ i hi, f₂ i hi, l₂ i hi]⟩
  · exact divLoop_frame ..

private theorem divRem1U_spec (r : A) (ro : USize) (a : A) (ao n : USize)
    (hr : LoopBound r ro n) (ha : LoopBound a ao n) (d : L) (hd : 0 < LA.val d) :
    LA.val d * LimbArray.valAt (divRem1U A r ro a ao n hr ha d).1 ro.toNat n.toNat +
        LA.val (divRem1U A r ro a ao n hr ha d).2 = LimbArray.valAt a ao.toNat n.toNat ∧
      LA.val (divRem1U A r ro a ao n hr ha d).2 < LA.val d := by
  unfold divRem1U
  dsimp only
  split
  · rename_i hc
    obtain ⟨hs₀, hs, hdn⟩ := shift_checks d (normShift A d) hc
    obtain ⟨-, -, l₃⟩ := lshiftW_spec r ro a ao n (normShift A d) hr ha hs₀ hs
    split
    · rename_i hlt
      have hlt' := (R.ltB_iff ..).1 hlt
      have hq := divLoopSelf_spec _ (R.shl d (normShift A d))
        (fun c x _ h => (div21_spec _ _ c x h).2) (fun c x h => (div21_spec _ _ c x h).1)
        (lshiftW r ro a ao n (normShift A d) hr ha).1 ro n (hr.of_size (size_lshiftW ..))
        (lshiftW r ro a ao n (normShift A d) hr ha).2 hlt'
      rw [hdn] at hq hlt'
      dsimp only
      rw [R.val_shr, Nat.mod_eq_of_lt hs]
      generalize divLoopSelf A _ _ ro n _ _ = q at hq hlt'
      generalize LimbArray.valAt (lshiftW r ro a ao n (normShift A d) hr ha).1 ro.toNat n.toNat = V
        at l₃ hq
      generalize LA.val (lshiftW r ro a ao n (normShift A d) hr ha).2 = c at l₃ hq
      generalize LimbArray.valAt q.1 ro.toNat n.toNat = Q at hq ⊢
      generalize LA.val q.2 = r₂ at hq hlt' ⊢
      generalize LimbArray.valAt a ao.toNat n.toNat = X at l₃ ⊢
      generalize LA.val (normShift A d) = k at hs₀ hs hq hlt' l₃ ⊢
      generalize 2 ^ (LA.w * n.toNat) = B at hq l₃
      generalize LA.val d = D at hq hlt' hd ⊢
      have hP : 0 < 2 ^ k := Nat.two_pow_pos k
      -- `D 2ᵏ Q + r₂ = X 2ᵏ`, so `r₂ = (X - D Q) 2ᵏ`.
      have e : D * 2 ^ k * Q + r₂ = X * 2 ^ k := by rw [hq, ← l₃]; grind
      have hDQ : D * Q ≤ X := by
        refine Nat.le_of_mul_le_mul_right ?_ hP
        rw [Nat.mul_right_comm]; lia
      have hr₂ : r₂ = (X - D * Q) * 2 ^ k := by rw [Nat.sub_mul, Nat.mul_right_comm]; lia
      rw [hr₂, Nat.mul_div_cancel _ hP]
      refine ⟨by lia, ?_⟩
      rw [hr₂] at hlt'
      exact Nat.lt_of_mul_lt_mul_right hlt'
    · exact divRem1W_plain _ ro a ao n _ ha d hd
  · exact divRem1W_plain r ro a ao n hr ha d hd

public theorem divRem1W_frame (t tu : USize) (r : A) (ro : USize) (a : A) (ao n : USize)
    (hr : LoopBound r ro n) (ha : LoopBound a ao n) (d : L) :
    LA.size (divRem1W A t tu r ro a ao n hr ha d).1 = LA.size r ∧
      ∀ i, (i < ro.toNat ∨ ro.toNat + n.toNat ≤ i) →
        LA.get (divRem1W A t tu r ro a ao n hr ha d).1 i = LA.get r i := by
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
  · split
    · exact divRem1U_frame ..
    · exact divLoop_frame ..

public theorem divRem1W_spec (t tu : USize) (r : A) (ro : USize) (a : A) (ao n : USize)
    (hr : LoopBound r ro n) (ha : LoopBound a ao n) (d : L) (hd : 0 < LA.val d) :
    LA.size (divRem1W A t tu r ro a ao n hr ha d).1 = LA.size r ∧
      (∀ i, (i < ro.toNat ∨ ro.toNat + n.toNat ≤ i) →
        LA.get (divRem1W A t tu r ro a ao n hr ha d).1 i = LA.get r i) ∧
      LA.val d * LimbArray.valAt (divRem1W A t tu r ro a ao n hr ha d).1 ro.toNat n.toNat +
          LA.val (divRem1W A t tu r ro a ao n hr ha d).2 = LimbArray.valAt a ao.toNat n.toNat ∧
      LA.val (divRem1W A t tu r ro a ao n hr ha d).2 < LA.val d := by
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
  · split
    · exact divRem1U_spec r ro a ao n hr ha d hd
    · exact divRem1W_plain r ro a ao n hr ha d hd

end MPN.WordArray
