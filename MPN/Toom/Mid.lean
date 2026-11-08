/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import MPN.MulLimbW
public import MPN.FFT.Fermat
public import MPN.Toom.Ops

/-!
# The middle term of Karatsuba's method, for limbs of any width

With `z₀ = a₀ b₀` in limbs `[o, o + 2 k)` of `d` and `z₂ = a₁ b₁` in `[o + 2 k, o + n)`, Karatsuba's
method adds `z₁ = t - z₀ - z₂` from limb `o + k` on, where `t = (a₀ + a₁) (b₀ + b₁)` has
`2 k + 2` limbs. `midW d o k n t` does it in one pass over the window of `L = min (n - k) (2 k + 2)`
limbs of `t`: limb `i` becomes `d[o + k + i] + t[i] - z₀[i] - z₂[i]` plus the carry, by the width's
`addDiffC`, written into `t`, which nothing else holds (`d` cannot be written in place: the window
overlaps the limbs of `z₀` and `z₂` that are still to be read). The window is then copied into `d`
with `copyIn`, and the carry goes on above it with `FFT.incrAt`. Two subtractions and an addition
took three passes over `t`.

The carry from one limb to the next is between `-2` and `1`; the loop keeps it plus `2`, a word
between `0` and `3`. Outside its conditions `midW` writes the value of its specification with
`writeNat`, which never happens.
-/

namespace MPN.WordArray

open LimbArray Toom

variable {A L : Type} [LA : LimbArray A L] [R : WordArray A L] [F : WordFolds A L]

/-! ## Sums of digits -/

/-- `g j + 2ʷ g (j + 1) + ⋯`, `m` terms: the value of the digits `g j, …, g (j + m - 1)`. -/
public def wsum (w : Nat) (g : Nat → Nat) (j : Nat) : Nat → Nat
  | 0 => 0
  | m + 1 => g j + 2 ^ w * wsum w g (j + 1) m

omit R F in
private theorem wsum_get (a : A) (lo m : Nat) : ∀ j,
    wsum LA.w (fun i => LA.val (LA.get a (lo + i))) j m = valAt a (lo + j) m := by
  induction m with
  | zero => intro j; rw [wsum, valAt_zero]
  | succ m ih => intro j; rw [wsum, ih (j + 1), valAt_succ, Nat.add_assoc]

omit R F in
/-- The limbs of `a` from `lo`, `len` of them and zeros after. -/
private theorem wsum_pad (a : A) (lo len m : Nat) : ∀ j, len ≤ j + m →
    wsum LA.w (fun i => if i < len then LA.val (LA.get a (lo + i)) else 0) j m =
      valAt a (lo + j) (len - j) := by
  induction m with
  | zero => intro j hj; rw [wsum, show len - j = 0 by lia, valAt_zero]
  | succ m ih =>
    intro j hj
    rw [wsum, ih (j + 1) (by lia)]
    by_cases hjl : j < len
    · simp only [hjl, ↓reduceIte]
      rw [show len - j = len - (j + 1) + 1 by lia, valAt_succ, Nat.add_assoc]
    · simp only [hjl, ↓reduceIte, show len - (j + 1) = 0 by lia, show len - j = 0 by lia,
        valAt_zero, Nat.mul_zero, Nat.add_zero]

/-! ## The loop -/

omit F in
/--
A fold whose step computes limb `v + x + (c - 2) - y - z` and the next carry plus `2` from the
digits `gv j`, `gy j`, `gz j`: the new limbs, the carry out and the digits it reads, as values.
-/
private theorem fold_mid (n : USize) (f : (j : USize) → j < n → L → L → L × L)
    (gv gy gz : Nat → Nat)
    (hf : ∀ j h x c, LA.val c ≤ 3 →
      LA.val (f j h x c).1 + 2 ^ LA.w * LA.val (f j h x c).2 + gy j.toNat + gz j.toNat + 2 =
          gv j.toNat + LA.val x + LA.val c + 2 * 2 ^ LA.w ∧ LA.val (f j h x c).2 ≤ 3)
    (arr : A) (rs : USize) (hr : LoopBound arr rs n) (j : USize) (c : L) (hc : LA.val c ≤ 3) :
    LA.size (foldUInPlace n f arr rs hr j c).1 = LA.size arr ∧
      LA.val (foldUInPlace n f arr rs hr j c).2 ≤ 3 ∧
      (∀ i, (i < rs.toNat + j.toNat ∨ rs.toNat + n.toNat ≤ i) →
        LA.get (foldUInPlace n f arr rs hr j c).1 i = LA.get arr i) ∧
      valAt (foldUInPlace n f arr rs hr j c).1 (rs.toNat + j.toNat) (n.toNat - j.toNat) +
          2 ^ (LA.w * (n.toNat - j.toNat)) * LA.val (foldUInPlace n f arr rs hr j c).2 +
          wsum LA.w gy j.toNat (n.toNat - j.toNat) + wsum LA.w gz j.toNat (n.toNat - j.toNat) + 2 =
        wsum LA.w gv j.toNat (n.toNat - j.toNat) +
          valAt arr (rs.toNat + j.toNat) (n.toNat - j.toNat) +
          LA.val c + 2 * 2 ^ (LA.w * (n.toNat - j.toNat)) := by
  induction arr, hr, j, c using foldUInPlace.induct (R := R) n f rs with
  | case1 arr hr j c h p ih =>
    rw [foldUInPlace_lt _ _ _ _ _ _ _ h]
    have hj := USize.lt_iff_toNat_lt.1 h
    have hj₁ := USize.toNat_add_one_of_lt h
    have hri := hr.toNat_add h
    have hz' : R.uget arr (rs + j) (hr.uset_bound h) = LA.get arr (rs.toNat + j.toNat) := by
      rw [R.uget_eq, hri]
    obtain ⟨hp₁, hp₂⟩ := hf j h (R.uget arr (rs + j) (hr.uset_bound h)) c hc
    obtain ⟨ih₁, ih₀, ih₂, ih₃⟩ := ih hp₂
    rw [hj₁] at ih₂ ih₃
    rw [R.size_uset] at ih₁
    have hv : LA.get (foldUInPlace n f (R.uset arr (rs + j) p.1 (hr.uset_bound h)) rs
        (hr.of_uset ..) (j + 1) p.2).1 (rs.toNat + j.toNat) = p.1 := by
      rw [ih₂ _ (.inl (by lia)), R.get_uset]
      simp [hri]
    have hZ : valAt (R.uset arr (rs + j) p.1 (hr.uset_bound h))
        (rs.toNat + (j.toNat + 1)) (n.toNat - (j.toNat + 1)) =
          valAt arr (rs.toNat + (j.toNat + 1)) (n.toNat - (j.toNat + 1)) :=
      valAt_uset_of _ _ _ _ _ _ (by rw [hri]; lia)
    refine ⟨ih₁, ih₀, fun i hi => ?_, ?_⟩
    · rw [ih₂ i (by lia), R.get_uset]
      simp only [hri]
      split <;> lia
    · rw [hZ] at ih₃
      obtain ⟨m, hm⟩ : ∃ m, n.toNat - j.toNat = m + 1 := ⟨n.toNat - j.toNat - 1, by lia⟩
      rw [show n.toNat - (j.toNat + 1) = m by lia, ← Nat.add_assoc] at ih₃
      rw [hm, valAt_succ, valAt_succ, hv, wsum, wsum, wsum, Nat.mul_succ, Nat.pow_add]
      rw [hz'] at hp₁
      simp only [p, hz'] at *
      generalize (foldUInPlace n f (R.uset arr (rs + j)
        (f j h (LA.get arr (rs.toNat + j.toNat)) c).1 (hr.uset_bound h)) rs (hr.of_uset ..) (j + 1)
          (f j h (LA.get arr (rs.toNat + j.toNat)) c).2) = q at *
      generalize f j h (LA.get arr (rs.toNat + j.toNat)) c = p' at *
      generalize valAt q.1 _ _ = X at *
      generalize valAt arr (rs.toNat + j.toNat + 1) m = T at *
      generalize wsum LA.w gv (j.toNat + 1) m = V at *
      generalize wsum LA.w gy (j.toNat + 1) m = Y at *
      generalize wsum LA.w gz (j.toNat + 1) m = Z at *
      generalize 2 ^ (LA.w * m) = P at *
      generalize LA.val q.2 = cR at *
      generalize LA.val p'.2 = c₁ at *
      generalize LA.val p'.1 = l at *
      generalize LA.val (LA.get arr (rs.toNat + j.toNat)) = x at *
      generalize (2 : Nat) ^ LA.w = B at *
      grind
  | case2 arr hr j c h =>
    rw [foldUInPlace_ge _ _ _ _ _ _ _ h]
    have : n.toNat - j.toNat = 0 := by have := USize.lt_iff_toNat_lt (a := j) (b := n); lia
    simp [this, hc, wsum]

/-! ## The middle term -/

omit F in
private theorem toNat_toUSize₄ {n : Nat} (h : n < 4294967295) : n.toUSize.toNat = n := by
  rw [Nat.toUSize_eq, USize.toNat_ofNat_of_lt' (by have := USize.size_eq; lia)]

/-- The length of the window, `min (n - k) (2 k + 2)`. -/
@[inline, expose] public def midLen (k n : Nat) : Nat := min (n - k) (k + k + 2)

/--
The conditions of `midW`: the `n` limbs from `o` fit in `d`, `t` has `2 k + 2` limbs, and
`3 k ≤ n ≤ 4 k + 2` with `2 ≤ k`, so that the window covers `z₀` and `z₂`.
-/
public structure MidOK (d : A) (o k n : Nat) (t : A) : Prop where
  hd : o + n ≤ LA.size d
  hdS : LA.size d < 4294967295
  hk : k + k + k ≤ n
  hn : n ≤ k + k + k + k + 2
  ht : LA.size t = k + k + 2
  hk2 : 2 ≤ k

/-- The checks of `midW`. -/
@[inline, expose] public def midOK (d : A) (o k n : Nat) (t : A) : Bool :=
  decide (o + n ≤ LA.size d) && decide (LA.size d < 4294967295) && decide (k + k + k ≤ n) &&
    decide (n ≤ k + k + k + k + 2) && decide (LA.size t = k + k + 2) && decide (2 ≤ k)

omit R F in
public theorem midOK_spec {d : A} {o k n : Nat} {t : A} (h : midOK d o k n t = true) :
    MidOK d o k n t := by
  simp only [midOK, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨h₁, h₂⟩, h₃⟩, h₄⟩, h₅⟩, h₆⟩ := h
  exact ⟨h₁, h₂, h₃, h₄, h₅, h₆⟩

namespace MidOK

variable {d : A} {o k n : Nat} {t : A}

omit R F in
public theorem e (h : MidOK d o k n t) :
    o.toUSize.toNat = o ∧ (o + k).toUSize.toNat = o + k ∧
      (o + (k + k)).toUSize.toNat = o + (k + k) ∧ (midLen k n).toUSize.toNat = midLen k n ∧
      (k + k).toUSize.toNat = k + k ∧ (n - (k + k)).toUSize.toNat = n - (k + k) ∧
      n.toUSize.toNat = n ∧ (k + midLen k n).toUSize.toNat = k + midLen k n := by
  have := h.hd; have := h.hdS; have := h.hk
  exact ⟨toNat_toUSize₄ (by lia), toNat_toUSize₄ (by lia), toNat_toUSize₄ (by lia),
    toNat_toUSize₄ (by unfold midLen; lia), toNat_toUSize₄ (by lia), toNat_toUSize₄ (by lia),
    toNat_toUSize₄ (by lia), toNat_toUSize₄ (by unfold midLen; lia)⟩

omit R F in
public theorem lbv (h : MidOK d o k n t) :
    LoopBound d (o + k).toUSize (midLen k n).toUSize := by
  obtain ⟨-, e₂, -, e₄, -⟩ := h.e
  have := h.hd; have := h.hdS; have := h.hk; have := USize.le_size
  constructor <;> rw [e₂, e₄] <;> unfold midLen <;> lia

omit R F in
public theorem lby (h : MidOK d o k n t) : LoopBound d o.toUSize (k + k).toUSize := by
  obtain ⟨e₁, -, -, -, e₅, -⟩ := h.e
  have := h.hd; have := h.hdS; have := h.hk; have := USize.le_size
  constructor <;> rw [e₁, e₅] <;> lia

omit R F in
public theorem lbz (h : MidOK d o k n t) :
    LoopBound d (o + (k + k)).toUSize (n - (k + k)).toUSize := by
  obtain ⟨-, -, e₃, -, -, e₆, -⟩ := h.e
  have := h.hd; have := h.hdS; have := h.hk; have := USize.le_size
  constructor <;> rw [e₃, e₆] <;> lia

omit R F in
public theorem lbt (h : MidOK d o k n t) : LoopBound t 0 (midLen k n).toUSize := by
  obtain ⟨-, -, -, e₄, -⟩ := h.e
  have := h.hd; have := h.hdS; have := h.ht; have := USize.le_size
  constructor <;> rw [USize.toNat_zero, e₄] <;> unfold midLen <;> lia

omit R F in
public theorem lbd (h : MidOK d o k n t) : LoopBound d o.toUSize n.toUSize := by
  obtain ⟨e₁, -, -, -, -, -, e₇, -⟩ := h.e
  have := h.hd; have := h.hdS; have := USize.le_size
  constructor <;> rw [e₁, e₇] <;> lia

end MidOK

variable (A) in
/--
Limb `i` of the window: `d[vo + i] + x - y - z` plus the carry `c - 2`, where `y` is limb `yo + i`
of `d` below `ny` and `0` after, and `z` limb `zo + i` below `nz`, by `addDiffC`.
-/
@[inline, expose] public def midStep (d : A) (vo yo zo len ny nz : USize) (hv : LoopBound d vo len)
    (hy : LoopBound d yo ny) (hz : LoopBound d zo nz) (i : USize) (hi : i < len) (x c : L) :
    L × L :=
  let v := R.uget d (vo + i) (hv.uset_bound hi)
  let y := if h : i < ny then R.uget d (yo + i) (hy.uset_bound h) else R.zero
  let z := if h : i < nz then R.uget d (zo + i) (hz.uset_bound h) else R.zero
  R.addDiffC v x y z c

omit F in
private theorem midStep_spec (d : A) (vo yo zo len ny nz : USize) (hv : LoopBound d vo len)
    (hy : LoopBound d yo ny) (hz : LoopBound d zo nz) (i : USize) (hi : i < len) (x c : L)
    (hc : LA.val c ≤ 3) :
    LA.val (midStep A d vo yo zo len ny nz hv hy hz i hi x c).1 +
        2 ^ LA.w * LA.val (midStep A d vo yo zo len ny nz hv hy hz i hi x c).2 +
        (if i.toNat < ny.toNat then LA.val (LA.get d (yo.toNat + i.toNat)) else 0) +
        (if i.toNat < nz.toNat then LA.val (LA.get d (zo.toNat + i.toNat)) else 0) + 2 =
      LA.val (LA.get d (vo.toNat + i.toNat)) + LA.val x + LA.val c + 2 * 2 ^ LA.w ∧
      LA.val (midStep A d vo yo zo len ny nz hv hy hz i hi x c).2 ≤ 3 := by
  have e := R.val_addDiffC (R.uget d (vo + i) (hv.uset_bound hi)) x
    (if h : i < ny then R.uget d (yo + i) (hy.uset_bound h) else R.zero)
    (if h : i < nz then R.uget d (zo + i) (hz.uset_bound h) else R.zero) c hc
  have hvv : LA.val (R.uget d (vo + i) (hv.uset_bound hi)) =
      LA.val (LA.get d (vo.toNat + i.toNat)) := by rw [R.uget_eq, hv.toNat_add hi]
  have hyy : LA.val (if h : i < ny then R.uget d (yo + i) (hy.uset_bound h) else R.zero) =
      if i.toNat < ny.toNat then LA.val (LA.get d (yo.toNat + i.toNat)) else 0 := by
    by_cases h : i < ny
    · rw [dite_eq_left h, ite_eq_left (USize.lt_iff_toNat_lt.1 h), R.uget_eq, hy.toNat_add h]
    · rw [dite_eq_right h, ite_eq_right (fun e => h (USize.lt_iff_toNat_lt.2 e)), R.val_zero]
  have hzz : LA.val (if h : i < nz then R.uget d (zo + i) (hz.uset_bound h) else R.zero) =
      if i.toNat < nz.toNat then LA.val (LA.get d (zo.toNat + i.toNat)) else 0 := by
    by_cases h : i < nz
    · rw [dite_eq_left h, ite_eq_left (USize.lt_iff_toNat_lt.1 h), R.uget_eq, hz.toNat_add h]
    · rw [dite_eq_right h, ite_eq_right (fun e => h (USize.lt_iff_toNat_lt.2 e)), R.val_zero]
  rw [hvv, hyy, hzz] at e
  exact ⟨by unfold midStep; lia, e.2⟩

/--
`d` with `t - z₀ - z₂` added to its limbs from `o + k` to `o + n - 1`, where `z₀` is in limbs
`[o, o + 2 k)` and `z₂` in `[o + 2 k, o + n)`: Karatsuba's middle term, in one pass over the window
of `t`. Outside `midOK` it writes the value of its specification.
-/
public def midW (d : A) (o k n : Nat) (t : A) : A :=
  if h : midOK d o k n t = true then
    have hm := midOK_spec h
    F.foldThen (midLen k n).toUSize
      (midStep A d (o + k).toUSize o.toUSize (o + (k + k)).toUSize (midLen k n).toUSize
        (k + k).toUSize (n - (k + k)).toUSize hm.lbv hm.lby hm.lbz) t 0 hm.lbt 0 (R.ofUSize 2)
      fun t' e c =>
        (FFT.incrAt (R.copyIn d (o + k) t' 0 (midLen k n)) o.toUSize n.toUSize
          (hm.lbd.of_size (R.size_copyIn _ _ _ _ _ (by
            have := hm.hd; have := hm.hk; unfold midLen; lia)))
          (k + midLen k n).toUSize (R.sub c (R.ofUSize 2))).1
  else
    writeNat d o n (valAt d o (k + k) +
      2 ^ (LA.w * k) * (valAt t 0 (k + k + 2) - valAt d o (k + k) -
        valAt d (o + (k + k)) (n - (k + k))) +
      2 ^ (LA.w * (k + k)) * valAt d (o + (k + k)) (n - (k + k)))

omit R F in
/-- Two numbers below `P` that differ by a multiple of `P` are equal. -/
private theorem eq_of_add_mul {X Y P a b : Nat} (hX : X < P) (hY : Y < P)
    (h : X + P * a = Y + P * b) : X = Y := by
  have := congrArg (· % P) h
  simp only [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hX, Nat.mod_eq_of_lt hY] at this
  exact this

public theorem midW_spec (d : A) (o k n : Nat) (t : A) (hd : o + n ≤ LA.size d) :
    Writes (midW d o k n t) d o n ∧
      ∀ Z₁, valAt t 0 (k + k + 2) = valAt d o (k + k) + Z₁ + valAt d (o + (k + k)) (n - (k + k)) →
        valAt d o (k + k) + 2 ^ (LA.w * k) * Z₁ +
            2 ^ (LA.w * (k + k)) * valAt d (o + (k + k)) (n - (k + k)) < 2 ^ (LA.w * n) →
        valAt (midW d o k n t) o n = valAt d o (k + k) + 2 ^ (LA.w * k) * Z₁ +
          2 ^ (LA.w * (k + k)) * valAt d (o + (k + k)) (n - (k + k)) := by
  unfold midW
  split
  case isFalse =>
    refine ⟨writes_writeNat .., fun Z₁ hT hlt => ?_⟩
    rw [valAt_writeNat _ _ _ _ hd, hT,
      show valAt d o (k + k) + Z₁ + valAt d (o + (k + k)) (n - (k + k)) - valAt d o (k + k) -
        valAt d (o + (k + k)) (n - (k + k)) = Z₁ by lia]
    exact Nat.mod_eq_of_lt hlt
  rename_i h
  have hm := midOK_spec h
  obtain ⟨e₁, e₂, e₃, e₄, e₅, e₆, e₇, e₈⟩ := hm.e
  have h₂ := hm.hk; have h₃ := hm.hn; have h₄ := hm.ht; have h₅ := hm.hk2
  have hL : midLen k n = min (n - k) (k + k + 2) := rfl
  dsimp only
  rw [F.foldThen_eq, foldUInPlaceThen]
  -- The fold over the window of `t`.
  have hm2 : LA.val (R.ofUSize 2) = 2 := by
    have h2 : (2 : USize).toNat = 2 := by
      have : 4294967296 ≤ USize.size := by cases USize.size_eq <;> lia
      rw [USize.toNat_ofNat, Nat.mod_eq_of_lt (by simp only [USize.size] at this; lia)]
    rw [R.val_ofUSize, h2]; have := four_le (R := R); exact Nat.mod_eq_of_lt (by lia)
  obtain ⟨hp₁, hp₄, -, hp₅⟩ := fold_mid (midLen k n).toUSize
    (midStep A d (o + k).toUSize o.toUSize (o + (k + k)).toUSize (midLen k n).toUSize
      (k + k).toUSize (n - (k + k)).toUSize hm.lbv hm.lby hm.lbz)
    (fun j => LA.val (LA.get d (o + k + j)))
    (fun j => if j < k + k then LA.val (LA.get d (o + j)) else 0)
    (fun j => if j < n - (k + k) then LA.val (LA.get d (o + (k + k) + j)) else 0)
    (fun j hj x c hc => by
      have := midStep_spec d _ _ _ _ _ _ hm.lbv hm.lby hm.lbz j hj x c hc
      simp only [e₁, e₂, e₃, e₅, e₆] at this
      exact this)
    t 0 hm.lbt 0 (R.ofUSize 2) (by rw [hm2]; decide)
  generalize foldUInPlace (midLen k n).toUSize
    (midStep A d (o + k).toUSize o.toUSize (o + (k + k)).toUSize (midLen k n).toUSize
      (k + k).toUSize (n - (k + k)).toUSize hm.lbv hm.lby hm.lbz) t 0 hm.lbt 0 (R.ofUSize 2) =
    p at *
  simp only [USize.toNat_zero, Nat.add_zero, Nat.sub_zero, e₄, hm2] at hp₅
  rw [wsum_get d (o + k) _ 0, wsum_pad d o (k + k) _ 0 (by rw [hL]; lia),
    wsum_pad d (o + (k + k)) (n - (k + k)) _ 0 (by rw [hL]; lia)] at hp₅
  simp only [Nat.add_zero, Nat.sub_zero] at hp₅
  -- The copy into `d`.
  have hcs : LA.size (R.copyIn d (o + k) p.1 0 (midLen k n)) = LA.size d :=
    R.size_copyIn _ _ _ _ _ (by have := hm.hd; rw [hL]; lia)
  have hc (i : Nat) : LA.get (R.copyIn d (o + k) p.1 0 (midLen k n)) i =
      if o + k ≤ i ∧ i < o + k + midLen k n then LA.get p.1 (i - (o + k)) else LA.get d i := by
    rw [R.get_copyIn _ _ _ _ _ _ (by have := hm.hd; rw [hL]; lia) (by rw [hp₁, h₄, hL]; lia),
      Nat.zero_add]
  -- The carry above the window.
  obtain ⟨a₁, a₂, a₃⟩ := FFT.incrAt_spec (R.copyIn d (o + k) p.1 0 (midLen k n)) o.toUSize
    n.toUSize (hm.lbd.of_size hcs) (k + midLen k n).toUSize (R.sub p.2 (R.ofUSize 2))
  generalize FFT.incrAt (R.copyIn d (o + k) p.1 0 (midLen k n)) o.toUSize n.toUSize _
    (k + midLen k n).toUSize (R.sub p.2 (R.ofUSize 2)) = q at *
  generalize R.copyIn d (o + k) p.1 0 (midLen k n) = d' at *
  simp only [e₁, e₇, e₈] at a₂ a₃
  refine ⟨⟨by rw [a₁, hcs], fun i hi => ?_⟩, fun Z₁ hT hW => ?_⟩
  · rw [a₂ i (by lia), hc i, ite_eq_right (by lia)]
  -- The value, from its three parts: below the window, the window, and above it.
  generalize hLL : midLen k n = L at *
  have hlo : valAt q.1 o k = valAt d o k :=
    valAt_congr _ fun i h₁ h₂ => by rw [a₂ i (by lia), hc i, ite_eq_right (by lia)]
  have hmid : valAt q.1 (o + k) L = valAt p.1 0 L := by
    have h₁ := wsum_get q.1 (o + k) L 0
    have h₂ := wsum_get p.1 0 L 0
    rw [Nat.add_zero] at h₁ h₂
    rw [← h₁, ← h₂]
    have hg : ∀ m j, j + m ≤ L → wsum LA.w (fun i => LA.val (LA.get q.1 (o + k + i))) j m =
        wsum LA.w (fun i => LA.val (LA.get p.1 (0 + i))) j m := by
      intro m
      induction m with
      | zero => intro j _; rfl
      | succ m ih =>
        intro j hj
        rw [wsum, wsum, ih (j + 1) (by lia), a₂ _ (by lia), hc, ite_eq_left (by lia),
          show o + k + j - (o + k) = 0 + j by lia]
    exact hg L 0 (by lia)
  have hhi : valAt d' (o + (k + L)) (n - (k + L)) = valAt d (o + (k + L)) (n - (k + L)) :=
    valAt_congr _ fun i h₁ h₂ => by rw [hc i, ite_eq_right (by lia)]
  rw [show o + (k + L) = o + (k + L) from rfl, hhi] at a₃
  have hsplit (a : A) : valAt a o n =
      valAt a o k + 2 ^ (LA.w * k) * (valAt a (o + k) L +
        2 ^ (LA.w * L) * valAt a (o + (k + L)) (n - (k + L))) := by
    have e : n = k + (L + (n - (k + L))) := by lia
    calc valAt a o n = valAt a o (k + (L + (n - (k + L)))) := by rw [← e]
      _ = _ := by rw [valAt_add, valAt_add, Nat.add_assoc o]
  have hsplit₂ : valAt d o n = valAt d o (k + k) +
      2 ^ (LA.w * (k + k)) * valAt d (o + (k + k)) (n - (k + k)) := by
    rw [← valAt_add, show k + k + (n - (k + k)) = n by lia]
  rw [hsplit q.1, hlo, hmid]
  have hA := hsplit d
  rw [hsplit₂] at hA
  have hPow : 2 ^ (LA.w * (k + k)) = 2 ^ (LA.w * k) * 2 ^ (LA.w * k) := by
    rw [← Nat.pow_add, ← Nat.mul_add]
  have hPN : 2 ^ (LA.w * n) = 2 ^ (LA.w * k) * (2 ^ (LA.w * L) * 2 ^ (LA.w * (n - (k + L)))) := by
    rw [← Nat.pow_add, ← Nat.pow_add, ← Nat.mul_add, ← Nat.mul_add]; congr 2; lia
  have hX := valAt_lt p.1 0 L
  have hQ : 0 < 2 ^ (LA.w * k) := Nat.two_pow_pos _
  have hlt := valAt_lt q.1 o n
  rw [hsplit q.1, hlo, hmid, hPN] at hlt
  rw [hPow] at hA hW ⊢
  rw [hPN] at hW
  generalize valAt d o k = R₀ at *
  generalize valAt d (o + k) L = V at *
  generalize valAt d o (k + k) = Z₀ at *
  generalize valAt d (o + (k + k)) (n - (k + k)) = Z₂ at *
  generalize valAt p.1 0 L = X at *
  generalize 2 ^ (LA.w * k) = Q at *
  rcases Nat.lt_or_ge L (k + k + 2) with hLt | hLe
  · -- The window ends at `n`: `t` was cut to `L` limbs, and nothing is above the window.
    have hNL : n - (k + L) = 0 := by lia
    rw [hNL, valAt_zero, Nat.mul_zero, Nat.add_zero] at hA ⊢
    have hTL := valAt_mod t 0 (Nat.le_of_lt hLt)
    rw [hTL] at hp₅
    generalize valAt t 0 (k + k + 2) = T at *
    generalize 2 ^ (LA.w * L) = P at *
    have hdm := Nat.div_add_mod T P
    have hPpos : 0 < P := by
      rcases Nat.eq_zero_or_pos P with e | e
      · rw [e] at hX; lia
      · exact e
    -- `V + Z₁` fits in the window, since the result fits in `n` limbs.
    have hVZ : V + Z₁ < P := by
      have hW' : Q * (V + Z₁) < Q * P := by
        simp only [hNL, Nat.mul_zero, Nat.pow_zero, Nat.mul_one] at hW
        have : R₀ + Q * V = Z₀ + Q * Q * Z₂ := hA.symm
        have e : Z₀ + Q * Z₁ + Q * Q * Z₂ = R₀ + Q * (V + Z₁) := by grind
        lia
      exact Nat.lt_of_mul_lt_mul_left hW'
    have hXe : X = V + Z₁ := by
      apply eq_of_add_mul hX hVZ (a := LA.val p.2 + T / P) (b := 2)
      rw [Nat.mul_add]
      generalize P * (T / P) = PT at *
      generalize T % P = TP at *
      generalize P * LA.val p.2 = Pc at *
      lia
    rw [hXe, Nat.mul_add]
    generalize Q * V = QV at *
    generalize Q * Z₁ = QZ at *
    generalize Q * Q * Z₂ = QQZ at *
    lia
  · -- The window has all of `t`: the carry out of it goes on above.
    have hLe' : L = k + k + 2 := by lia
    subst hLe'
    rw [hT] at hp₅
    generalize 2 ^ (LA.w * (k + k + 2)) = P at *
    generalize valAt q.1 (o + (k + (k + k + 2))) (n - (k + (k + k + 2))) = Hq at *
    generalize valAt d (o + (k + (k + k + 2))) (n - (k + (k + k + 2))) = H at *
    generalize 2 ^ (LA.w * (n - (k + (k + k + 2)))) = P' at *
    generalize LA.val q.2 = cout at *
    -- The carry out of the window is `2` or `3`, the true carry `0` or `1`.
    have hc23 : LA.val p.2 = 2 ∨ LA.val p.2 = 3 := by
      have : LA.val p.2 = 0 ∨ LA.val p.2 = 1 ∨ LA.val p.2 = 2 ∨ LA.val p.2 = 3 := by lia
      rcases this with e | e | e | e <;> rw [e] at hp₅ <;> first | lia | simp [e]
    have hsub : LA.val (R.sub p.2 (R.ofUSize 2)) = LA.val p.2 - 2 := by
      rw [R.val_sub, hm2]
      have := four_le (R := R)
      have := LA.val_lt p.2
      rw [show LA.val p.2 + (2 ^ LA.w - 2) = (LA.val p.2 - 2) + 2 ^ LA.w by lia, Nat.add_mod_right,
        Nat.mod_eq_of_lt (by lia)]
    rw [hsub] at a₃
    -- The value plus the carry out of `n` limbs is the product.
    have hres : R₀ + Q * (X + P * Hq) + Q * (P * P') * cout = Z₀ + Q * Z₁ + Q * Q * Z₂ := by
      have e₁ : Q * (P * P') * cout = Q * P * (P' * cout) := by
        rw [Nat.mul_assoc, Nat.mul_assoc, Nat.mul_assoc]
      have e₂ : Q * (P * H) = Q * P * H := by rw [Nat.mul_assoc]
      have e₃ : Q * (P * Hq) = Q * P * Hq := by rw [Nat.mul_assoc]
      rw [e₁, Nat.mul_add, e₃]
      rw [Nat.mul_add, e₂] at hA
      rcases hc23 with e | e <;> rw [e] at hp₅ a₃
      · have hx : X = V + Z₁ := by lia
        have ha : Q * P * Hq + Q * P * (P' * cout) = Q * P * H := by
          rw [← Nat.mul_add, a₃, Nat.sub_self, Nat.add_zero]
        rw [hx, Nat.mul_add]
        generalize Q * P * Hq = A' at *
        generalize Q * P * (P' * cout) = B at *
        generalize Q * P * H = C at *
        generalize Q * V = QV at *
        generalize Q * Z₁ = QZ at *
        generalize Q * Q * Z₂ = QQZ at *
        lia
      · have hx : X + P = V + Z₁ := by lia
        have ha : Q * P * Hq + Q * P * (P' * cout) = Q * P * H + Q * P := by
          rw [← Nat.mul_add, a₃, Nat.mul_add, Nat.mul_one]
        have hb : Q * X + Q * P = Q * V + Q * Z₁ := by
          rw [← Nat.mul_add, ← Nat.mul_add, hx]
        generalize Q * P * Hq = A' at *
        generalize Q * P * (P' * cout) = B at *
        generalize Q * P * H = C at *
        generalize Q * V = QV at *
        generalize Q * Z₁ = QZ at *
        generalize Q * Q * Z₂ = QQZ at *
        generalize Q * X = QX at *
        generalize Q * P = QP at *
        lia
    -- Both are below `βⁿ`, so the carry out is `0`.
    have hcout : cout = 0 := by
      rcases Nat.eq_zero_or_pos cout with e | e
      · exact e
      · have : Q * (P * P') ≤ Q * (P * P') * cout := Nat.le_mul_of_pos_right _ e
        generalize Q * (P * P') * cout = D at *
        generalize Q * (P * P') = E at *
        lia
    rw [hcout, Nat.mul_zero, Nat.add_zero] at hres
    exact hres

end MPN.WordArray
