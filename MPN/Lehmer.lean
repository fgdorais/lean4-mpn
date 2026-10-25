/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import MPN.Generic.Ops64

/-!
# The kernel of Lehmer's step

`mulSubMul x y a b` is `a x - b y` in one pass over the limbs, like `main`'s `mulSubMul` and GMP's
`mpn_hgcd_mul_matrix1_vector`, or `none` when it is negative: each limb adds `a xᵢ`, subtracts
`b yᵢ`, and carries a signed word (`sval`) to the next. `mulAddMul x y a b` is `a x + b y` in the
same way, for the entries of the matrices of half-gcd.
-/

open ScalarArray UInt64Array

namespace MPN

/-! ## Signed words -/

/-- The value of a word in two's complement. -/
@[expose] public def sval (s : UInt64) : Int :=
  if s.toNat < 2 ^ 63 then s.toNat else (s.toNat : Int) - 2 ^ 64

private theorem sval_of_mod (w : UInt64) (z k : Int) (h : (w.toNat : Int) - z = 2 ^ 64 * k)
    (hz : -2 ^ 63 ≤ z ∧ z < 2 ^ 63) : sval w = z := by
  have hw := w.toNat_lt
  unfold sval
  split <;> lia

private theorem sub_word (u v : UInt64) :
    ∃ k, k ≤ 1 ∧ (u - v).toNat + v.toNat = u.toNat + 2 ^ 64 * k := by
  have := u.toNat_lt; have := v.toNat_lt
  rw [UInt64.toNat_sub]
  by_cases h : v.toNat ≤ u.toNat
  · exact ⟨0, by lia, by
      rw [show 2 ^ 64 - v.toNat + u.toNat = (u.toNat - v.toNat) + 2 ^ 64 by lia, Nat.add_mod_right,
        Nat.mod_eq_of_lt (by lia)]; lia⟩
  · exact ⟨1, by lia, by rw [Nat.mod_eq_of_lt (by lia)]; lia⟩

private theorem add_word (u v : UInt64) :
    ∃ k, k ≤ 1 ∧ (u + v).toNat + 2 ^ 64 * k = u.toNat + v.toNat := by
  have := u.toNat_lt; have := v.toNat_lt
  rw [UInt64.toNat_add]
  by_cases h : u.toNat + v.toNat < 2 ^ 64
  · exact ⟨0, by lia, by rw [Nat.mod_eq_of_lt h]; try lia⟩
  · exact ⟨1, by lia, by
      rw [show u.toNat + v.toNat = (u.toNat + v.toNat - 2 ^ 64) + 2 ^ 64 by lia, Nat.add_mod_right,
        Nat.mod_eq_of_lt (by lia)]; try lia⟩

/-! ## One limb -/

/--
One limb of `a x - b y`: the low word of `a xᵢ - b yᵢ + s`, for the signed carry `s`, and the
signed carry out.
-/
@[inline, expose] public def msWord (xi yi a b s : UInt64) : UInt64 × UInt64 :=
  let pl := a * xi
  let ql := b * yi
  let d := pl - ql
  let e := d + s
  (e, UInt64.mulh a xi - UInt64.mulh b yi - UInt64.subh 0 pl ql + UInt64.addh 0 d s - (s >>> 63))

private theorem msWord_spec (xi yi a b s : UInt64) (ha : a.toNat < 2 ^ 62) (hb : b.toNat < 2 ^ 62)
    (hs : -2 ^ 62 - 2 ≤ sval s ∧ sval s ≤ 2 ^ 62 + 1) :
    ((msWord xi yi a b s).1.toNat : Int) + 2 ^ 64 * sval (msWord xi yi a b s).2 =
        a.toNat * xi.toNat - b.toNat * yi.toNat + sval s ∧
      -2 ^ 62 - 2 ≤ sval (msWord xi yi a b s).2 ∧ sval (msWord xi yi a b s).2 ≤ 2 ^ 62 + 1 := by
  have hx := xi.toNat_lt; have hy := yi.toNat_lt; have hsn := s.toNat_lt
  have hP := Nat.mul_lt_mul_of_lt_of_le ha (Nat.le_of_lt hx) (Nat.two_pow_pos _)
  have hQ := Nat.mul_lt_mul_of_lt_of_le hb (Nat.le_of_lt hy) (Nat.two_pow_pos _)
  -- The words of the products, and the bit that gives the sign of `s`.
  have hpl := Nat.div_add_mod (a.toNat * xi.toNat) (2 ^ 64)
  have hql := Nat.div_add_mod (b.toNat * yi.toNat) (2 ^ 64)
  have hneg : (s >>> 63).toNat = s.toNat / 2 ^ 63 := by
    rw [UInt64.toNat_shiftRight, Nat.shiftRight_eq_div_pow]; rfl
  simp only [msWord]
  generalize hsv : sval s = σ at hs ⊢
  have hσ : σ = s.toNat - 2 ^ 64 * (s.toNat / 2 ^ 63 : Nat) := by
    rw [← hsv]; unfold sval
    split
    · rw [Nat.div_eq_of_lt (by lia)]; lia
    · rw [show s.toNat / 2 ^ 63 = 1 by lia]; lia
  have hpw : (UInt64.mulh a xi).toNat = a.toNat * xi.toNat / 2 ^ 64 := UInt64.toNat_mulh ..
  have hqw : (UInt64.mulh b yi).toNat = b.toNat * yi.toNat / 2 ^ 64 := UInt64.toNat_mulh ..
  have hplw : (a * xi).toNat = a.toNat * xi.toNat % 2 ^ 64 := UInt64.toNat_mul ..
  have hqlw : (b * yi).toNat = b.toNat * yi.toNat % 2 ^ 64 := UInt64.toNat_mul ..
  generalize a * xi = pl at *
  generalize b * yi = ql at *
  generalize UInt64.mulh a xi = ph at *
  generalize UInt64.mulh b yi = qh at *
  generalize hPd : a.toNat * xi.toNat = P at *
  generalize hQd : b.toNat * yi.toNat = Q at *
  have hd : (pl - ql).toNat = (2 ^ 64 - ql.toNat + pl.toNat) % 2 ^ 64 := UInt64.toNat_sub ..
  generalize pl - ql = d at *
  have he : (d + s).toNat = (d.toNat + s.toNat) % 2 ^ 64 := UInt64.toNat_add ..
  have hbw : (UInt64.subh 0 pl ql).toNat = if pl.toNat < ql.toNat then 1 else 0 := by
    rw [UInt64.toNat_subh]; split <;> simp
  have hcy : (UInt64.addh 0 d s).toNat = (d.toNat + s.toNat) / 2 ^ 64 := by
    rw [UInt64.toNat_addh]; simp only [UInt64.toNat_zero, Nat.zero_add]
    exact Nat.mod_eq_of_lt (by have := d.toNat_lt; lia)
  generalize d + s = e at *
  generalize UInt64.subh 0 pl ql = bw at *
  generalize UInt64.addh 0 d s = cy at *
  -- The three exact relations of the step.
  have E1 : d.toNat + ql.toNat = pl.toNat + 2 ^ 64 * bw.toNat := by
    have := pl.toNat_lt; have := ql.toNat_lt
    split at hbw <;> lia
  have E2 : e.toNat + 2 ^ 64 * cy.toNat = d.toNat + s.toNat := by
    have := Nat.div_add_mod (d.toNat + s.toNat) (2 ^ 64); lia
  have hbw1 : bw.toNat ≤ 1 := by split at hbw <;> lia
  have hcy1 : cy.toNat ≤ 1 := by have := d.toNat_lt; lia
  have hneg1 : (s >>> 63).toNat ≤ 1 := by lia
  -- The carry out, word by word.
  obtain ⟨k₁, hk₁, w₁⟩ := sub_word ph qh
  obtain ⟨k₂, hk₂, w₂⟩ := sub_word (ph - qh) bw
  obtain ⟨k₃, hk₃, w₃⟩ := add_word (ph - qh - bw) cy
  obtain ⟨k₄, hk₄, w₄⟩ := sub_word (ph - qh - bw + cy) (s >>> 63)
  generalize ph - qh = v₁ at *
  generalize v₁ - bw = v₂ at *
  generalize v₂ + cy = v₃ at *
  generalize v₃ - s >>> 63 = w at *
  have hz := sval_of_mod w ((ph.toNat : Int) - qh.toNat - bw.toNat + cy.toNat - (s >>> 63).toNat)
    ((k₁ : Int) + k₂ - k₃ + k₄) (by push_cast; lia) (by constructor <;> lia)
  rw [hz]
  have hP' : P = 2 ^ 64 * ph.toNat + pl.toNat := by rw [hpw, hplw]; lia
  have hQ' : Q = 2 ^ 64 * qh.toNat + ql.toNat := by rw [hqw, hqlw]; lia
  have hσ' : σ = s.toNat - 2 ^ 64 * (s >>> 63).toNat := by rw [hneg]; exact hσ
  have hph : ph.toNat < 2 ^ 62 := by rw [hpw]; lia
  have hqh : qh.toNat < 2 ^ 62 := by rw [hqw]; lia
  clear hpl hql hpw hqw hplw hqlw hσ hneg hd he hcy hbw
  have hPi : (a.toNat : Int) * xi.toNat = P := by rw [← hPd]; push_cast; rfl
  have hQi : (b.toNat : Int) * yi.toNat = Q := by rw [← hQd]; push_cast; rfl
  rw [hPi, hQi]
  refine ⟨?_, by lia, by lia⟩
  lia

/-! ## The pass -/

/-- The step of `mulSubMul`: limb `j` of `a x - b y` with the signed carry `s`. -/
@[inline, expose] public def msStep (x y : UInt64Array) (a b : UInt64) (n : USize) (j : USize)
    (_h : j < n) (_z s : UInt64) : UInt64 × UInt64 :=
  msWord (Num.limbAt x j.toNat) (Num.limbAt y j.toNat) a b s

private theorem ms_spec (x y : UInt64Array) (a b : UInt64) (ha : a.toNat < 2 ^ 62)
    (hb : b.toNat < 2 ^ 62) (n : USize) (arr : UInt64Array) (rs : USize)
    (hr : LoopBound arr rs n) (j : USize) (s : UInt64)
    (hs : -2 ^ 62 - 2 ≤ sval s ∧ sval s ≤ 2 ^ 62 + 1) :
    (foldUInPlace n (msStep x y a b n) arr rs hr j s).1.size = arr.size ∧
      (∀ i, (i < rs.toNat + j.toNat ∨ rs.toNat + n.toNat ≤ i) →
        (foldUInPlace n (msStep x y a b n) arr rs hr j s).1[i]! = arr[i]!) ∧
      ((foldUInPlace n (msStep x y a b n) arr rs hr j s).1.valAt (rs.toNat + j.toNat)
          (n.toNat - j.toNat) : Int) +
          2 ^ (64 * (n.toNat - j.toNat)) *
            sval (foldUInPlace n (msStep x y a b n) arr rs hr j s).2 =
        a.toNat * x.valAt j.toNat (n.toNat - j.toNat) -
          b.toNat * y.valAt j.toNat (n.toNat - j.toNat) + sval s ∧
      -2 ^ 62 - 2 ≤ sval (foldUInPlace n (msStep x y a b n) arr rs hr j s).2 ∧
        sval (foldUInPlace n (msStep x y a b n) arr rs hr j s).2 ≤ 2 ^ 62 + 1 := by
  induction arr, hr, j, s using foldUInPlace.induct n (msStep x y a b n) rs with
  | case1 arr hr j s h p ih =>
    rw [foldUInPlace_lt _ _ _ _ _ _ _ h]
    have hj := USize.lt_iff_toNat_lt.1 h
    have hj₁ := USize.toNat_add_one_of_lt h
    have hidx := hr.toNat_add h
    obtain ⟨m₁, m₂, m₃⟩ := msWord_spec (Num.limbAt x j.toNat) (Num.limbAt y j.toNat) a b s ha hb
      hs
    obtain ⟨ih₁, ih₂, ih₃, ih₄⟩ := ih ⟨m₂, m₃⟩
    simp only [p, msStep] at ih₁ ih₂ ih₃ ih₄ ⊢
    rw [hj₁] at ih₂ ih₃
    simp only [UInt64Array.size_uset] at ih₁
    have hv := ih₂ (rs.toNat + j.toNat) (.inl (by lia))
    rw [getElem!_uset, hidx] at hv
    simp only [↓reduceIte] at hv
    refine ⟨ih₁, fun i hi => ?_, ?_, ih₄⟩
    · rw [ih₂ i (by lia), getElem!_uset]
      simp only [hidx]
      split <;> lia
    · obtain ⟨k, hk⟩ : ∃ k, n.toNat - j.toNat = k + 1 := ⟨n.toNat - j.toNat - 1, by lia⟩
      rw [show n.toNat - (j.toNat + 1) = k by lia, ← Nat.add_assoc] at ih₃
      rw [hk, UInt64Array.valAt_succ, UInt64Array.valAt_succ, UInt64Array.valAt_succ, hv,
        ← Num.limbAt_eq, ← Num.limbAt_eq, Nat.mul_succ]
      simp only [Int.natCast_add, Int.natCast_mul, Int.natCast_pow, Int.pow_add] at ih₃ m₁ ⊢
      generalize (foldUInPlace (β := UInt64) _ _ _ _ _ _ _).1.valAt _ _ = R at *
      generalize sval (foldUInPlace (β := UInt64) _ _ _ _ _ _ _).2 = c' at *
      generalize sval (msWord _ _ a b s).2 = c₁ at *
      generalize (msWord _ _ a b s).1.toNat = o at *
      generalize x.valAt _ k = X at *
      generalize y.valAt _ k = Y at *
      generalize (Num.limbAt x j.toNat).toNat = xi at *
      generalize (Num.limbAt y j.toNat).toNat = yi at *
      generalize 2 ^ (64 * k) = P at *
      generalize sval s = σ at *
      generalize a.toNat = A at *
      generalize b.toNat = B at *
      grind
  | case2 arr hr j s h =>
    rw [foldUInPlace_ge _ _ _ _ _ _ _ h]
    have : n.toNat - j.toNat = 0 := by have := USize.lt_iff_toNat_lt (a := j) (b := n); lia
    refine ⟨rfl, fun _ _ => rfl, by simp [this], hs⟩

private theorem ms_bound {n : Nat} (h : fits (n + 2) = true) :
    LoopBound (UInt64Array.replicate (n + 1) 0) 0 n.toUSize := by
  have := lt_of_fits h
  have hn : n.toUSize.toNat = n := USize.toNat_ofNat_of_lt' (by lia)
  constructor <;> simp [hn] <;> lia

/--
`a x - b y` for `a, b < 2⁶²`, or `none` when it is negative, in one pass over the limbs
(`msStep`).
-/
public def mulSubMul (x y : UInt64Array) (a b : UInt64) : Option UInt64Array :=
  let n := max x.size y.size
  if h : fits (n + 2) = true then
    foldUInPlaceThen n.toUSize (msStep x y a b n.toUSize) (UInt64Array.replicate (n + 1) 0) 0
      (ms_bound h) 0 0 fun arr _ s =>
        if s < 0x8000000000000000 then some (arr.set! n s) else none
  else if b.toNat * y.toNat ≤ a.toNat * x.toNat then
    some (ofNat (a.toNat * x.toNat - b.toNat * y.toNat))
  else none

public theorem toNat_mulSubMul (x y : UInt64Array) (a b : UInt64) (ha : a.toNat < 2 ^ 62)
    (hb : b.toNat < 2 ^ 62) (r : UInt64Array) (h : mulSubMul x y a b = some r) :
    (r.toNat : Int) = a.toNat * x.toNat - b.toNat * y.toNat := by
  unfold mulSubMul at h
  dsimp only at h
  split at h
  · rename_i hf
    have hS := lt_of_fits hf
    have hn : (max x.size y.size).toUSize.toNat = max x.size y.size :=
      USize.toNat_ofNat_of_lt' (by lia)
    rw [foldUInPlaceThen_eq] at h
    obtain ⟨f₁, -, f₃, -⟩ := ms_spec x y a b ha hb _ _ 0 (ms_bound hf) 0 0 (by simp [sval])
    simp only [USize.toNat_zero, Nat.add_zero, Nat.sub_zero, hn] at f₁ f₃
    rw [Num.valAt_ge x _ (by lia), Num.valAt_ge y _ (by lia)] at f₃
    generalize foldUInPlace _ (msStep x y a b _) _ 0 _ 0 0 = F at f₁ f₃ h
    split at h
    · rename_i hs
      rw [Option.some.injEq] at h
      subst h
      have hsv : sval F.2 = F.2.toNat := by
        unfold sval; rw [if_pos (by rw [UInt64.lt_iff_toNat_lt] at hs; simpa using hs)]
      have hsz : F.1.size = max x.size y.size + 1 := by rw [f₁]; simp
      rw [toNat_eq_valAt, size_set!, hsz, UInt64Array.valAt_add, valAt_one, Nat.zero_add,
        getElem!_set!_self _ _ _ (by lia),
        valAt_congr (b := F.1) _ fun i _ hi => getElem!_set!_of_ne _ _ (by lia)]
      have h0 : sval 0 = 0 := by simp [sval]
      rw [hsv, h0] at f₃
      rw [Int.natCast_add, Int.natCast_mul, Int.natCast_pow]
      lia
    · exact absurd h (by simp)
  · split at h
    · rename_i _ hle
      rw [Option.some.injEq] at h
      subst h
      rw [toNat_ofNat, Int.ofNat_sub hle, Int.natCast_mul, Int.natCast_mul]
    · exact absurd h (by simp)

/-! ## Sums -/

/-- One limb of `a x + b y`: the low word of `a xᵢ + b yᵢ + c`, and the carry out. -/
@[inline, expose] public def maWord (xi yi a b c : UInt64) : UInt64 × UInt64 :=
  let pl := a * xi
  let ql := b * yi
  let t := pl + ql
  (t + c, UInt64.addh (UInt64.addh (UInt64.mulh a xi + UInt64.mulh b yi) pl ql) t c)

private theorem maWord_spec (xi yi a b c : UInt64) (ha : a.toNat < 2 ^ 62) (hb : b.toNat < 2 ^ 62)
    (hc : c.toNat ≤ 2 ^ 63) :
    (maWord xi yi a b c).1.toNat + 2 ^ 64 * (maWord xi yi a b c).2.toNat =
        a.toNat * xi.toNat + b.toNat * yi.toNat + c.toNat ∧
      (maWord xi yi a b c).2.toNat ≤ 2 ^ 63 := by
  have hx := xi.toNat_lt; have hy := yi.toNat_lt
  have hP := Nat.mul_lt_mul_of_lt_of_le ha (Nat.le_of_lt hx) (Nat.two_pow_pos _)
  have hQ := Nat.mul_lt_mul_of_lt_of_le hb (Nat.le_of_lt hy) (Nat.two_pow_pos _)
  have hpl := Nat.div_add_mod (a.toNat * xi.toNat) (2 ^ 64)
  have hql := Nat.div_add_mod (b.toNat * yi.toNat) (2 ^ 64)
  simp only [maWord]
  have hpw : (UInt64.mulh a xi).toNat = a.toNat * xi.toNat / 2 ^ 64 := UInt64.toNat_mulh ..
  have hqw : (UInt64.mulh b yi).toNat = b.toNat * yi.toNat / 2 ^ 64 := UInt64.toNat_mulh ..
  have hplw : (a * xi).toNat = a.toNat * xi.toNat % 2 ^ 64 := UInt64.toNat_mul ..
  have hqlw : (b * yi).toNat = b.toNat * yi.toNat % 2 ^ 64 := UInt64.toNat_mul ..
  generalize a * xi = pl at *
  generalize b * yi = ql at *
  generalize UInt64.mulh a xi = ph at *
  generalize UInt64.mulh b yi = qh at *
  generalize a.toNat * xi.toNat = P at *
  generalize b.toNat * yi.toNat = Q at *
  have hph : ph.toNat < 2 ^ 62 := by rw [hpw]; lia
  have hqh : qh.toNat < 2 ^ 62 := by rw [hqw]; lia
  have h₁ : (ph + qh).toNat = ph.toNat + qh.toNat := by
    rw [UInt64.toNat_add, Nat.mod_eq_of_lt (by lia)]
  have ht : (pl + ql).toNat = (pl.toNat + ql.toNat) % 2 ^ 64 := UInt64.toNat_add ..
  have hk₁ := Nat.div_add_mod (pl.toNat + ql.toNat) (2 ^ 64)
  have hk₁' : (pl.toNat + ql.toNat) / 2 ^ 64 ≤ 1 := by
    have := pl.toNat_lt; have := ql.toNat_lt; lia
  have h₂ : (UInt64.addh (ph + qh) pl ql).toNat = ph.toNat + qh.toNat +
      (pl.toNat + ql.toNat) / 2 ^ 64 := by
    rw [UInt64.toNat_addh, h₁, Nat.mod_eq_of_lt (by lia)]
  generalize pl + ql = t at *
  have he : (t + c).toNat = (t.toNat + c.toNat) % 2 ^ 64 := UInt64.toNat_add ..
  have hk₂ := Nat.div_add_mod (t.toNat + c.toNat) (2 ^ 64)
  have hk₂' : (t.toNat + c.toNat) / 2 ^ 64 ≤ 1 := by have := t.toNat_lt; lia
  have h₃ : (UInt64.addh (UInt64.addh (ph + qh) pl ql) t c).toNat = ph.toNat + qh.toNat +
      (pl.toNat + ql.toNat) / 2 ^ 64 + (t.toNat + c.toNat) / 2 ^ 64 := by
    rw [UInt64.toNat_addh, h₂, Nat.mod_eq_of_lt (by lia)]
  rw [h₃, he]
  generalize (pl.toNat + ql.toNat) / 2 ^ 64 = k₁ at *
  generalize (t.toNat + c.toNat) / 2 ^ 64 = k₂ at *
  have hP' : P = 2 ^ 64 * ph.toNat + pl.toNat := by rw [hpw, hplw]; lia
  have hQ' : Q = 2 ^ 64 * qh.toNat + ql.toNat := by rw [hqw, hqlw]; lia
  rw [ht] at hk₂ he
  constructor
  · lia
  · -- `2⁶⁴ (carry) ≤ P + Q + c < 2¹²⁷ + 2⁶³`.
    have : 2 ^ 64 * (ph.toNat + qh.toNat + k₁ + k₂) ≤ P + Q + c.toNat := by lia
    lia

/-- The step of `mulAddMul`: limb `j` of `a x + b y` with the carry `c`. -/
@[inline, expose] public def maStep (x y : UInt64Array) (a b : UInt64) (n : USize) (j : USize)
    (_h : j < n) (_z c : UInt64) : UInt64 × UInt64 :=
  maWord (Num.limbAt x j.toNat) (Num.limbAt y j.toNat) a b c

private theorem ma_spec (x y : UInt64Array) (a b : UInt64) (ha : a.toNat < 2 ^ 62)
    (hb : b.toNat < 2 ^ 62) (n : USize) (arr : UInt64Array) (rs : USize)
    (hr : LoopBound arr rs n) (j : USize) (c : UInt64) (hc : c.toNat ≤ 2 ^ 63) :
    (foldUInPlace n (maStep x y a b n) arr rs hr j c).1.size = arr.size ∧
      (∀ i, (i < rs.toNat + j.toNat ∨ rs.toNat + n.toNat ≤ i) →
        (foldUInPlace n (maStep x y a b n) arr rs hr j c).1[i]! = arr[i]!) ∧
      (foldUInPlace n (maStep x y a b n) arr rs hr j c).1.valAt (rs.toNat + j.toNat)
          (n.toNat - j.toNat) +
          2 ^ (64 * (n.toNat - j.toNat)) *
            (foldUInPlace n (maStep x y a b n) arr rs hr j c).2.toNat =
        a.toNat * x.valAt j.toNat (n.toNat - j.toNat) +
          b.toNat * y.valAt j.toNat (n.toNat - j.toNat) + c.toNat ∧
      (foldUInPlace n (maStep x y a b n) arr rs hr j c).2.toNat ≤ 2 ^ 63 := by
  induction arr, hr, j, c using foldUInPlace.induct n (maStep x y a b n) rs with
  | case1 arr hr j c h p ih =>
    rw [foldUInPlace_lt _ _ _ _ _ _ _ h]
    have hj := USize.lt_iff_toNat_lt.1 h
    have hj₁ := USize.toNat_add_one_of_lt h
    have hidx := hr.toNat_add h
    obtain ⟨m₁, m₂⟩ := maWord_spec (Num.limbAt x j.toNat) (Num.limbAt y j.toNat) a b c ha hb hc
    obtain ⟨ih₁, ih₂, ih₃, ih₄⟩ := ih m₂
    simp only [p, maStep] at ih₁ ih₂ ih₃ ih₄ ⊢
    rw [hj₁] at ih₂ ih₃
    simp only [UInt64Array.size_uset] at ih₁
    have hv := ih₂ (rs.toNat + j.toNat) (.inl (by lia))
    rw [getElem!_uset, hidx] at hv
    simp only [↓reduceIte] at hv
    refine ⟨ih₁, fun i hi => ?_, ?_, ih₄⟩
    · rw [ih₂ i (by lia), getElem!_uset]
      simp only [hidx]
      split <;> lia
    · obtain ⟨k, hk⟩ : ∃ k, n.toNat - j.toNat = k + 1 := ⟨n.toNat - j.toNat - 1, by lia⟩
      rw [show n.toNat - (j.toNat + 1) = k by lia, ← Nat.add_assoc] at ih₃
      rw [hk, UInt64Array.valAt_succ, UInt64Array.valAt_succ, UInt64Array.valAt_succ, hv,
        ← Num.limbAt_eq, ← Num.limbAt_eq, Nat.mul_succ, Nat.pow_add]
      generalize (foldUInPlace (β := UInt64) _ _ _ _ _ _ _).1.valAt _ _ = R at *
      generalize (foldUInPlace (β := UInt64) _ _ _ _ _ _ _).2.toNat = c' at *
      generalize (maWord _ _ a b c).2.toNat = c₁ at *
      generalize (maWord _ _ a b c).1.toNat = o at *
      generalize x.valAt _ k = X at *
      generalize y.valAt _ k = Y at *
      generalize (Num.limbAt x j.toNat).toNat = xi at *
      generalize (Num.limbAt y j.toNat).toNat = yi at *
      generalize 2 ^ (64 * k) = P at *
      generalize a.toNat = A at *
      generalize b.toNat = B at *
      grind
  | case2 arr hr j c h =>
    rw [foldUInPlace_ge _ _ _ _ _ _ _ h]
    have : n.toNat - j.toNat = 0 := by have := USize.lt_iff_toNat_lt (a := j) (b := n); lia
    refine ⟨rfl, fun _ _ => rfl, by simp [this], hc⟩

/-- `a x + b y` for `a, b < 2⁶²`, in one pass over the limbs (`maStep`), in `max` sizes `+ 1`. -/
public def mulAddMul (x y : UInt64Array) (a b : UInt64) : UInt64Array :=
  let n := max x.size y.size
  if h : fits (n + 2) = true then
    foldUInPlaceThen n.toUSize (maStep x y a b n.toUSize) (UInt64Array.replicate (n + 1) 0) 0
      (ms_bound h) 0 0 fun arr _ c => arr.set! n c
  else ofNat (a.toNat * x.toNat + b.toNat * y.toNat)

public theorem toNat_mulAddMul (x y : UInt64Array) (a b : UInt64) (ha : a.toNat < 2 ^ 62)
    (hb : b.toNat < 2 ^ 62) :
    (mulAddMul x y a b).toNat = a.toNat * x.toNat + b.toNat * y.toNat := by
  unfold mulAddMul
  dsimp only
  split
  · rename_i hf
    have hS := lt_of_fits hf
    have hn : (max x.size y.size).toUSize.toNat = max x.size y.size :=
      USize.toNat_ofNat_of_lt' (by lia)
    rw [foldUInPlaceThen_eq]
    obtain ⟨f₁, -, f₃, -⟩ := ma_spec x y a b ha hb _ _ 0 (ms_bound hf) 0 0 (by simp)
    simp only [USize.toNat_zero, Nat.add_zero, Nat.sub_zero, hn] at f₁ f₃
    rw [Num.valAt_ge x _ (by lia), Num.valAt_ge y _ (by lia)] at f₃
    generalize foldUInPlace _ (maStep x y a b _) _ 0 _ 0 0 = F at f₁ f₃
    have hsz : F.1.size = max x.size y.size + 1 := by rw [f₁]; simp
    rw [toNat_eq_valAt, size_set!, hsz, UInt64Array.valAt_add, valAt_one, Nat.zero_add,
      getElem!_set!_self _ _ _ (by lia),
      valAt_congr (b := F.1) _ fun i _ hi => getElem!_set!_of_ne _ _ (by lia)]
    simp only [UInt64.toNat_zero, Nat.add_zero] at f₃
    lia
  · exact toNat_ofNat _

end MPN
