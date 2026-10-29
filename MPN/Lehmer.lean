/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import MPN.Generic.Ops64
public import MPN.LinComb

/-!
# The kernel of Lehmer's step

`mulSubMul x y a b` is `a x - b y` in one pass over the limbs, `main`'s `LinComb.mulSubMul` on
`UInt64Array`, like GMP's `mpn_hgcd_mul_matrix1_vector`, or `none` when it is negative: each limb
adds `a xᵢ`, subtracts `b yᵢ`, and carries a signed word (`sval`) to the next (`msWord`).
`mulAddMul x y a b` is `a x + b y` in the same way (`maWord`), for the entries of the matrices of
half-gcd. The steps and their values are the instance `linComb64` of `main`'s `LinCombOps`.
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
    (_hs : -2 ^ 62 - 2 ≤ sval s ∧ sval s ≤ 2 ^ 62 + 1) :
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
  generalize hsv : sval s = σ at _hs ⊢
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

/-! ## The passes -/

/-- The steps of `main`'s linear combinations on `UInt64Array`, by `msWord` and `maWord`. -/
public instance linComb64 : LinCombOps UInt64Array UInt64 where
  cb := 62
  cb_lt := by decide
  zeros n := UInt64Array.replicate n 0
  size_zeros n := UInt64Array.size_replicate ..
  val_get_ge a i h := by
    show a[i]!.toNat = 0
    rw [getElem!_neg a i (Nat.not_lt.2 h)]; rfl
  limb := Num.limbAt
  val_limb a i := congrArg UInt64.toNat (Num.limbAt_eq a i)
  maC := maWord
  cOK c := c.toNat ≤ 2 ^ 63
  cOK_zero := by decide
  val_maC xi yi a b c ha hb hc := by
    exact maWord_spec xi yi a b c ha hb hc
  msC := msWord
  sv := sval
  sOK s := -2 ^ 62 - 2 ≤ sval s ∧ sval s ≤ 2 ^ 62 + 1
  s0 := 0
  sOK_s0 := by simp [sval]
  sv_s0 := by simp [sval]
  val_msC xi yi a b s ha hb hs := by
    exact msWord_spec xi yi a b s ha hb hs
  sNeg s := !decide (s < 0x8000000000000000)
  sNeg_iff s _ := by
    have := s.toNat_lt
    simp only [Bool.not_eq_true', decide_eq_false_iff_not, UInt64.lt_iff_toNat_lt,
      UInt64.reduceToNat, Nat.not_lt, sval]
    split <;> lia
  sTop s := s
  val_sTop s _ hs := by
    show (s.toNat : Int) = sval s
    have := s.toNat_lt
    by_cases h : s.toNat < 2 ^ 63
    · simp [sval, h]
    · exfalso
      simp only [sval, h, ↓reduceIte] at hs
      lia

/--
`a x - b y` for `a, b < 2⁶²`, or `none` when it is negative, in one pass over the limbs: `main`'s
`LinComb.mulSubMul`.
-/
public def mulSubMul (x y : UInt64Array) (a b : UInt64) : Option UInt64Array :=
  let p := LinComb.mulSubMul x y a b
  if p.2 then none else some p.1

public theorem toNat_mulSubMul (x y : UInt64Array) (a b : UInt64) (ha : a.toNat < 2 ^ 62)
    (hb : b.toNat < 2 ^ 62) (r : UInt64Array) (h : mulSubMul x y a b = some r) :
    (r.toNat : Int) = a.toNat * x.toNat - b.toNat * y.toNat := by
  unfold mulSubMul at h
  obtain ⟨s₁, s₂, -⟩ := LinComb.mulSubMul_spec x y a b ha hb
  dsimp only at h
  split at h
  · exact absurd h (by simp)
  · rename_i hn
    rw [Option.some.injEq] at h
    subst h
    have e := s₂ (by simpa using hn)
    have e' : (LinComb.mulSubMul x y a b).1.toNat + b.toNat * y.toNat = a.toNat * x.toNat := by
      rw [toNat_eq_valAt, show (LinComb.mulSubMul x y a b).1.size = max x.size y.size + 1 from s₁,
        toNat_eq_valAt x, toNat_eq_valAt y]
      exact e
    have : ((LinComb.mulSubMul x y a b).1.toNat : Int) + b.toNat * y.toNat = a.toNat * x.toNat := by
      exact_mod_cast e'
    lia

/-- `a x + b y` for `a, b < 2⁶²`, in one pass over the limbs, in `max` sizes `+ 1`: `main`'s
`LinComb.mulAddMul`. -/
public def mulAddMul (x y : UInt64Array) (a b : UInt64) : UInt64Array :=
  LinComb.mulAddMul x y a b

public theorem toNat_mulAddMul (x y : UInt64Array) (a b : UInt64) (ha : a.toNat < 2 ^ 62)
    (hb : b.toNat < 2 ^ 62) :
    (mulAddMul x y a b).toNat = a.toNat * x.toNat + b.toNat * y.toNat := by
  obtain ⟨s₁, s₂⟩ := LinComb.mulAddMul_spec x y a b ha hb
  rw [mulAddMul, toNat_eq_valAt, show (LinComb.mulAddMul x y a b).size = _ from s₁,
    toNat_eq_valAt x, toNat_eq_valAt y]
  exact s₂

end MPN
