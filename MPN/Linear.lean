/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import MPN.AddSub
public import MPN.Mul.Basecase

/-!
# Linear passes for the Toom methods

All in place on the limbs of a slice `r`:

* `addMulInto r b x` and `subMulInto r b x` add `b * x` to `r` and subtract it, propagating the
  carry or borrow to the end of `r`, like `mpn_addmul_1` and `mpn_submul_1` followed by
  `mpn_add_1` and `mpn_sub_1`;
* `shl63Into r` multiplies `r` by `2⁶³`, which divides an even value by `2` when read from the
  next limb on;
* `divExact3Into r` divides `r` by `3`, exactly when `3` divides it, by multiplying by the inverse
  of `3` modulo `2⁶⁴`, like `mpn_divexact_by3`.
-/

open ScalarArray UInt64Array

namespace MPN

/-! ## Adding and subtracting a multiple -/

private theorem mulInto_bound (r : USlice) (arr : UInt64Array) (h : arr.size = r.array.size) :
    LoopBound arr r.start r.size := by
  have := r.loopBound (USize.le_iff_toNat_le.2 (Nat.le_refl r.size.toNat))
  simp only [LoopBound, h] at this ⊢
  exact this

/--
Adds `b * x` to the limbs of `r` and returns the carry out, like `mpn_addmul_1` followed by
`mpn_add_1` with the result in place. It requires `b.size ≤ r.size`.
-/
public def addMulInto (r b : USlice) (x : UInt64) : UInt64Array × UInt64 :=
  let p := addMul1Loop r.array r.start b (min b.size r.size) (USize.min_le_left ..)
    (r.loopBound (USize.min_le_right ..)) x 0 0
  add1IntoLoop p.1 r.start r.size (mulInto_bound r p.1 (addMul1Loop_spec ..).1)
    (min b.size r.size) p.2

@[simp] public theorem size_addMulInto (r b : USlice) (x : UInt64) :
    (addMulInto r b x).1.size = r.array.size := by
  rw [addMulInto, (add1IntoLoop_spec ..).1, (addMul1Loop_spec ..).1]

/-- `addMulInto` leaves the limbs of `r` outside the slice unchanged. -/
public theorem getElem!_addMulInto (r b : USlice) (x : UInt64) (i : Nat)
    (hi : i < r.start.toNat ∨ r.start.toNat + r.size.toNat ≤ i) :
    (addMulInto r b x).1[i]! = r.array[i]! := by
  have hm := USize.toNat_min b.size r.size
  rw [addMulInto, (add1IntoLoop_spec ..).2.1 i (by lia), (addMul1Loop_spec ..).2.1 i
    (by rw [hm, USize.toNat_zero]; lia)]

public theorem valAt_addMulInto (r b : USlice) (x : UInt64) (hb : b.size ≤ r.size) :
    (addMulInto r b x).1.valAt r.start.toNat r.size.toNat +
        2 ^ (64 * r.size.toNat) * (addMulInto r b x).2.toNat =
      r.array.valAt r.start.toNat r.size.toNat + b.toNat * x.toNat := by
  have h₁ := USize.le_iff_toNat_le.1 hb
  have hm : (min b.size r.size).toNat = b.size.toNat := by rw [USize.toNat_min]; lia
  obtain ⟨hN₁, hN₂, hN⟩ := addMul1Loop_spec r.array r.start b _ (USize.min_le_left ..)
    (r.loopBound (USize.min_le_right ..)) x 0 0
  simp only [USize.toNat_zero, Nat.add_zero, Nat.sub_zero, hm, UInt64.toNat_zero] at hN hN₂
  obtain ⟨-, h₃, h₄⟩ := add1IntoLoop_spec _ r.start r.size (mulInto_bound r _ hN₁)
    (min b.size r.size) (addMul1Loop r.array r.start b _ (USize.min_le_left ..)
      (r.loopBound (USize.min_le_right ..)) x 0 0).2
  rw [hm] at h₄ h₃
  -- The limbs above `b` are still those of `r` when the carry reaches them.
  have h₆ : (addMul1Loop r.array r.start b _ (USize.min_le_left ..)
      (r.loopBound (USize.min_le_right ..)) x 0 0).1.valAt (r.start.toNat + b.size.toNat)
        (r.size.toNat - b.size.toNat) =
      r.array.valAt (r.start.toNat + b.size.toNat) (r.size.toNat - b.size.toNat) :=
    UInt64Array.valAt_congr _ fun i hi _ => hN₂ i (by lia)
  rw [h₆] at h₄
  have h₅ : (addMulInto r b x).1.valAt r.start.toNat b.size.toNat =
      (addMul1Loop r.array r.start b _ (USize.min_le_left ..)
        (r.loopBound (USize.min_le_right ..)) x 0 0).1.valAt r.start.toNat b.size.toNat :=
    UInt64Array.valAt_congr _ fun i _ hi => h₃ i (by lia)
  rw [addMulInto] at h₅ ⊢
  obtain ⟨k, hk⟩ : ∃ k, r.size.toNat = b.size.toNat + k := ⟨r.size.toNat - b.size.toNat, by lia⟩
  rw [show r.size.toNat - b.size.toNat = k by lia] at h₄
  rw [USlice.toNat_eq_valAt, hk, UInt64Array.valAt_add, UInt64Array.valAt_add, h₅, Nat.mul_add,
    Nat.pow_add]
  generalize (add1IntoLoop _ _ _ _ _ _).1.valAt _ _ = R at *
  generalize (add1IntoLoop _ _ _ _ _ _).2.toNat = c' at *
  generalize (addMul1Loop _ _ _ _ _ _ _ _ _).1.valAt _ _ = L at *
  generalize (addMul1Loop _ _ _ _ _ _ _ _ _).2.toNat = c₁ at *
  generalize r.array.valAt _ k = R₀ at *
  generalize r.array.valAt _ b.size.toNat = L₀ at *
  generalize b.array.valAt _ _ = B at *
  generalize 2 ^ (64 * b.size.toNat) = P at *
  generalize 2 ^ (64 * k) = Q at *
  grind

/--
Subtracts `b * x` from the limbs of `r` and returns the borrow out, like `mpn_submul_1` followed
by `mpn_sub_1` with the result in place. It requires `b.size ≤ r.size`.
-/
public def subMulInto (r b : USlice) (x : UInt64) : UInt64Array × UInt64 :=
  let p := subMul1Loop r.array r.start b (min b.size r.size) (USize.min_le_left ..)
    (r.loopBound (USize.min_le_right ..)) x 0 0
  sub1IntoLoop p.1 r.start r.size (mulInto_bound r p.1 (subMul1Loop_spec ..).1)
    (min b.size r.size) p.2

@[simp] public theorem size_subMulInto (r b : USlice) (x : UInt64) :
    (subMulInto r b x).1.size = r.array.size := by
  rw [subMulInto, (sub1IntoLoop_spec ..).1, (subMul1Loop_spec ..).1]

/-- `subMulInto` leaves the limbs of `r` outside the slice unchanged. -/
public theorem getElem!_subMulInto (r b : USlice) (x : UInt64) (i : Nat)
    (hi : i < r.start.toNat ∨ r.start.toNat + r.size.toNat ≤ i) :
    (subMulInto r b x).1[i]! = r.array[i]! := by
  have hm := USize.toNat_min b.size r.size
  rw [subMulInto, (sub1IntoLoop_spec ..).2.1 i (by lia), (subMul1Loop_spec ..).2.1 i
    (by rw [hm, USize.toNat_zero]; lia)]

public theorem valAt_subMulInto (r b : USlice) (x : UInt64) (hb : b.size ≤ r.size) :
    (subMulInto r b x).1.valAt r.start.toNat r.size.toNat + b.toNat * x.toNat =
      r.array.valAt r.start.toNat r.size.toNat +
        2 ^ (64 * r.size.toNat) * (subMulInto r b x).2.toNat := by
  have h₁ := USize.le_iff_toNat_le.1 hb
  have hm : (min b.size r.size).toNat = b.size.toNat := by rw [USize.toNat_min]; lia
  obtain ⟨hN₁, hN₂, hN⟩ := subMul1Loop_spec r.array r.start b _ (USize.min_le_left ..)
    (r.loopBound (USize.min_le_right ..)) x 0 0
  simp only [USize.toNat_zero, Nat.add_zero, Nat.sub_zero, hm, UInt64.toNat_zero] at hN hN₂
  obtain ⟨-, h₃, h₄⟩ := sub1IntoLoop_spec _ r.start r.size (mulInto_bound r _ hN₁)
    (min b.size r.size) (subMul1Loop r.array r.start b _ (USize.min_le_left ..)
      (r.loopBound (USize.min_le_right ..)) x 0 0).2
  rw [hm] at h₄ h₃
  -- The limbs above `b` are still those of `r` when the borrow reaches them.
  have h₆ : (subMul1Loop r.array r.start b _ (USize.min_le_left ..)
      (r.loopBound (USize.min_le_right ..)) x 0 0).1.valAt (r.start.toNat + b.size.toNat)
        (r.size.toNat - b.size.toNat) =
      r.array.valAt (r.start.toNat + b.size.toNat) (r.size.toNat - b.size.toNat) :=
    UInt64Array.valAt_congr _ fun i hi _ => hN₂ i (by lia)
  rw [h₆] at h₄
  have h₅ : (subMulInto r b x).1.valAt r.start.toNat b.size.toNat =
      (subMul1Loop r.array r.start b _ (USize.min_le_left ..)
        (r.loopBound (USize.min_le_right ..)) x 0 0).1.valAt r.start.toNat b.size.toNat :=
    UInt64Array.valAt_congr _ fun i _ hi => h₃ i (by lia)
  rw [subMulInto] at h₅ ⊢
  obtain ⟨k, hk⟩ : ∃ k, r.size.toNat = b.size.toNat + k := ⟨r.size.toNat - b.size.toNat, by lia⟩
  rw [show r.size.toNat - b.size.toNat = k by lia] at h₄
  rw [USlice.toNat_eq_valAt, hk, UInt64Array.valAt_add, UInt64Array.valAt_add, h₅, Nat.mul_add,
    Nat.pow_add]
  generalize (sub1IntoLoop _ _ _ _ _ _).1.valAt _ _ = R at *
  generalize (sub1IntoLoop _ _ _ _ _ _).2.toNat = c' at *
  generalize (subMul1Loop _ _ _ _ _ _ _ _ _).1.valAt _ _ = L at *
  generalize (subMul1Loop _ _ _ _ _ _ _ _ _).2.toNat = c₁ at *
  generalize r.array.valAt _ k = R₀ at *
  generalize r.array.valAt _ b.size.toNat = L₀ at *
  generalize b.array.valAt _ _ = B at *
  generalize 2 ^ (64 * b.size.toNat) = P at *
  generalize 2 ^ (64 * k) = Q at *
  grind

/-! ## Halving -/

/-- The step of `shl63Into`: limb `x` times `2⁶³`, plus the bit carried in, and the bits out. -/
@[inline, expose] public def shl63Step (n : USize) (j : USize) (_h : j < n) (x c : UInt64) :
    UInt64 × UInt64 :=
  ((x <<< 63) + c, x >>> 1)

private theorem shl63Step_spec (n j : USize) (h : j < n) (x c : UInt64) (hc : c.toNat < 2 ^ 63) :
    (shl63Step n j h x c).1.toNat + 2 ^ 64 * (shl63Step n j h x c).2.toNat =
      x.toNat * 2 ^ 63 + c.toNat ∧ (shl63Step n j h x c).2.toNat < 2 ^ 63 := by
  have := x.toNat_lt
  simp only [shl63Step, UInt64.toNat_add, UInt64.toNat_shiftLeft, UInt64.toNat_shiftRight,
    UInt64.reduceToNat, Nat.reduceMod, Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow]
  generalize x.toNat = x at *
  generalize c.toNat = c at *
  constructor <;> lia

private theorem shl63_spec (n : USize) (arr : UInt64Array) (rs : USize) (hr : LoopBound arr rs n)
    (j : USize) (c : UInt64) (hc : c.toNat < 2 ^ 63) :
    (foldUInPlace n (shl63Step n) arr rs hr j c).1.size = arr.size ∧
      (∀ i, (i < rs.toNat + j.toNat ∨ rs.toNat + n.toNat ≤ i) →
        (foldUInPlace n (shl63Step n) arr rs hr j c).1[i]! = arr[i]!) ∧
      (foldUInPlace n (shl63Step n) arr rs hr j c).1.valAt (rs.toNat + j.toNat)
          (n.toNat - j.toNat) +
          2 ^ (64 * (n.toNat - j.toNat)) * (foldUInPlace n (shl63Step n) arr rs hr j c).2.toNat =
        arr.valAt (rs.toNat + j.toNat) (n.toNat - j.toNat) * 2 ^ 63 + c.toNat := by
  induction arr, hr, j, c using foldUInPlace.induct n (shl63Step n) rs with
  | case1 arr hr j c h p ih =>
    rw [foldUInPlace_lt _ _ _ _ _ _ _ h]
    have hj := USize.lt_iff_toNat_lt.1 h
    have hj₁ := USize.toNat_add_one_of_lt h
    have hidx := hr.toNat_add h
    have hs := shl63Step_spec n j h (arr.uget (rs + j) (hr.uset_bound h)) c hc
    obtain ⟨ih₁, ih₂, ih₃⟩ := ih hs.2
    simp only [p] at ih₁ ih₂ ih₃
    rw [hj₁] at ih₂ ih₃
    simp only [UInt64Array.size_uset] at ih₁
    have hv := ih₂ (rs.toNat + j.toNat) (.inl (by lia))
    rw [getElem!_uset, hidx] at hv
    simp only [↓reduceIte] at hv
    have hx : arr.uget (rs + j) (hr.uset_bound h) = arr[rs.toNat + j.toNat]! := by
      rw [uget_eq_getElem!, hidx]
    refine ⟨ih₁, fun i hi => ?_, ?_⟩
    · rw [ih₂ i (by lia), getElem!_uset]
      simp only [hidx]
      split <;> lia
    · rw [valAt_uset_of _ _ _ _ _ _ (.inl (by rw [hidx]; lia))] at ih₃
      obtain ⟨k, hk⟩ : ∃ k, n.toNat - j.toNat = k + 1 := ⟨n.toNat - j.toNat - 1, by lia⟩
      rw [show n.toNat - (j.toNat + 1) = k by lia, ← Nat.add_assoc] at ih₃
      rw [hk, UInt64Array.valAt_succ, UInt64Array.valAt_succ, hv, ← hx, Nat.mul_succ, Nat.pow_add]
      have hs1 := hs.1
      generalize (foldUInPlace (β := UInt64) _ _ _ _ _ _ _).1.valAt _ _ = R at *
      generalize (foldUInPlace (β := UInt64) _ _ _ _ _ _ _).2.toNat = c' at *
      generalize (shl63Step n j h _ c).2.toNat = c₁ at *
      generalize (shl63Step n j h _ c).1.toNat = s at *
      generalize arr.valAt _ k = R₀ at *
      generalize (arr.uget (rs + j) _).toNat = x at *
      generalize 2 ^ (64 * k) = P at *
      grind
  | case2 arr hr j c h =>
    rw [foldUInPlace_ge _ _ _ _ _ _ _ h]
    have : n.toNat - j.toNat = 0 := by have := USize.lt_iff_toNat_lt (a := j) (b := n); lia
    simp [this]

/--
Multiplies the limbs of `r` by `2⁶³` and returns the bits out, the top limb of the product. An even
value that fits in all but the last limb of `r` ends up halved in the limbs from the second on.
-/
public def shl63Into (r : USlice) : UInt64Array × UInt64 :=
  foldUInPlaceThen r.size (shl63Step r.size) r.array r.start
    (r.loopBound (USize.le_iff_toNat_le.2 (Nat.le_refl _))) 0 0 fun arr _ c => (arr, c)

@[simp] public theorem size_shl63Into (r : USlice) : (shl63Into r).1.size = r.array.size := by
  rw [shl63Into, foldUInPlaceThen_eq]
  exact (shl63_spec _ _ _ _ 0 0 (by simp)).1

/-- `shl63Into` leaves the limbs of `r` outside the slice unchanged. -/
public theorem getElem!_shl63Into (r : USlice) (i : Nat)
    (hi : i < r.start.toNat ∨ r.start.toNat + r.size.toNat ≤ i) :
    (shl63Into r).1[i]! = r.array[i]! := by
  rw [shl63Into, foldUInPlaceThen_eq]
  exact (shl63_spec _ _ _ _ 0 0 (by simp)).2.1 i (by rw [USize.toNat_zero]; lia)

public theorem valAt_shl63Into (r : USlice) :
    (shl63Into r).1.valAt r.start.toNat r.size.toNat +
        2 ^ (64 * r.size.toNat) * (shl63Into r).2.toNat =
      r.array.valAt r.start.toNat r.size.toNat * 2 ^ 63 := by
  rw [shl63Into, foldUInPlaceThen_eq]
  simpa using (shl63_spec _ _ _ _ 0 0 (by simp)).2.2

/--
Halving: an even value below `2^(64 (n - 1))` is halved in the limbs of `r` from the second on.
-/
public theorem valAt_shl63Into_half (r : USlice) (h₀ : 0 < r.size.toNat)
    (heven : r.array.valAt r.start.toNat r.size.toNat % 2 = 0)
    (hlt : r.array.valAt r.start.toNat r.size.toNat < 2 ^ (64 * (r.size.toNat - 1))) :
    (shl63Into r).1.valAt (r.start.toNat + 1) (r.size.toNat - 1) =
      r.array.valAt r.start.toNat r.size.toNat / 2 := by
  have h := valAt_shl63Into r
  have hlo := (shl63Into r).1[r.start.toNat]!.toNat_lt
  have hsplit := UInt64Array.valAt_add (shl63Into r).1 r.start.toNat 1 (r.size.toNat - 1)
  rw [show 1 + (r.size.toNat - 1) = r.size.toNat by lia, UInt64Array.valAt_one] at hsplit
  have hP : 2 ^ (64 * r.size.toNat) = 2 ^ 64 * 2 ^ (64 * (r.size.toNat - 1)) := by
    rw [← Nat.pow_add]; congr 1; lia
  rw [hsplit, hP] at h
  generalize (shl63Into r).1.valAt (r.start.toNat + 1) (r.size.toNat - 1) = Y at *
  generalize (shl63Into r).2.toNat = c at *
  generalize ((shl63Into r).1[r.start.toNat]!).toNat = l at *
  generalize r.array.valAt r.start.toNat r.size.toNat = X at *
  generalize 2 ^ (64 * (r.size.toNat - 1)) = P at *
  -- `X 2⁶³ = (X / 2) 2⁶⁴`, below `2^64 P`: no limb out, and nothing in the bottom limb.
  obtain ⟨m, rfl⟩ : ∃ m, X = 2 * m := ⟨X / 2, by lia⟩
  rw [show 2 * m * 2 ^ 63 = 2 ^ 64 * m by lia] at h
  rw [show 2 * m / 2 = m by lia]
  have hc : c = 0 := by
    rcases Nat.eq_zero_or_pos c with hc | hc
    · exact hc
    · have := Nat.le_mul_of_pos_right (2 ^ 64 * P) hc
      generalize 2 ^ 64 * P * c = Q at *
      generalize 2 ^ (64 * 1) * Y = W at *
      have : 2 ^ 64 * m < 2 ^ 64 * P := Nat.mul_lt_mul_of_pos_left (by lia) (by decide)
      lia
  subst hc
  rw [Nat.mul_zero, Nat.add_zero, show 64 * 1 = 64 by rfl] at h
  -- `l + 2⁶⁴ Y = 2⁶⁴ m` with `l < 2⁶⁴`: `l = 0` and `Y = m`.
  have : l = 0 := by lia
  subst this
  lia

/-! ## Exact division by an odd constant -/

/--
The step of `divExactInto` by `d` with inverse `dinv` modulo `2⁶⁴`: limb `x`, minus the borrow,
times `dinv`, and the borrow out.
-/
@[inline, expose] public def divExactStep (d dinv : UInt64) (n : USize) (j : USize) (_h : j < n)
    (x c : UInt64) : UInt64 × UInt64 :=
  let q := (x - c) * dinv
  (q, q.mulh d + (decide (x < c)).toUInt64)

private theorem divExactStep_spec (d dinv : UInt64) (hd : d.toNat * dinv.toNat % 2 ^ 64 = 1)
    (n j : USize) (h : j < n) (x c : UInt64) :
    d.toNat * (divExactStep d dinv n j h x c).1.toNat + c.toNat =
      x.toNat + 2 ^ 64 * (divExactStep d dinv n j h x c).2.toNat := by
  have := x.toNat_lt; have := c.toNat_lt; have hdl := d.toNat_lt
  simp only [divExactStep, UInt64.toNat_mul, UInt64.toNat_sub, UInt64.toNat_add,
    UInt64.toNat_mulh]
  -- `q = (x - c) d⁻¹` modulo `2⁶⁴`, so `d q = (x - c) + 2⁶⁴ hi`.
  generalize hD : (2 ^ 64 - c.toNat + x.toNat) % 2 ^ 64 = D
  have hDlt : D < 2 ^ 64 := by rw [← hD]; exact Nat.mod_lt _ (by decide)
  have hq : d.toNat * (D * dinv.toNat % 2 ^ 64) % 2 ^ 64 = D := by
    rw [Nat.mul_mod, Nat.mod_mod, ← Nat.mul_mod, ← Nat.mul_assoc, Nat.mul_comm d.toNat D,
      Nat.mul_assoc, Nat.mul_mod, hd, Nat.mul_one, Nat.mod_mod, Nat.mod_eq_of_lt hDlt]
  have hdiv := Nat.mod_add_div (d.toNat * (D * dinv.toNat % 2 ^ 64)) (2 ^ 64)
  rw [hq] at hdiv
  have hhi : D * dinv.toNat % 2 ^ 64 * d.toNat / 2 ^ 64 < d.toNat := by
    have h₁ := Nat.mod_lt (D * dinv.toNat) (show 0 < 2 ^ 64 by decide)
    have hd₀ : 0 < d.toNat := by
      rcases Nat.eq_zero_or_pos d.toNat with e | e
      · rw [e, Nat.zero_mul, Nat.zero_mod] at hd; exact absurd hd (by decide)
      · exact e
    rw [Nat.div_lt_iff_lt_mul (by decide), Nat.mul_comm d.toNat]
    exact Nat.mul_lt_mul_of_pos_right h₁ hd₀
  have hb : (decide (x < c)).toUInt64.toNat = if x.toNat < c.toNat then 1 else 0 := by
    by_cases hxc : x < c
    · simp only [decide_eq_true hxc, UInt64.lt_iff_toNat_lt.1 hxc, ↓reduceIte]; rfl
    · simp only [decide_eq_false hxc,
        show ¬x.toNat < c.toNat from fun h' => hxc (UInt64.lt_iff_toNat_lt.2 h'), ↓reduceIte]; rfl
  rw [hb, Nat.mod_eq_of_lt (show D * dinv.toNat % 2 ^ 64 * d.toNat / 2 ^ 64 +
    (if x.toNat < c.toNat then 1 else 0) < 2 ^ 64 by split <;> lia)]
  rw [Nat.mul_comm (D * dinv.toNat % 2 ^ 64) d.toNat] at hhi ⊢
  generalize d.toNat * (D * dinv.toNat % 2 ^ 64) = T at *
  generalize x.toNat = x at *
  generalize c.toNat = c at *
  split <;> lia

private theorem divExact_spec (d dinv : UInt64) (hd : d.toNat * dinv.toNat % 2 ^ 64 = 1)
    (n : USize) (arr : UInt64Array) (rs : USize)
    (hr : LoopBound arr rs n) (j : USize) (c : UInt64) :
    (foldUInPlace n (divExactStep d dinv n) arr rs hr j c).1.size = arr.size ∧
      (∀ i, (i < rs.toNat + j.toNat ∨ rs.toNat + n.toNat ≤ i) →
        (foldUInPlace n (divExactStep d dinv n) arr rs hr j c).1[i]! = arr[i]!) ∧
      d.toNat * (foldUInPlace n (divExactStep d dinv n) arr rs hr j c).1.valAt
          (rs.toNat + j.toNat) (n.toNat - j.toNat) + c.toNat =
        arr.valAt (rs.toNat + j.toNat) (n.toNat - j.toNat) +
          2 ^ (64 * (n.toNat - j.toNat)) *
            (foldUInPlace n (divExactStep d dinv n) arr rs hr j c).2.toNat := by
  induction arr, hr, j, c using foldUInPlace.induct n (divExactStep d dinv n) rs with
  | case1 arr hr j c h p ih =>
    rw [foldUInPlace_lt _ _ _ _ _ _ _ h]
    have hj := USize.lt_iff_toNat_lt.1 h
    have hj₁ := USize.toNat_add_one_of_lt h
    have hidx := hr.toNat_add h
    obtain ⟨ih₁, ih₂, ih₃⟩ := ih
    simp only [p] at ih₁ ih₂ ih₃
    rw [hj₁] at ih₂ ih₃
    simp only [UInt64Array.size_uset] at ih₁
    have hv := ih₂ (rs.toNat + j.toNat) (.inl (by lia))
    rw [getElem!_uset, hidx] at hv
    simp only [↓reduceIte] at hv
    have hx : arr.uget (rs + j) (hr.uset_bound h) = arr[rs.toNat + j.toNat]! := by
      rw [uget_eq_getElem!, hidx]
    refine ⟨ih₁, fun i hi => ?_, ?_⟩
    · rw [ih₂ i (by lia), getElem!_uset]
      simp only [hidx]
      split <;> lia
    · rw [valAt_uset_of _ _ _ _ _ _ (.inl (by rw [hidx]; lia))] at ih₃
      obtain ⟨k, hk⟩ : ∃ k, n.toNat - j.toNat = k + 1 := ⟨n.toNat - j.toNat - 1, by lia⟩
      rw [show n.toNat - (j.toNat + 1) = k by lia, ← Nat.add_assoc] at ih₃
      rw [hk, UInt64Array.valAt_succ, UInt64Array.valAt_succ, hv, ← hx, Nat.mul_succ, Nat.pow_add]
      have hs := divExactStep_spec d dinv hd n j h (arr.uget (rs + j) (hr.uset_bound h)) c
      generalize (foldUInPlace (β := UInt64) _ _ _ _ _ _ _).1.valAt _ _ = R at *
      generalize (foldUInPlace (β := UInt64) _ _ _ _ _ _ _).2.toNat = c' at *
      generalize (divExactStep d dinv n j h _ c).2.toNat = c₁ at *
      generalize (divExactStep d dinv n j h _ c).1.toNat = q at *
      generalize arr.valAt _ k = R₀ at *
      generalize (arr.uget (rs + j) _).toNat = x at *
      generalize 2 ^ (64 * k) = P at *
      generalize d.toNat = D at *
      grind
  | case2 arr hr j c h =>
    rw [foldUInPlace_ge _ _ _ _ _ _ _ h]
    have : n.toNat - j.toNat = 0 := by have := USize.lt_iff_toNat_lt (a := j) (b := n); lia
    simp [this]

/--
Divides the limbs of `r` by `d` in place, with `dinv` the inverse of `d` modulo `2⁶⁴`, like GMP's
`mpn_divexact_1` for odd divisors: exactly when `d` divides their value and `2⁶⁴ ≡ 1` modulo
`d`, and then the borrow out is `0`.
-/
public def divExactInto (r : USlice) (d dinv : UInt64) : UInt64Array × UInt64 :=
  foldUInPlaceThen r.size (divExactStep d dinv r.size) r.array r.start
    (r.loopBound (USize.le_iff_toNat_le.2 (Nat.le_refl _))) 0 0 fun arr _ c => (arr, c)

@[simp] public theorem size_divExactInto (r : USlice) (d dinv : UInt64) :
    (divExactInto r d dinv).1.size = r.array.size := by
  rw [divExactInto, foldUInPlaceThen_eq]
  exact size_foldUInPlace ..

/-- `divExactInto` leaves the limbs of `r` outside the slice unchanged. -/
public theorem getElem!_divExactInto (r : USlice) (d dinv : UInt64)
    (hd : d.toNat * dinv.toNat % 2 ^ 64 = 1) (i : Nat)
    (hi : i < r.start.toNat ∨ r.start.toNat + r.size.toNat ≤ i) :
    (divExactInto r d dinv).1[i]! = r.array[i]! := by
  rw [divExactInto, foldUInPlaceThen_eq]
  exact (divExact_spec d dinv hd _ _ _ _ 0 0).2.1 i (by rw [USize.toNat_zero]; lia)

public theorem valAt_divExactInto (r : USlice) (d dinv : UInt64)
    (hd : d.toNat * dinv.toNat % 2 ^ 64 = 1) (hd₁ : d.toNat % 2 = 1)
    (h : r.array.valAt r.start.toNat r.size.toNat % d.toNat = 0) :
    (divExactInto r d dinv).1.valAt r.start.toNat r.size.toNat =
      r.array.valAt r.start.toNat r.size.toNat / d.toNat := by
  have hs := (divExact_spec d dinv hd r.size r.array r.start
    (r.loopBound (USize.le_iff_toNat_le.2 (Nat.le_refl _))) 0 0).2.2
  simp only [USize.toNat_zero, Nat.add_zero, Nat.sub_zero, UInt64.toNat_zero] at hs
  rw [divExactInto, foldUInPlaceThen_eq]
  have hQ := valAt_lt (foldUInPlace r.size (divExactStep d dinv r.size) r.array r.start
    (r.loopBound (USize.le_iff_toNat_le.2 (Nat.le_refl _))) 0 0).1 r.start.toNat r.size.toNat
  have hX := valAt_lt r.array r.start.toNat r.size.toNat
  -- `d` is odd, so prime to `2^(64 n)`: the borrow out is a multiple of `d`, and below it.
  have hcop : Nat.Coprime d.toNat (2 ^ (64 * r.size.toNat)) := by
    refine Nat.Coprime.pow_right _ ?_
    show Nat.gcd d.toNat 2 = 1
    rw [Nat.gcd_comm, Nat.gcd_rec, hd₁]; rfl
  generalize (foldUInPlace (β := UInt64) _ _ _ _ _ 0 0).1.valAt _ _ = Q at *
  generalize (foldUInPlace (β := UInt64) _ _ _ _ _ 0 0).2.toNat = c at *
  generalize r.array.valAt r.start.toNat r.size.toNat = X at *
  generalize 2 ^ (64 * r.size.toNat) = P at *
  generalize d.toNat = D at *
  have hD : 1 ≤ D := by
    rcases Nat.eq_zero_or_pos D with e | e
    · rw [e] at hd₁; exact absurd hd₁ (by decide)
    · exact e
  have hc_lt : c < D := by
    rcases Nat.lt_or_ge c D with e | e
    · exact e
    · have h₁ := Nat.mul_le_mul_left P e
      have h₂ : D * Q < D * P := Nat.mul_lt_mul_of_pos_left hQ (by lia)
      rw [Nat.mul_comm P D] at h₁
      lia
  have hdvd : D ∣ P * c := by
    have h₁ : D ∣ X := Nat.dvd_of_mod_eq_zero h
    have h₂ : P * c = D * Q - X := by lia
    rw [h₂]
    exact Nat.dvd_sub (Nat.dvd_mul_right _ _) h₁
  have hc : c = 0 := by
    rcases Nat.eq_zero_or_pos c with e | e
    · exact e
    · exact absurd (Nat.le_of_dvd e (hcop.dvd_of_dvd_mul_left hdvd)) (by lia)
  subst hc
  rw [Nat.mul_zero, Nat.add_zero] at hs
  rw [← hs, Nat.mul_div_cancel_left _ (by lia)]

/-- Divides the limbs of `r` by `3` in place, like GMP's `mpn_divexact_by3`. -/
public def divExact3Into (r : USlice) : UInt64Array × UInt64 :=
  divExactInto r 3 0xAAAAAAAAAAAAAAAB

@[simp] public theorem size_divExact3Into (r : USlice) :
    (divExact3Into r).1.size = r.array.size := size_divExactInto ..

/-- `divExact3Into` leaves the limbs of `r` outside the slice unchanged. -/
public theorem getElem!_divExact3Into (r : USlice) (i : Nat)
    (hi : i < r.start.toNat ∨ r.start.toNat + r.size.toNat ≤ i) :
    (divExact3Into r).1[i]! = r.array[i]! := getElem!_divExactInto _ _ _ (by decide) i hi

public theorem valAt_divExact3Into (r : USlice)
    (h : r.array.valAt r.start.toNat r.size.toNat % 3 = 0) :
    (divExact3Into r).1.valAt r.start.toNat r.size.toNat =
      r.array.valAt r.start.toNat r.size.toNat / 3 :=
  valAt_divExactInto _ _ _ (by decide) (by decide) h

/-- Divides the limbs of `r` by `5` in place. -/
public def divExact5Into (r : USlice) : UInt64Array × UInt64 :=
  divExactInto r 5 0xCCCCCCCCCCCCCCCD

@[simp] public theorem size_divExact5Into (r : USlice) :
    (divExact5Into r).1.size = r.array.size := size_divExactInto ..

/-- `divExact5Into` leaves the limbs of `r` outside the slice unchanged. -/
public theorem getElem!_divExact5Into (r : USlice) (i : Nat)
    (hi : i < r.start.toNat ∨ r.start.toNat + r.size.toNat ≤ i) :
    (divExact5Into r).1[i]! = r.array[i]! := getElem!_divExactInto _ _ _ (by decide) i hi

public theorem valAt_divExact5Into (r : USlice)
    (h : r.array.valAt r.start.toNat r.size.toNat % 5 = 0) :
    (divExact5Into r).1.valAt r.start.toNat r.size.toNat =
      r.array.valAt r.start.toNat r.size.toNat / 5 :=
  valAt_divExactInto _ _ _ (by decide) (by decide) h

/-- One limb of `rshiftInto`: `x >> s` with the low `s` bits `c` of the limb above. -/
private theorem rshift_step (x c s m : UInt64) (hs₀ : 0 < s.toNat) (hs : s.toNat < 64)
    (hm : m.toNat = 2 ^ s.toNat - 1) (hc : c.toNat < 2 ^ s.toNat) :
    2 ^ s.toNat * ((x >>> s) + (c <<< (64 - s))).toNat + (x &&& m).toNat =
      x.toNat + 2 ^ 64 * c.toNat ∧ (x &&& m).toNat < 2 ^ s.toNat := by
  have h64s : (64 - s).toNat = 64 - s.toNat := by
    rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.2 (by simp; lia))]; rfl
  have hx := x.toNat_lt
  have hP : 2 ^ s.toNat * 2 ^ (64 - s.toNat) = 2 ^ 64 := by rw [← Nat.pow_add]; congr 1; lia
  have hand : (x &&& m).toNat = x.toNat % 2 ^ s.toNat := by
    rw [UInt64.toNat_and, hm, Nat.and_two_pow_sub_one_eq_mod]
  rw [hand]
  refine ⟨?_, Nat.mod_lt _ (Nat.two_pow_pos _)⟩
  rw [UInt64.toNat_add, UInt64.toNat_shiftRight, UInt64.toNat_shiftLeft, h64s,
    Nat.mod_eq_of_lt (show s.toNat < 64 from hs), Nat.mod_eq_of_lt (show 64 - s.toNat < 64 by lia),
    Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq]
  have hdm := Nat.div_add_mod x.toNat (2 ^ s.toNat)
  have hq : x.toNat / 2 ^ s.toNat < 2 ^ (64 - s.toNat) := by
    rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _), Nat.mul_comm, hP]; exact hx
  have hcP : c.toNat * 2 ^ (64 - s.toNat) + 2 ^ (64 - s.toNat) ≤ 2 ^ 64 := by
    have := Nat.mul_le_mul_right (2 ^ (64 - s.toNat)) hc
    rw [Nat.succ_mul, hP] at this; exact this
  rw [Nat.mod_eq_of_lt (show c.toNat * 2 ^ (64 - s.toNat) < 2 ^ 64 by lia),
    Nat.mod_eq_of_lt (show x.toNat / 2 ^ s.toNat + c.toNat * 2 ^ (64 - s.toNat) < 2 ^ 64 by lia)]
  generalize x.toNat / 2 ^ s.toNat = q at *
  generalize x.toNat % 2 ^ s.toNat = r at *
  generalize 2 ^ (64 - s.toNat) = Q at *
  generalize 2 ^ s.toNat = P at *
  generalize x.toNat = X at *
  subst hdm
  rw [← hP]
  grind

/--
Shifts limbs `rs` to `rs + j - 1` of `arr` right by `s` bits, from the top down, with `c` the low
bits of the limb above them, and returns the bits shifted out of the bottom.
-/
public def rshiftLoop (arr : UInt64Array) (rs : USize) (s m : UInt64) (j : USize)
    (h : LoopBound arr rs j) (c : UInt64) : UInt64Array × UInt64 :=
  if hj : j = 0 then (arr, c)
  else
    have hj₀ : j.toNat ≠ 0 := fun e => hj (USize.toNat_inj.1 (by rw [e]; rfl))
    have hj' : (j - 1).toNat = j.toNat - 1 :=
      (USize.toNat_sub_of_le j 1 (USize.le_iff_toNat_le.2 (by rw [USize.toNat_one]; lia))).trans
        (by rw [USize.toNat_one])
    have hi : (rs + (j - 1)).toNat < arr.size := by
      rw [USize.toNat_add_of_lt (by rw [hj']; lia), hj']; lia
    let x := arr.uget (rs + (j - 1)) hi
    rshiftLoop (arr.uset (rs + (j - 1)) ((x >>> s) + (c <<< (64 - s))) hi) rs s m (j - 1)
      ⟨by rw [size_uset, hj']; lia, by rw [hj']; lia⟩ (x &&& m)
termination_by j.toNat
decreasing_by
  have : j.toNat ≠ 0 := fun e => hj (USize.toNat_inj.1 (by rw [e]; rfl))
  have : (j - 1).toNat = j.toNat - 1 :=
    (USize.toNat_sub_of_le j 1 (USize.le_iff_toNat_le.2 (by rw [USize.toNat_one]; lia))).trans
      (by rw [USize.toNat_one])
  lia

private theorem rshiftLoop_spec (s m : UInt64) (hs₀ : 0 < s.toNat) (hs : s.toNat < 64)
    (hm : m.toNat = 2 ^ s.toNat - 1) (arr : UInt64Array) (rs j : USize) (h : LoopBound arr rs j)
    (c : UInt64) (hc : c.toNat < 2 ^ s.toNat) :
    (rshiftLoop arr rs s m j h c).1.size = arr.size ∧
      (∀ i, (i < rs.toNat ∨ rs.toNat + j.toNat ≤ i) → (rshiftLoop arr rs s m j h c).1[i]! = arr[i]!)
          ∧
      2 ^ s.toNat * (rshiftLoop arr rs s m j h c).1.valAt rs.toNat j.toNat +
          (rshiftLoop arr rs s m j h c).2.toNat =
        arr.valAt rs.toNat j.toNat + 2 ^ (64 * j.toNat) * c.toNat ∧
      (rshiftLoop arr rs s m j h c).2.toNat < 2 ^ s.toNat := by
  induction arr, j, h, c using rshiftLoop.induct rs s m with
  | case1 arr h c =>
    rw [rshiftLoop]
    simp [hc]
  | case2 arr j h c hj hj₀ hj' hi x ih =>
    rw [rshiftLoop, dite_eq_right hj]
    dsimp only
    obtain ⟨st, hst⟩ := rshift_step x c s m hs₀ hs hm hc
    obtain ⟨i₁, i₂, i₃, i₄⟩ := ih hst
    have hidx : (rs + (j - 1)).toNat = rs.toNat + (j.toNat - 1) := by
      rw [USize.toNat_add_of_lt (by rw [hj']; lia), hj']
    rw [hj'] at i₂ i₃
    simp only [size_uset] at i₁
    have hx : x = arr[rs.toNat + (j.toNat - 1)]! := by
      show arr.uget _ _ = _
      rw [uget_eq_getElem!, hidx]
    have hout := i₂ (rs.toNat + (j.toNat - 1)) (.inr (Nat.le_refl _))
    rw [getElem!_uset, hidx] at hout
    simp only [↓reduceIte] at hout
    have hlo : (arr.uset (rs + (j - 1)) ((x >>> s) + (c <<< (64 - s))) hi).valAt rs.toNat
        (j.toNat - 1) = arr.valAt rs.toNat (j.toNat - 1) :=
      valAt_uset_of _ _ _ _ _ _ (by rw [hidx]; lia)
    rw [hlo] at i₃
    refine ⟨i₁, fun i hi' => ?_, ?_, i₄⟩
    · rw [i₂ i (by lia), getElem!_uset]
      simp only [hidx]
      split <;> lia
    · have e : j.toNat = (j.toNat - 1) + 1 := by lia
      rw [e, UInt64Array.valAt_add, UInt64Array.valAt_add, UInt64Array.valAt_one,
        UInt64Array.valAt_one, hout, ← hx, show 64 * (j.toNat - 1 + 1) = 64 * (j.toNat - 1) + 64 by
          lia, Nat.pow_add]
      generalize (rshiftLoop _ _ _ _ _ _ _).1.valAt _ _ = V at *
      generalize (rshiftLoop _ _ _ _ _ _ _).2.toNat = co at *
      generalize ((x >>> s) + (c <<< (64 - s))).toNat = out at *
      generalize (x &&& m).toNat = c' at *
      generalize arr.valAt rs.toNat (j.toNat - 1) = L at *
      generalize 2 ^ (64 * (j.toNat - 1)) = P at *
      generalize 2 ^ s.toNat = S at *
      grind

/-- Shifts the limbs of `r` right by `s` bits in place, `0 < s < 64`, like GMP's `mpn_rshift`. -/
public def rshiftInto (r : USlice) (s : UInt64) : UInt64Array :=
  (rshiftLoop r.array r.start s ((1 <<< s) - 1) r.size
    (r.loopBound (USize.le_iff_toNat_le.2 (Nat.le_refl _))) 0).1

private theorem rshiftInto_spec (r : USlice) (s : UInt64) (hs₀ : 0 < s.toNat) (hs : s.toNat < 64) :
    (rshiftInto r s).size = r.array.size ∧
      (∀ i, (i < r.start.toNat ∨ r.start.toNat + r.size.toNat ≤ i) →
        (rshiftInto r s)[i]! = r.array[i]!) ∧
      (rshiftInto r s).valAt r.start.toNat r.size.toNat =
        r.array.valAt r.start.toNat r.size.toNat / 2 ^ s.toNat := by
  have hm : ((1 : UInt64) <<< s - 1).toNat = 2 ^ s.toNat - 1 := by
    have h₁ : ((1 : UInt64) <<< s).toNat = 2 ^ s.toNat := by
      rw [UInt64.toNat_shiftLeft, Nat.mod_eq_of_lt hs, Nat.shiftLeft_eq, UInt64.toNat_one,
        Nat.one_mul, Nat.mod_eq_of_lt (Nat.pow_lt_pow_right (by decide) hs)]
    rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.2 (by
      rw [h₁, UInt64.toNat_one]; exact Nat.one_le_two_pow)), h₁, UInt64.toNat_one]
  obtain ⟨i₁, i₂, i₃, i₄⟩ := rshiftLoop_spec s _ hs₀ hs hm r.array r.start r.size
    (r.loopBound (USize.le_iff_toNat_le.2 (Nat.le_refl _))) 0
    (by rw [UInt64.toNat_zero]; exact Nat.two_pow_pos _)
  rw [UInt64.toNat_zero, Nat.mul_zero, Nat.add_zero] at i₃
  refine ⟨i₁, i₂, ?_⟩
  rw [rshiftInto, ← i₃]
  generalize (rshiftLoop _ _ _ _ _ _ _).1.valAt _ _ = V at *
  generalize (rshiftLoop _ _ _ _ _ _ _).2.toNat = co at *
  rw [Nat.add_comm, Nat.mul_comm, Nat.add_mul_div_right _ _ (Nat.two_pow_pos _),
    Nat.div_eq_of_lt i₄, Nat.zero_add]

private theorem size_rshiftLoop (s m : UInt64) (arr : UInt64Array) (rs j : USize)
    (h : LoopBound arr rs j) (c : UInt64) : (rshiftLoop arr rs s m j h c).1.size = arr.size := by
  induction arr, j, h, c using rshiftLoop.induct rs s m with
  | case1 arr h c => rw [rshiftLoop]; simp
  | case2 arr j h c hj hj₀ hj' hi x ih =>
    rw [rshiftLoop, dite_eq_right hj]
    exact ih.trans (size_uset ..)

@[simp] public theorem size_rshiftInto (r : USlice) (s : UInt64) :
    (rshiftInto r s).size = r.array.size := size_rshiftLoop ..

/-- `rshiftInto` leaves the limbs of `r` outside the slice unchanged. -/
public theorem getElem!_rshiftInto (r : USlice) (s : UInt64) (hs₀ : 0 < s.toNat)
    (hs : s.toNat < 64) (i : Nat) (hi : i < r.start.toNat ∨ r.start.toNat + r.size.toNat ≤ i) :
    (rshiftInto r s)[i]! = r.array[i]! := (rshiftInto_spec r s hs₀ hs).2.1 i hi

public theorem valAt_rshiftInto (r : USlice) (s : UInt64) (hs₀ : 0 < s.toNat)
    (hs : s.toNat < 64) :
    (rshiftInto r s).valAt r.start.toNat r.size.toNat =
      r.array.valAt r.start.toNat r.size.toNat / 2 ^ s.toNat := (rshiftInto_spec r s hs₀ hs).2.2

/-! ## Exact passes

When the result fits, there is no carry or borrow out, and the passes compute plain values.
-/

private theorem no_borrow {V' V b P c : Nat} (h : V' + b = V + P * c) (hV' : V' < P)
    (hb : b ≤ V) : V' = V - b := by
  rcases Nat.eq_zero_or_pos c with hc | hc
  · subst hc; lia
  · have := Nat.le_mul_of_pos_right P hc
    generalize P * c = Pc at *
    lia

private theorem no_carry {V' V b P c : Nat} (h : V' + P * c = V + b) (hlt : V + b < P) :
    V' = V + b := by
  rcases Nat.eq_zero_or_pos c with hc | hc
  · subst hc; lia
  · have := Nat.le_mul_of_pos_right P hc
    generalize P * c = Pc at *
    lia

public theorem subInto_exact (r b : USlice) (hb : b.size ≤ r.size)
    (hle : b.toNat ≤ r.array.valAt r.start.toNat r.size.toNat) :
    (subInto r b 0).1.valAt r.start.toNat r.size.toNat =
      r.array.valAt r.start.toNat r.size.toNat - b.toNat := by
  have h := valAt_subInto r b 0 hb
  rw [UInt64.toNat_zero, Nat.add_zero] at h
  exact no_borrow h (valAt_lt ..) hle

public theorem subMulInto_exact (r b : USlice) (x : UInt64) (hb : b.size ≤ r.size)
    (hle : b.toNat * x.toNat ≤ r.array.valAt r.start.toNat r.size.toNat) :
    (subMulInto r b x).1.valAt r.start.toNat r.size.toNat =
      r.array.valAt r.start.toNat r.size.toNat - b.toNat * x.toNat :=
  no_borrow (valAt_subMulInto r b x hb) (valAt_lt ..) hle

public theorem addInto_exact (r b : USlice) (hb : b.size ≤ r.size)
    (hlt : r.array.valAt r.start.toNat r.size.toNat + b.toNat < 2 ^ (64 * r.size.toNat)) :
    (addInto r b 0).1.valAt r.start.toNat r.size.toNat =
      r.array.valAt r.start.toNat r.size.toNat + b.toNat := by
  have h := valAt_addInto r b 0 hb
  rw [UInt64.toNat_zero, Nat.add_zero] at h
  exact no_carry h hlt

public theorem addMulInto_exact (r b : USlice) (x : UInt64) (hb : b.size ≤ r.size)
    (hlt : r.array.valAt r.start.toNat r.size.toNat + b.toNat * x.toNat <
      2 ^ (64 * r.size.toNat)) :
    (addMulInto r b x).1.valAt r.start.toNat r.size.toNat =
      r.array.valAt r.start.toNat r.size.toNat + b.toNat * x.toNat :=
  no_carry (valAt_addMulInto r b x hb) hlt

end MPN
