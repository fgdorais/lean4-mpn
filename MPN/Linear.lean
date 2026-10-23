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

/-! ## Exact division by 3 -/

/-- The step of `divExact3Into`: limb `x`, minus the borrow, times the inverse of `3`. -/
@[inline, expose] public def divExact3Step (n : USize) (j : USize) (_h : j < n) (x c : UInt64) :
    UInt64 × UInt64 :=
  let q := (x - c) * 0xAAAAAAAAAAAAAAAB
  (q, q.mulh 3 + (decide (x < c)).toUInt64)

private theorem divExact3Step_spec (n j : USize) (h : j < n) (x c : UInt64) :
    3 * (divExact3Step n j h x c).1.toNat + c.toNat =
      x.toNat + 2 ^ 64 * (divExact3Step n j h x c).2.toNat := by
  have := x.toNat_lt; have := c.toNat_lt
  simp only [divExact3Step, UInt64.toNat_mul, UInt64.toNat_sub, UInt64.toNat_add, UInt64.toNat_mulh,
    UInt64.reduceToNat]
  -- `q = d 3⁻¹` modulo `2⁶⁴`, where `d = x - c` modulo `2⁶⁴`, so `3 q = d + 2⁶⁴ hi`.
  generalize hd : (2 ^ 64 - c.toNat + x.toNat) % 2 ^ 64 = d
  have hdlt : d < 2 ^ 64 := by rw [← hd]; exact Nat.mod_lt _ (by decide)
  have hq : 3 * (d * 12297829382473034411 % 2 ^ 64) % 2 ^ 64 = d := by
    rw [Nat.mul_mod, Nat.mod_mod, ← Nat.mul_mod, ← Nat.mul_assoc, Nat.mul_comm 3 d, Nat.mul_assoc,
      Nat.mul_mod, show 3 * 12297829382473034411 % 2 ^ 64 = 1 by decide, Nat.mul_one, Nat.mod_mod,
      Nat.mod_eq_of_lt hdlt]
  have hdiv := Nat.mod_add_div (3 * (d * 12297829382473034411 % 2 ^ 64)) (2 ^ 64)
  rw [hq] at hdiv
  have hhi : d * 12297829382473034411 % 2 ^ 64 * 3 / 2 ^ 64 ≤ 2 := by
    have := Nat.mod_lt (d * 12297829382473034411) (show 0 < 2 ^ 64 by decide)
    lia
  have hb : (decide (x < c)).toUInt64.toNat = if x.toNat < c.toNat then 1 else 0 := by
    by_cases hxc : x < c
    · simp only [decide_eq_true hxc, UInt64.lt_iff_toNat_lt.1 hxc, ↓reduceIte]; rfl
    · simp only [decide_eq_false hxc,
        show ¬x.toNat < c.toNat from fun h' => hxc (UInt64.lt_iff_toNat_lt.2 h'), ↓reduceIte]; rfl
  rw [hb, Nat.mod_eq_of_lt (show d * 12297829382473034411 % 2 ^ 64 * 3 / 2 ^ 64 +
    (if x.toNat < c.toNat then 1 else 0) < 2 ^ 64 by split <;> lia)]
  rw [Nat.mul_comm (d * 12297829382473034411 % 2 ^ 64) 3] at hhi ⊢
  generalize 3 * (d * 12297829382473034411 % 2 ^ 64) = T at *
  generalize x.toNat = x at *
  generalize c.toNat = c at *
  split <;> lia

private theorem divExact3_spec (n : USize) (arr : UInt64Array) (rs : USize)
    (hr : LoopBound arr rs n) (j : USize) (c : UInt64) :
    (foldUInPlace n (divExact3Step n) arr rs hr j c).1.size = arr.size ∧
      (∀ i, (i < rs.toNat + j.toNat ∨ rs.toNat + n.toNat ≤ i) →
        (foldUInPlace n (divExact3Step n) arr rs hr j c).1[i]! = arr[i]!) ∧
      3 * (foldUInPlace n (divExact3Step n) arr rs hr j c).1.valAt (rs.toNat + j.toNat)
          (n.toNat - j.toNat) + c.toNat =
        arr.valAt (rs.toNat + j.toNat) (n.toNat - j.toNat) +
          2 ^ (64 * (n.toNat - j.toNat)) *
            (foldUInPlace n (divExact3Step n) arr rs hr j c).2.toNat := by
  induction arr, hr, j, c using foldUInPlace.induct n (divExact3Step n) rs with
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
      have hs := divExact3Step_spec n j h (arr.uget (rs + j) (hr.uset_bound h)) c
      generalize (foldUInPlace (β := UInt64) _ _ _ _ _ _ _).1.valAt _ _ = R at *
      generalize (foldUInPlace (β := UInt64) _ _ _ _ _ _ _).2.toNat = c' at *
      generalize (divExact3Step n j h _ c).2.toNat = c₁ at *
      generalize (divExact3Step n j h _ c).1.toNat = q at *
      generalize arr.valAt _ k = R₀ at *
      generalize (arr.uget (rs + j) _).toNat = x at *
      generalize 2 ^ (64 * k) = P at *
      grind
  | case2 arr hr j c h =>
    rw [foldUInPlace_ge _ _ _ _ _ _ _ h]
    have : n.toNat - j.toNat = 0 := by have := USize.lt_iff_toNat_lt (a := j) (b := n); lia
    simp [this]

/--
Divides the limbs of `r` by `3` in place, like GMP's `mpn_divexact_by3`: exactly when `3` divides
their value, and then the borrow out is `0`.
-/
public def divExact3Into (r : USlice) : UInt64Array × UInt64 :=
  foldUInPlaceThen r.size (divExact3Step r.size) r.array r.start
    (r.loopBound (USize.le_iff_toNat_le.2 (Nat.le_refl _))) 0 0 fun arr _ c => (arr, c)

@[simp] public theorem size_divExact3Into (r : USlice) :
    (divExact3Into r).1.size = r.array.size := by
  rw [divExact3Into, foldUInPlaceThen_eq]
  exact (divExact3_spec _ _ _ _ 0 0).1

/-- `divExact3Into` leaves the limbs of `r` outside the slice unchanged. -/
public theorem getElem!_divExact3Into (r : USlice) (i : Nat)
    (hi : i < r.start.toNat ∨ r.start.toNat + r.size.toNat ≤ i) :
    (divExact3Into r).1[i]! = r.array[i]! := by
  rw [divExact3Into, foldUInPlaceThen_eq]
  exact (divExact3_spec _ _ _ _ 0 0).2.1 i (by rw [USize.toNat_zero]; lia)

public theorem valAt_divExact3Into (r : USlice)
    (h : r.array.valAt r.start.toNat r.size.toNat % 3 = 0) :
    (divExact3Into r).1.valAt r.start.toNat r.size.toNat =
      r.array.valAt r.start.toNat r.size.toNat / 3 := by
  have hs := (divExact3_spec r.size r.array r.start
    (r.loopBound (USize.le_iff_toNat_le.2 (Nat.le_refl _))) 0 0).2.2
  simp only [USize.toNat_zero, Nat.add_zero, Nat.sub_zero, UInt64.toNat_zero] at hs
  rw [divExact3Into, foldUInPlaceThen_eq]
  have hQ := valAt_lt (foldUInPlace r.size (divExact3Step r.size) r.array r.start
    (r.loopBound (USize.le_iff_toNat_le.2 (Nat.le_refl _))) 0 0).1 r.start.toNat r.size.toNat
  -- `2^(64 n) ≡ 1` modulo `3`, so the borrow out is a multiple of `3`, and below `3`.
  have hB : 2 ^ (64 * r.size.toNat) % 3 = 1 := by
    rw [Nat.pow_mul, Nat.pow_mod]; simp
  generalize (foldUInPlace (β := UInt64) _ _ _ _ _ 0 0).1.valAt _ _ = Q at *
  generalize (foldUInPlace (β := UInt64) _ _ _ _ _ 0 0).2.toNat = c at *
  generalize r.array.valAt r.start.toNat r.size.toNat = X at *
  generalize 2 ^ (64 * r.size.toNat) = P at *
  have hc3 : c % 3 = 0 := by
    have : (X + P * c) % 3 = 0 := by rw [← hs]; lia
    rw [Nat.add_mod, h, Nat.zero_add, Nat.mul_mod, hB, Nat.one_mul, Nat.mod_mod] at this
    simpa using this
  have hc : c = 0 := by
    rcases Nat.lt_or_ge c 3 with h3 | h3
    · lia
    · have := Nat.mul_le_mul_left P h3
      lia
  subst hc
  lia

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
