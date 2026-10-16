/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bignum.Add

/-!
# Adding a difference

`addDiffInto r off x y z` adds `x - y - z` to `r` from limb `off` on, when `y + z ≤ x`, in one
pass over the limbs of `x`. Karatsuba's combination adds its middle term `z₁ - z₀ - z₂` this way,
where two subtractions and an addition took three passes.

The carry from one limb to the next is between `-2` and `1`. The loop keeps it plus `2`, a word
between `0` and `3`, so that each step is a sum and a difference of natural numbers below `2⁶⁴`.
At the end of `x` the true carry is `0` or `1`, and a carry of `1` is propagated with `incrFrom`.
-/

open ScalarArray

namespace Bignum

/-! ## The step -/

/--
`v + x + (c - 2) - y - z` as its low word and its high word plus `2`, for a carry `c` between
`0` and `3` that is the true carry plus `2`.
-/
@[inline, expose] public def addDiffStep (v x y z c : UInt32) : UInt32 × UInt32 :=
  let t := v.toUInt64 + x.toUInt64 + c.toUInt64 + 0x1FFFFFFFE - y.toUInt64 - z.toUInt64
  (t.toUInt32, (t >>> 32).toUInt32)

public theorem addDiffStep_spec (v x y z c : UInt32) (hc : c.toNat ≤ 3) :
    (addDiffStep v x y z c).1.toNat + 2 ^ 32 * (addDiffStep v x y z c).2.toNat + y.toNat +
        z.toNat + 2 = v.toNat + x.toNat + c.toNat + 2 ^ 33 ∧
      (addDiffStep v x y z c).2.toNat ≤ 3 := by
  have := v.toNat_lt
  have := x.toNat_lt
  have := y.toNat_lt
  have := z.toNat_lt
  simp only [addDiffStep, UInt64.toNat_sub, UInt64.toNat_add, UInt64.toNat_toUInt32,
    UInt32.toNat_toUInt64, UInt64.toNat_shiftRight, Nat.shiftRight_eq_div_pow, UInt64.toNat_ofNat,
    Nat.reduceMod, Nat.reducePow] at *
  omega

/-! ## The loop -/

/--
Adds `x[j...] - y[j...] - z[j...]` and the carry `c - 2` to `r` from limb `off + j` on, up to the
end of `x`, and returns the carry out plus `2`.
-/
def addDiffLoop (r : UInt32Array) (off : Nat) (x y z : UInt32Array) (j : Nat) (c : UInt32) :
    UInt32Array × UInt32 :=
  if h : j < x.size ∧ off + j < r.size then
    let p := addDiffStep r[off + j] x[j] (y.getD j 0) (z.getD j 0) c
    addDiffLoop (r.set (off + j) p.1 h.2) off x y z (j + 1) p.2
  else
    (r, c)
termination_by x.size - j

private theorem addDiffLoop_spec (r : UInt32Array) (off : Nat) (x y z : UInt32Array) (j : Nat)
    (c : UInt32) (hx : off + x.size ≤ r.size) (hy : y.size ≤ x.size) (hz : z.size ≤ x.size)
    (hj : j ≤ x.size) (hc : c.toNat ≤ 3) :
    (addDiffLoop r off x y z j c).1.size = r.size ∧
      (addDiffLoop r off x y z j c).1.toList.drop (off + x.size) = r.toList.drop (off + x.size) ∧
      (addDiffLoop r off x y z j c).2.toNat ≤ 3 ∧
      ofLimbs (addDiffLoop r off x y z j c).1.toList +
          2 ^ (32 * (off + x.size)) * (addDiffLoop r off x y z j c).2.toNat +
          2 ^ (32 * (off + j)) *
            (ofLimbs (y.toList.drop j) + ofLimbs (z.toList.drop j) + 2) =
        ofLimbs r.toList + 2 ^ (32 * (off + j)) * (ofLimbs (x.toList.drop j) + c.toNat) +
          2 * 2 ^ (32 * (off + x.size)) := by
  induction r, j, c using addDiffLoop.induct off x y z with
  | case1 r j c h p ih =>
    rw [addDiffLoop]
    simp only [h, and_self, ↓reduceDIte]
    have hs := addDiffStep_spec r[off + j] x[j] (y.getD j 0) (z.getD j 0) c hc
    obtain ⟨ih₁, ih₂, ih₃, ih₄⟩ := ih (by simpa using hx) (by omega) hs.2
    simp only [UInt32Array.size_set] at ih₁ ih₂ ih₄
    refine ⟨ih₁, ?_, ih₃, ?_⟩
    · rw [ih₂, UInt32Array.toList_set, List.drop_set]
      simp only [show off + j < off + x.size by omega, ↓reduceIte]
    have hk : off + j < r.toList.length := by simp; omega
    have hset := ofLimbs_set r.toList (off + j) p.1 hk
    simp only [UInt32Array.getElem_toList] at hset
    have hX := ofLimbs_drop x.toList j
    have hY := ofLimbs_drop y.toList j
    have hZ := ofLimbs_drop z.toList j
    have hxj : x.toList.getD j 0 = x[j] := by simp [List.getD_eq_getElem?_getD, h.1]
    have hyj : y.toList.getD j 0 = y.getD j 0 := by simp [List.getD_eq_getElem?_getD]
    have hzj : z.toList.getD j 0 = z.getD j 0 := by simp [List.getD_eq_getElem?_getD]
    rw [hxj] at hX
    rw [hyj] at hY
    rw [hzj] at hZ
    rw [UInt32Array.toList_set] at ih₄
    rw [← Nat.add_assoc off j 1, Nat.mul_add 32 (off + j) 1, Nat.mul_one, Nat.pow_add] at ih₄
    generalize ofLimbs (r.toList.set (off + j) p.1) = R₁ at *
    generalize ofLimbs r.toList = R at *
    generalize ofLimbs (x.toList.drop j) = X at *
    generalize ofLimbs (y.toList.drop j) = Y at *
    generalize ofLimbs (z.toList.drop j) = Z at *
    generalize ofLimbs (x.toList.drop (j + 1)) = X' at *
    generalize ofLimbs (y.toList.drop (j + 1)) = Y' at *
    generalize ofLimbs (z.toList.drop (j + 1)) = Z' at *
    generalize ofLimbs (addDiffLoop (r.set (off + j) p.1 h.2) off x y z (j + 1) p.2).1.toList =
      R₂ at *
    generalize (addDiffLoop (r.set (off + j) p.1 h.2) off x y z (j + 1) p.2).2.toNat = C₂ at *
    generalize 2 ^ (32 * (off + j)) = P at *
    generalize 2 ^ (32 * (off + x.size)) = Q at *
    simp only [p] at *
    generalize (addDiffStep r[off + j] x[j] (y.getD j 0) (z.getD j 0) c).1.toNat = lo at *
    generalize (addDiffStep r[off + j] x[j] (y.getD j 0) (z.getD j 0) c).2.toNat = hi at *
    generalize r[off + j].toNat = v at *
    generalize x[j].toNat = xj at *
    generalize (y.getD j 0).toNat = yj at *
    generalize (z.getD j 0).toNat = zj at *
    generalize c.toNat = c at *
    grind
  | case2 r j c h =>
    rw [addDiffLoop]
    simp only [h, ↓reduceDIte]
    have hjx : j = x.size := by omega
    subst hjx
    have hy' : y.toList.drop x.size = [] := List.drop_of_length_le (by simp; omega)
    have hz' : z.toList.drop x.size = [] := List.drop_of_length_le (by simp; omega)
    have hx' : x.toList.drop x.size = [] := List.drop_of_length_le (by simp)
    simp only [hy', hz', hx', ofLimbs_nil]
    refine ⟨by simp, by simp, hc, ?_⟩
    simp only [Nat.zero_add]
    omega

/-! ## Adding the difference -/

/--
Adds `x - y - z` to the limbs of `r` from `off` on, in one pass over the limbs of `x`, then
propagates the carry. Correct when `y + z ≤ x`, the sum fits in `r`, and `x` is the longest of
the three.
-/
public def addDiffInto (r : UInt32Array) (off : Nat) (x y z : UInt32Array) : UInt32Array :=
  let p := addDiffLoop r off x y z 0 2
  if p.2 = 3 then incrFrom p.1 (off + x.size) else p.1

/-- The value of a list split at `n`: the limbs below and the limbs from `n` on. -/
private theorem ofLimbs_take_drop (l : List UInt32) (n : Nat) (hn : n ≤ l.length) :
    ofLimbs l = ofLimbs (l.take n) + 2 ^ (32 * n) * ofLimbs (l.drop n) := by
  conv => lhs; rw [← List.take_append_drop n l]
  rw [ofLimbs_append, List.length_take, Nat.min_eq_left hn]

public theorem addDiffInto_spec (r : UInt32Array) (off : Nat) (x y z : UInt32Array)
    (hx : off + x.size ≤ r.size) (hy : y.size ≤ x.size) (hz : z.size ≤ x.size)
    (hle : toNat y + toNat z ≤ toNat x)
    (hlt : toNat r + 2 ^ (32 * off) * (toNat x - toNat y - toNat z) < 2 ^ (32 * r.size)) :
    (addDiffInto r off x y z).size = r.size ∧
      toNat (addDiffInto r off x y z) =
        toNat r + 2 ^ (32 * off) * (toNat x - toNat y - toNat z) := by
  obtain ⟨h₁, h₂, h₃, h₄⟩ := addDiffLoop_spec r off x y z 0 2 hx hy hz (by omega) (by decide)
  simp only [Nat.add_zero, List.drop_zero, UInt32.reduceToNat] at h₄
  simp only [toNat_toSlice] at hle hlt ⊢
  -- The limbs above `x` are those of `r`, so the carry out is at least `2`.
  have hn : off + x.size ≤ r.toList.length := by simp; omega
  have hn' : off + x.size ≤ (addDiffLoop r off x y z 0 2).1.toList.length := by simp [h₁]; omega
  have hR := ofLimbs_take_drop r.toList _ hn
  have hR' := ofLimbs_take_drop _ _ hn'
  rw [h₂] at hR'
  have hlo := ofLimbs_take_lt (addDiffLoop r off x y z 0 2).1.toList (off + x.size)
  have hlo' := ofLimbs_take_lt r.toList (off + x.size)
  have hpow : 2 ^ (32 * (off + x.size)) = 2 ^ (32 * off) * 2 ^ (32 * x.size) := by
    rw [Nat.mul_add, Nat.pow_add]
  have hX := toNat_lt x.toSlice
  simp only [toNat_toSlice, UInt32Array.size_toSlice, Nat.min_self, Nat.sub_zero] at hX
  have hBX : 2 ^ (32 * off) * ofLimbs x.toList < 2 ^ (32 * (off + x.size)) := by
    rw [hpow]
    exact Nat.mul_lt_mul_of_pos_left hX (Nat.two_pow_pos _)
  generalize ofLimbs ((addDiffLoop r off x y z 0 2).1.toList.take (off + x.size)) = L' at *
  generalize ofLimbs (r.toList.take (off + x.size)) = L at *
  generalize ofLimbs (r.toList.drop (off + x.size)) = H at *
  generalize hQ : 2 ^ (32 * (off + x.size)) = Q at *
  generalize hD : 2 ^ (32 * off) * (ofLimbs x.toList - ofLimbs y.toList - ofLimbs z.toList) = D
    at hlt ⊢
  have hD' : 2 ^ (32 * off) * (ofLimbs y.toList + ofLimbs z.toList) + D =
      2 ^ (32 * off) * ofLimbs x.toList := by
    rw [← hD, ← Nat.mul_add]
    congr 1
    omega
  -- `L' + Q (H + c) = L + D + Q (H + 2)`, where `L' < Q`, so the carry out `c` is at least `2`.
  have key : L' + Q * (H + (addDiffLoop r off x y z 0 2).2.toNat) = L + D + Q * (H + 2) := by
    rw [hR, hR'] at h₄
    generalize 2 ^ (32 * off) = B at *
    simp only [Nat.mul_add] at h₄ hD' ⊢
    omega
  have hC : 2 ≤ (addDiffLoop r off x y z 0 2).2.toNat := by
    generalize (addDiffLoop r off x y z 0 2).2.toNat = C at *
    rcases Nat.lt_or_ge C 2 with hC | hC
    · have : Q * (H + 2) < Q * (H + C + 1) := by
        rw [Nat.mul_add Q (H + C) 1]
        omega
      have := Nat.lt_of_mul_lt_mul_left this
      omega
    · exact hC
  have hval : ofLimbs (addDiffLoop r off x y z 0 2).1.toList +
      Q * ((addDiffLoop r off x y z 0 2).2.toNat - 2) = ofLimbs r.toList + D := by
    rw [hR, hR']
    generalize (addDiffLoop r off x y z 0 2).2.toNat = C at *
    have : Q * (H + C) = Q * H + Q * (C - 2) + Q * 2 := by
      rw [← Nat.mul_add, ← Nat.mul_add]
      congr 1
      omega
    rw [Nat.mul_add Q H 2] at key
    rw [this] at key
    omega
  simp only [addDiffInto]
  split
  · rename_i h3
    have h3' : (addDiffLoop r off x y z 0 2).2.toNat = 3 := by rw [h3]; rfl
    rw [h3'] at hval
    have hi := incrFrom_spec (addDiffLoop r off x y z 0 2).1 (off + x.size) (by omega)
      (by rw [h₁, hQ]; omega)
    rw [hi.1, h₁, hi.2, hQ]
    exact ⟨rfl, by omega⟩
  · rename_i h3
    have h2 : (addDiffLoop r off x y z 0 2).2.toNat = 2 := by
      have : (addDiffLoop r off x y z 0 2).2.toNat ≠ 3 := fun e =>
        h3 (UInt32.toNat_inj.1 (by simpa using e))
      omega
    rw [h2] at hval
    exact ⟨h₁, by omega⟩

/-! ## The compiled loop

`addDiffIntoFast` runs the loop as a `foldInPlaceThen` over the limbs of `r` from `off` on, reading
`x`, `y` and `z` with `uget`; `y` and `z` read as `0` past their ends. `@[csimp]` makes the
compiler use it in place of `addDiffInto`.
-/

/-- The step of the fold of `addDiffIntoFast` at limb `k` of `x`. -/
@[inline] def addDiffStepU (x y z : UInt32Array) (ny nz : USize) (hx : x.size < USize.size)
    (hny : ny.toNat = y.size) (hnz : nz.toNat = z.size) (k : USize)
    (hk : k.toNat < x.size.toUSize.toNat) (v c : UInt32) : UInt32 × UInt32 :=
  addDiffStep v (x.uget k (by rw [toNat_toUSize hx] at hk; exact hk))
    (if h : k < ny then y.uget k (by rw [← hny]; exact USize.lt_iff_toNat_lt.1 h) else 0)
    (if h : k < nz then z.uget k (by rw [← hnz]; exact USize.lt_iff_toNat_lt.1 h) else 0) c

private theorem addDiffStepU_eq (x y z : UInt32Array) (ny nz : USize) (hx : x.size < USize.size)
    (hny : ny.toNat = y.size) (hnz : nz.toNat = z.size) (k : USize) (hk) (j : Nat)
    (hj : k.toNat = j) (hjx : j < x.size) (v c : UInt32) :
    addDiffStepU x y z ny nz hx hny hnz k hk v c =
      addDiffStep v x[j] (y.getD j 0) (z.getD j 0) c := by
  have hd (w : UInt32Array) (nw : USize) (hnw : nw.toNat = w.size) :
      (if h : k < nw then w.uget k (by rw [← hnw]; exact USize.lt_iff_toNat_lt.1 h) else 0) =
        w.getD j 0 := by
    by_cases h : j < w.size
    · have h' : k < nw := USize.lt_iff_toNat_lt.2 (by omega)
      simp [h', h, hj, UInt32Array.getD_eq_getD_getElem?]
    · have h' : ¬ k < nw := fun h' => h (by have := USize.lt_iff_toNat_lt.1 h'; omega)
      simp [h', h, UInt32Array.getD_eq_getD_getElem?]
  rw [addDiffStepU, hd y ny hny, hd z nz hnz, uget_eq_getElem _ _ j hj]

/-- `addDiffInto` with `foldInPlaceThen`, which the compiler uses in its place. -/
public def addDiffIntoFast (r : UInt32Array) (off : Nat) (x y z : UInt32Array) : UInt32Array :=
  if hs : r.size < 4294967295 ∧ y.size < 4294967295 ∧ z.size < 4294967295 ∧
      off + x.size ≤ r.size then
    r.foldInPlaceThen off.toUSize x.size.toUSize (2 : UInt32)
      (addDiffStepU x y z y.size.toUSize z.size.toUSize (lt_usizeSize (by omega))
        (toNat_toUSize (lt_usizeSize hs.2.1)) (toNat_toUSize (lt_usizeSize hs.2.2.1)))
      (fun r' c => if c = 3 then incrFrom r' (off + x.size) else r')
      (by
        rw [toNat_toUSize (lt_usizeSize (by omega)), toNat_toUSize (lt_usizeSize (by omega))]
        exact hs.2.2.2)
  else
    let p := addDiffLoop r off x y z 0 2
    if p.2 = 3 then incrFrom p.1 (off + x.size) else p.1

/-- The fold of `addDiffIntoFast` from limb `j` on is `addDiffLoop` from limb `j` on. -/
private theorem foldInPlace_loop_addDiff (r : UInt32Array) (off : Nat) (x y z : UInt32Array)
    (ny nz : USize) (hx : x.size < USize.size) (hny : ny.toNat = y.size)
    (hnz : nz.toNat = z.size) (s n : Nat) (hs : s = off) (hn : n = x.size) (j : Nat) (c : UInt32)
    (hfit : off + x.size ≤ r.size) (h' hlen) :
    UInt32Array.foldInPlace.loop x.size.toUSize (addDiffStepU x y z ny nz hx hny hnz) s n r h'
        hlen j c =
      addDiffLoop r off x y z j c := by
  subst s n
  induction r, j, c using addDiffLoop.induct off x y z with
  | case1 r j c h p ih =>
    rw [UInt32Array.foldInPlace.loop]
    conv => rhs; rw [addDiffLoop]
    simp only [h, and_self, ↓reduceDIte]
    have e := addDiffStepU_eq x y z ny nz hx hny hnz j.toUSize
      (by rw [toNat_toUSize (Nat.lt_trans h.1 hx), toNat_toUSize hx]; exact h.1) j
      (toNat_toUSize (Nat.lt_trans h.1 hx)) h.1 r[off + j] c
    simp only [e]
    exact ih (by simpa using hfit) _
  | case2 r j c h =>
    rw [UInt32Array.foldInPlace.loop, addDiffLoop]
    have : ¬ j < x.size := by omega
    simp [this]

@[csimp] public theorem addDiffInto_eq_addDiffIntoFast : @addDiffInto = @addDiffIntoFast := by
  funext r off x y z
  rw [addDiffIntoFast]
  split
  · rename_i hs
    rw [UInt32Array.foldInPlaceThen_eq, UInt32Array.foldInPlace,
      foldInPlace_loop_addDiff r off x y z _ _ _ _ _ _ _
        (toNat_toUSize (lt_usizeSize (by omega))) (toNat_toUSize (lt_usizeSize (by omega))) 0 2
        hs.2.2.2]
    rfl
  · rfl

end Bignum
