/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import MPN32.Add
public import MPN32.Arch.UInt

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

namespace MPN.W32

/-! ## Propagating a carry -/

/-- Adds one at limb `i` of `r` and propagates the carry to the end of `r`, dropping the last. -/
public def incrFrom (r : UInt32Array) (i : Nat) : UInt32Array :=
  if h : i < r.size then
    if r[i] = 0xFFFFFFFF then incrFrom (r.set i 0 h) (i + 1) else r.set i (r[i] + 1) h
  else
    r
termination_by r.size - i

/-- `incrFrom r i` adds `2^(32 i)` to `r` when the sum fits. -/
public theorem incrFrom_spec (r : UInt32Array) (i : Nat) (hi : i ≤ r.size)
    (hlt : r.valAt 0 r.size + 2 ^ (32 * i) < 2 ^ (32 * r.size)) :
    (incrFrom r i).size = r.size ∧
      (incrFrom r i).valAt 0 r.size = r.valAt 0 r.size + 2 ^ (32 * i) := by
  induction r, i using incrFrom.induct with
  | case1 r i h hmax ih =>
    rw [incrFrom]
    simp only [h, hmax, ↓reduceDIte, ↓reduceIte]
    have hset := UInt32Array.valAt_set r i 0 h 0 r.size (by lia) (by lia)
    simp only [Nat.sub_zero, hmax, UInt32.toNat_zero, Nat.mul_zero, Nat.add_zero,
      UInt32.reduceToNat] at hset
    have hpow : 2 ^ (32 * (i + 1)) = 2 ^ (32 * i) * 4294967296 := by
      rw [Nat.mul_add, Nat.mul_one, Nat.pow_add]
    simp only [UInt32Array.size_set, hpow] at ih ⊢
    generalize (r.set i 0 h).valAt 0 r.size = R' at *
    generalize r.valAt 0 r.size = R at *
    generalize 2 ^ (32 * i) = P at *
    obtain ⟨ih₁, ih₂⟩ := ih (by lia) (by lia)
    exact ⟨ih₁, by lia⟩
  | case2 r i h hmax =>
    rw [incrFrom]
    simp only [h, hmax, ↓reduceDIte, ↓reduceIte, UInt32Array.size_set, true_and]
    have hset := UInt32Array.valAt_set r i (r[i] + 1) h 0 r.size (by lia) (by lia)
    rw [Nat.sub_zero] at hset
    generalize r[i] = v at hmax hset
    have hv : (v + 1).toNat = v.toNat + 1 := by
      have : v.toNat ≠ 4294967295 := fun e => hmax (UInt32.toNat_inj.1 e)
      have := v.toNat_lt
      rw [UInt32.toNat_add, UInt32.toNat_one]
      lia
    rw [hv, Nat.mul_add, Nat.mul_one] at hset
    lia
  | case3 r i h =>
    have : i = r.size := by lia
    subst this
    lia

/-! ## The step -/

/--
`v + x + (c - 2) - y - z` as its low word and its high word plus `2`, for a carry `c` between
`0` and `3` that is the true carry plus `2`.
-/
@[inline, expose] public def addDiffStep (v x y z c : UInt32) : UInt32 × UInt32 :=
  let p := v.toUInt64 + x.toUInt64 + 0x1FFFFFFFE - y.toUInt64 - z.toUInt64
  (p.toUInt32 + c, ((p + c.toUInt64) >>> 32).toUInt32)

/-- `addDiffStep` with the carry in the sum, as its specification reads it. -/
private theorem addDiffStep_eq (v x y z c : UInt32) :
    addDiffStep v x y z c =
      ((v.toUInt64 + x.toUInt64 + c.toUInt64 + 0x1FFFFFFFE - y.toUInt64 - z.toUInt64).toUInt32,
        ((v.toUInt64 + x.toUInt64 + c.toUInt64 + 0x1FFFFFFFE - y.toUInt64 - z.toUInt64) >>>
          32).toUInt32) := by
  have e : v.toUInt64 + x.toUInt64 + c.toUInt64 + 0x1FFFFFFFE - y.toUInt64 - z.toUInt64 =
      v.toUInt64 + x.toUInt64 + 0x1FFFFFFFE - y.toUInt64 - z.toUInt64 + c.toUInt64 := by grind
  rw [e]
  simp only [addDiffStep, UInt32.toUInt32_add]

public theorem addDiffStep_spec (v x y z c : UInt32) (hc : c.toNat ≤ 3) :
    (addDiffStep v x y z c).1.toNat + 2 ^ 32 * (addDiffStep v x y z c).2.toNat + y.toNat +
        z.toNat + 2 = v.toNat + x.toNat + c.toNat + 2 ^ 33 ∧
      (addDiffStep v x y z c).2.toNat ≤ 3 := by
  have := v.toNat_lt
  have := x.toNat_lt
  have := y.toNat_lt
  have := z.toNat_lt
  rw [addDiffStep_eq]
  simp only [UInt64.toNat_sub, UInt64.toNat_add, UInt64.toNat_toUInt32,
    UInt32.toNat_toUInt64, UInt64.toNat_shiftRight, Nat.shiftRight_eq_div_pow, UInt64.toNat_ofNat,
    Nat.reduceMod, Nat.reducePow] at *
  lia

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
    (c : UInt32) (hx : off + x.size ≤ r.size) (hj : j ≤ x.size) (hc : c.toNat ≤ 3) :
    (addDiffLoop r off x y z j c).1.size = r.size ∧
      (∀ i, off + x.size ≤ i → (addDiffLoop r off x y z j c).1[i]! = r[i]!) ∧
      (addDiffLoop r off x y z j c).2.toNat ≤ 3 ∧
      (addDiffLoop r off x y z j c).1.valAt 0 r.size +
          2 ^ (32 * (off + x.size)) * (addDiffLoop r off x y z j c).2.toNat +
          2 ^ (32 * (off + j)) * (y.valAt j (x.size - j) + z.valAt j (x.size - j) + 2) =
        r.valAt 0 r.size + 2 ^ (32 * (off + j)) * (x.valAt j (x.size - j) + c.toNat) +
          2 * 2 ^ (32 * (off + x.size)) := by
  induction r, j, c using addDiffLoop.induct off x y z with
  | case1 r j c h p ih =>
    rw [addDiffLoop]
    simp only [h, and_self, ↓reduceDIte]
    have hs := addDiffStep_spec r[off + j] x[j] (y.getD j 0) (z.getD j 0) c hc
    obtain ⟨ih₁, ih₂, ih₃, ih₄⟩ := ih (by simpa using hx) (by lia) hs.2
    simp only [UInt32Array.size_set] at ih₁ ih₄
    refine ⟨ih₁, fun i hi => ?_, ih₃, ?_⟩
    · rw [ih₂ i hi, UInt32Array.getElem!_set, ite_eq_right (by lia)]
    have hset := UInt32Array.valAt_set r (off + j) p.1 h.2 0 r.size (by lia) (by lia)
    rw [Nat.sub_zero] at hset
    have e : x.size - j = x.size - (j + 1) + 1 := by lia
    have hX := UInt32Array.valAt_succ x j (x.size - (j + 1))
    have hY := UInt32Array.valAt_succ y j (x.size - (j + 1))
    have hZ := UInt32Array.valAt_succ z j (x.size - (j + 1))
    rw [← e] at hX hY hZ
    rw [UInt32Array.getElem!_eq_getElem x j h.1] at hX
    rw [← UInt32Array.getD_zero_eq_getElem!] at hY hZ
    rw [← Nat.add_assoc off j 1, Nat.mul_add 32 (off + j) 1, Nat.mul_one, Nat.pow_add] at ih₄
    generalize (r.set (off + j) p.1 h.2).valAt 0 r.size = R₁ at *
    generalize r.valAt 0 r.size = R at *
    generalize x.valAt j (x.size - j) = X at *
    generalize y.valAt j (x.size - j) = Y at *
    generalize z.valAt j (x.size - j) = Z at *
    generalize x.valAt (j + 1) (x.size - (j + 1)) = X' at *
    generalize y.valAt (j + 1) (x.size - (j + 1)) = Y' at *
    generalize z.valAt (j + 1) (x.size - (j + 1)) = Z' at *
    generalize (addDiffLoop (r.set (off + j) p.1 h.2) off x y z (j + 1) p.2).1.valAt 0 r.size =
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
    have hjx : j = x.size := by lia
    subst hjx
    simp only [Nat.sub_self, UInt32Array.valAt_zero]
    refine ⟨trivial, fun _ _ => trivial, hc, ?_⟩
    lia

/-! ## Adding the difference -/

/--
Adds `x - y - z` to the limbs of `r` from `off` on, in one pass over the limbs of `x`, then
propagates the carry. Correct when `y + z ≤ x`, the sum fits in `r`, and `x` is the longest of
the three.
-/
public def addDiffInto (r : UInt32Array) (off : Nat) (x y z : UInt32Array) : UInt32Array :=
  let p := addDiffLoop r off x y z 0 2
  if p.2 = 3 then incrFrom p.1 (off + x.size) else p.1

public theorem addDiffInto_spec (r : UInt32Array) (off : Nat) (x y z : UInt32Array)
    (hx : off + x.size ≤ r.size) (hy : y.size ≤ x.size) (hz : z.size ≤ x.size)
    (hle : toNat y + toNat z ≤ toNat x)
    (hlt : toNat r + 2 ^ (32 * off) * (toNat x - toNat y - toNat z) < 2 ^ (32 * r.size)) :
    (addDiffInto r off x y z).size = r.size ∧
      toNat (addDiffInto r off x y z) =
        toNat r + 2 ^ (32 * off) * (toNat x - toNat y - toNat z) := by
  obtain ⟨h₁, h₂, h₃, h₄⟩ := addDiffLoop_spec r off x y z 0 2 hx (by lia) (by decide)
  simp only [Nat.add_zero, Nat.sub_zero, UInt32.reduceToNat] at h₄
  rw [UInt32Array.valAt_extend y (lo := 0) (m := y.size) x.size (by lia) hy,
    UInt32Array.valAt_extend z (lo := 0) (m := z.size) x.size (by lia) hz] at h₄
  simp only [toNat_toSlice, Nat.sub_zero] at hle hlt ⊢
  -- The limbs above `x` are those of `r`, so the carry out is at least `2`.
  have hR := UInt32Array.valAt_add r 0 (off + x.size) (r.size - (off + x.size))
  have hR' := UInt32Array.valAt_add (addDiffLoop r off x y z 0 2).1 0 (off + x.size)
    (r.size - (off + x.size))
  rw [show off + x.size + (r.size - (off + x.size)) = r.size by lia, Nat.zero_add] at hR hR'
  rw [UInt32Array.valAt_congr (b := r) _ fun i hi _ => h₂ i hi] at hR'
  have hlo := UInt32Array.valAt_lt (addDiffLoop r off x y z 0 2).1 0 (off + x.size)
  have hlo' := UInt32Array.valAt_lt r 0 (off + x.size)
  have hpow : 2 ^ (32 * (off + x.size)) = 2 ^ (32 * off) * 2 ^ (32 * x.size) := by
    rw [Nat.mul_add, Nat.pow_add]
  have hX := UInt32Array.valAt_lt x 0 x.size
  have hBX : 2 ^ (32 * off) * x.valAt 0 x.size < 2 ^ (32 * (off + x.size)) := by
    rw [hpow]
    exact Nat.mul_lt_mul_of_pos_left hX (Nat.two_pow_pos _)
  generalize (addDiffLoop r off x y z 0 2).1.valAt 0 (off + x.size) = L' at *
  generalize r.valAt 0 (off + x.size) = L at *
  generalize r.valAt (off + x.size) (r.size - (off + x.size)) = H at *
  generalize hQ : 2 ^ (32 * (off + x.size)) = Q at *
  generalize hD : 2 ^ (32 * off) * (x.valAt 0 x.size - y.valAt 0 y.size - z.valAt 0 z.size) = D
    at hlt ⊢
  have hD' : 2 ^ (32 * off) * (y.valAt 0 y.size + z.valAt 0 z.size) + D =
      2 ^ (32 * off) * x.valAt 0 x.size := by
    rw [← hD, ← Nat.mul_add]
    congr 1
    lia
  -- `L' + Q (H + c) = L + D + Q (H + 2)`, where `L' < Q`, so the carry out `c` is at least `2`.
  have key : L' + Q * (H + (addDiffLoop r off x y z 0 2).2.toNat) = L + D + Q * (H + 2) := by
    rw [hR, hR'] at h₄
    generalize 2 ^ (32 * off) = B at *
    simp only [Nat.mul_add] at h₄ hD' ⊢
    lia
  have hC : 2 ≤ (addDiffLoop r off x y z 0 2).2.toNat := by
    generalize (addDiffLoop r off x y z 0 2).2.toNat = C at *
    rcases Nat.lt_or_ge C 2 with hC | hC
    · have : Q * (H + 2) < Q * (H + C + 1) := by
        rw [Nat.mul_add Q (H + C) 1]
        lia
      have := Nat.lt_of_mul_lt_mul_left this
      lia
    · exact hC
  have hval : (addDiffLoop r off x y z 0 2).1.valAt 0 r.size +
      Q * ((addDiffLoop r off x y z 0 2).2.toNat - 2) = r.valAt 0 r.size + D := by
    rw [hR, hR']
    generalize (addDiffLoop r off x y z 0 2).2.toNat = C at *
    have : Q * (H + C) = Q * H + Q * (C - 2) + Q * 2 := by
      rw [← Nat.mul_add, ← Nat.mul_add]
      congr 1
      lia
    rw [Nat.mul_add Q H 2] at key
    rw [this] at key
    lia
  simp only [addDiffInto]
  split
  · rename_i h3
    have h3' : (addDiffLoop r off x y z 0 2).2.toNat = 3 := by rw [h3]; rfl
    rw [h3'] at hval
    have hi := incrFrom_spec (addDiffLoop r off x y z 0 2).1 (off + x.size) (by lia)
      (by rw [h₁, hQ]; lia)
    rw [hi.1, hi.2, h₁, hQ]
    exact ⟨rfl, by lia⟩
  · rename_i h3
    have h2 : (addDiffLoop r off x y z 0 2).2.toNat = 2 := by
      have : (addDiffLoop r off x y z 0 2).2.toNat ≠ 3 := fun e =>
        h3 (UInt32.toNat_inj.1 (by simpa using e))
      lia
    rw [h2] at hval
    exact ⟨h₁, by lia⟩

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
    · have h' : k < nw := USize.lt_iff_toNat_lt.2 (by lia)
      simp [h', h, hj, UInt32Array.getD_eq_getD_getElem?]
    · have h' : ¬ k < nw := fun h' => h (by have := USize.lt_iff_toNat_lt.1 h'; lia)
      simp [h', h, UInt32Array.getD_eq_getD_getElem?]
  rw [addDiffStepU, hd y ny hny, hd z nz hnz, uget_eq_getElem _ _ j hj]

/-- `addDiffInto` with `foldInPlaceThen`, which the compiler uses in its place. -/
public def addDiffIntoFast (r : UInt32Array) (off : Nat) (x y z : UInt32Array) : UInt32Array :=
  if hs : r.size < 4294967295 ∧ y.size < 4294967295 ∧ z.size < 4294967295 ∧
      off + x.size ≤ r.size then
    r.foldInPlaceThen off.toUSize x.size.toUSize (2 : UInt32)
      (addDiffStepU x y z y.size.toUSize z.size.toUSize (lt_usizeSize (by lia))
        (toNat_toUSize (lt_usizeSize hs.2.1)) (toNat_toUSize (lt_usizeSize hs.2.2.1)))
      (fun r' c => if c = 3 then incrFrom r' (off + x.size) else r')
      (by
        rw [toNat_toUSize (lt_usizeSize (by lia)), toNat_toUSize (lt_usizeSize (by lia))]
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
    have : ¬ j < x.size := by lia
    simp [this]

@[csimp] public theorem addDiffInto_eq_addDiffIntoFast : @addDiffInto = @addDiffIntoFast := by
  funext r off x y z
  rw [addDiffIntoFast]
  split
  · rename_i hs
    rw [UInt32Array.foldInPlaceThen_eq, UInt32Array.foldInPlace,
      foldInPlace_loop_addDiff r off x y z _ _ _ _ _ _ _
        (toNat_toUSize (lt_usizeSize (by lia))) (toNat_toUSize (lt_usizeSize (by lia))) 0 2
        hs.2.2.2]
    rfl
  · rfl

end MPN.W32
