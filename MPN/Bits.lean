/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import MPN.Linear
import all Init.Data.UInt.Log2
import all Init.Data.Fin.Log2

/-!
# Shifts and bits

Like the other `mpn` functions, these write their result into the limbs of the slice `r`:

* `lshift r a s` is `a * 2ˢ` for `0 < s < 64`, on the first `min r.size a.size` limbs, and returns
  the bits shifted out of the top, like `mpn_lshift`;
* `rshift r a s` is `a / 2ˢ` for `0 < s < 64`, on the first `min r.size a.size` limbs, and returns
  the bits shifted out of the bottom, `a % 2ˢ`, like `mpn_rshift` (which returns them in the top
  bits of a word instead);
* `shiftLeft r a k` and `shiftRight r a k` shift by any number of bits `k`, through whole limbs
  and then `lshift` or `rshift`;
* `zeroInto r` clears the limbs of `r`;
* `log2 a` is `Nat.log2 a.toNat`, from the top nonzero limb.
-/

open ScalarArray UInt64Array

namespace MPN

/-! ## Clearing -/

/-- The step of `zeroInto`. -/
@[inline, expose] public def zeroStep (n : USize) (j : USize) (_h : j < n) (_x c : UInt64) :
    UInt64 × UInt64 :=
  (0, c)

/-- Clears the limbs of `r`. -/
public def zeroInto (r : USlice) : UInt64Array :=
  foldUInPlaceThen r.size (zeroStep r.size) r.array r.start
    (r.loopBound (USize.le_iff_toNat_le.2 (Nat.le_refl _))) 0 0 fun arr _ _ => arr

private theorem zero_spec (n : USize) (arr : UInt64Array) (rs : USize) (hr : LoopBound arr rs n)
    (j : USize) (c : UInt64) :
    (foldUInPlace n (zeroStep n) arr rs hr j c).1.size = arr.size ∧
      (∀ i, (i < rs.toNat + j.toNat ∨ rs.toNat + n.toNat ≤ i) →
        (foldUInPlace n (zeroStep n) arr rs hr j c).1[i]! = arr[i]!) ∧
      (foldUInPlace n (zeroStep n) arr rs hr j c).1.valAt (rs.toNat + j.toNat)
        (n.toNat - j.toNat) = 0 := by
  induction arr, hr, j, c using foldUInPlace.induct n (zeroStep n) rs with
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
    refine ⟨ih₁, fun i hi => ?_, ?_⟩
    · rw [ih₂ i (by lia), getElem!_uset]
      simp only [hidx]
      split <;> lia
    · obtain ⟨k, hk⟩ : ∃ k, n.toNat - j.toNat = k + 1 := ⟨n.toNat - j.toNat - 1, by lia⟩
      rw [show n.toNat - (j.toNat + 1) = k by lia, ← Nat.add_assoc] at ih₃
      rw [hk, UInt64Array.valAt_succ, hv, ih₃]
      rfl
  | case2 arr hr j c h =>
    rw [foldUInPlace_ge _ _ _ _ _ _ _ h]
    have : n.toNat - j.toNat = 0 := by have := USize.lt_iff_toNat_lt (a := j) (b := n); lia
    simp [this]

public theorem zeroInto_spec (r : USlice) :
    (zeroInto r).size = r.array.size ∧
      (∀ i, (i < r.start.toNat ∨ r.start.toNat + r.size.toNat ≤ i) →
        (zeroInto r)[i]! = r.array[i]!) ∧
      (zeroInto r).valAt r.start.toNat r.size.toNat = 0 := by
  rw [zeroInto, foldUInPlaceThen_eq]
  have := zero_spec r.size r.array r.start
    (r.loopBound (USize.le_iff_toNat_le.2 (Nat.le_refl _))) 0 0
  simp only [USize.toNat_zero, Nat.add_zero, Nat.sub_zero] at this
  exact this

public theorem valAt_replicate_zero (n lo m : Nat) :
    (UInt64Array.replicate n 0).valAt lo m = 0 := by
  induction m generalizing lo with
  | zero => simp
  | succ m ih =>
    rw [valAt_succ, ih]
    rw [getElem!_eq_getElem!_data, data_replicate]
    by_cases h : lo < n
    · simp [h]
    · simp [h]; rfl

/-! ## Words -/

/-- A word shifted left by `t < 64` bits keeps its low `64 - t` bits. -/
private theorem toNat_shl (y t : UInt64) (ht : t.toNat < 64) :
    (y <<< t).toNat = y.toNat % 2 ^ (64 - t.toNat) * 2 ^ t.toNat := by
  have hP : 2 ^ (64 - t.toNat) * 2 ^ t.toNat = 2 ^ 64 := by rw [← Nat.pow_add]; congr 1; lia
  rw [UInt64.toNat_shiftLeft, Nat.mod_eq_of_lt ht, Nat.shiftLeft_eq, ← hP,
    Nat.mul_mod_mul_right]

private theorem sub_toNat (s : UInt64) (hs : s.toNat < 64) : (64 - s).toNat = 64 - s.toNat := by
  rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.2 (by simp; lia))]; rfl

/-- One limb of `lshift`: `x 2ˢ` with the bits `c` from the limb below. -/
private theorem lshift_word (x c s : UInt64) (hs₀ : 0 < s.toNat) (hs : s.toNat < 64)
    (hc : c.toNat < 2 ^ s.toNat) :
    ((x <<< s) + c).toNat + 2 ^ 64 * (x >>> (64 - s)).toNat = x.toNat * 2 ^ s.toNat + c.toNat ∧
      (x >>> (64 - s)).toNat < 2 ^ s.toNat := by
  have hx := x.toNat_lt
  have hP : 2 ^ (64 - s.toNat) * 2 ^ s.toNat = 2 ^ 64 := by rw [← Nat.pow_add]; congr 1; lia
  have h64s := sub_toNat s hs
  have hq : x.toNat / 2 ^ (64 - s.toNat) < 2 ^ s.toNat := by
    rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _), Nat.mul_comm, hP]; exact hx
  have hr := Nat.mod_lt x.toNat (Nat.two_pow_pos (64 - s.toNat))
  have hdm := Nat.div_add_mod x.toNat (2 ^ (64 - s.toNat))
  have hle := Nat.mul_le_mul_right (2 ^ s.toNat) (show x.toNat % 2 ^ (64 - s.toNat) + 1 ≤
    2 ^ (64 - s.toNat) from hr)
  rw [UInt64.toNat_add, toNat_shl x s hs, UInt64.toNat_shiftRight, h64s,
    Nat.mod_eq_of_lt (show 64 - s.toNat < 64 by lia), Nat.shiftRight_eq_div_pow]
  refine ⟨?_, hq⟩
  rw [Nat.mod_eq_of_lt (by rw [Nat.succ_mul, hP] at hle; lia)]
  generalize x.toNat / 2 ^ (64 - s.toNat) = q at *
  generalize x.toNat % 2 ^ (64 - s.toNat) = r at *
  generalize 2 ^ (64 - s.toNat) = Q at *
  generalize 2 ^ s.toNat = P at *
  generalize x.toNat = X at *
  subst hdm
  rw [← hP]
  grind

/-- One limb of `rshift`: `x / 2ˢ` with the low bits of the limb `y` above. -/
private theorem rshift_word (x y s : UInt64) (hs₀ : 0 < s.toNat) (hs : s.toNat < 64) :
    2 ^ s.toNat * ((x >>> s) + (y <<< (64 - s))).toNat + x.toNat % 2 ^ s.toNat =
      x.toNat + 2 ^ 64 * (y.toNat % 2 ^ s.toNat) := by
  have hx := x.toNat_lt
  have hP : 2 ^ s.toNat * 2 ^ (64 - s.toNat) = 2 ^ 64 := by rw [← Nat.pow_add]; congr 1; lia
  have h64s := sub_toNat s hs
  have hq : x.toNat / 2 ^ s.toNat < 2 ^ (64 - s.toNat) := by
    rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _), Nat.mul_comm, hP]; exact hx
  have hr := Nat.mod_lt y.toNat (Nat.two_pow_pos s.toNat)
  have hdm := Nat.div_add_mod x.toNat (2 ^ s.toNat)
  have hle := Nat.mul_le_mul_right (2 ^ (64 - s.toNat)) (show y.toNat % 2 ^ s.toNat + 1 ≤
    2 ^ s.toNat from hr)
  rw [UInt64.toNat_add, toNat_shl y _ (by rw [h64s]; lia), h64s, UInt64.toNat_shiftRight,
    Nat.mod_eq_of_lt hs, Nat.shiftRight_eq_div_pow, show 64 - (64 - s.toNat) = s.toNat by lia]
  rw [Nat.mod_eq_of_lt (by rw [Nat.succ_mul, hP] at hle; lia)]
  generalize x.toNat / 2 ^ s.toNat = q at *
  generalize x.toNat % 2 ^ s.toNat = r at *
  generalize y.toNat % 2 ^ s.toNat = c at *
  generalize 2 ^ (64 - s.toNat) = Q at *
  generalize 2 ^ s.toNat = P at *
  generalize x.toNat = X at *
  subst hdm
  rw [← hP]
  grind

/-! ## Left shifts -/

/-- The step of `lshift`: limb `j` of `a` shifted left by `s`, with the bits `c` from below. -/
@[inline, expose] public def lshiftStep (a : USlice) (s : UInt64) (n : USize) (hn : n ≤ a.size)
    (j : USize) (h : j < n) (_ c : UInt64) : UInt64 × UInt64 :=
  let x := a[j]'(USize.lt_of_lt_of_le h hn)
  ((x <<< s) + c, x >>> (64 - s))

private theorem lshift_spec (a : USlice) (s : UInt64) (hs₀ : 0 < s.toNat) (hs : s.toNat < 64)
    (n : USize) (hn : n ≤ a.size) (arr : UInt64Array) (rs : USize) (hr : LoopBound arr rs n)
    (j : USize) (c : UInt64) (hc : c.toNat < 2 ^ s.toNat) :
    (foldUInPlace n (lshiftStep a s n hn) arr rs hr j c).1.size = arr.size ∧
      (∀ i, (i < rs.toNat + j.toNat ∨ rs.toNat + n.toNat ≤ i) →
        (foldUInPlace n (lshiftStep a s n hn) arr rs hr j c).1[i]! = arr[i]!) ∧
      (foldUInPlace n (lshiftStep a s n hn) arr rs hr j c).1.valAt (rs.toNat + j.toNat)
          (n.toNat - j.toNat) +
          2 ^ (64 * (n.toNat - j.toNat)) *
            (foldUInPlace n (lshiftStep a s n hn) arr rs hr j c).2.toNat =
        a.array.valAt (a.start.toNat + j.toNat) (n.toNat - j.toNat) * 2 ^ s.toNat + c.toNat := by
  induction arr, hr, j, c using foldUInPlace.induct n (lshiftStep a s n hn) rs with
  | case1 arr hr j c h p ih =>
    rw [foldUInPlace_lt _ _ _ _ _ _ _ h]
    have hj := USize.lt_iff_toNat_lt.1 h
    have hj₁ := USize.toNat_add_one_of_lt h
    have hidx := hr.toNat_add h
    have hs' := lshift_word (a[j]'(USize.lt_of_lt_of_le h hn)) c s hs₀ hs hc
    obtain ⟨ih₁, ih₂, ih₃⟩ := ih hs'.2
    simp only [p] at ih₁ ih₂ ih₃
    rw [hj₁] at ih₂ ih₃
    simp only [UInt64Array.size_uset] at ih₁
    have hv := ih₂ (rs.toNat + j.toNat) (.inl (by lia))
    rw [getElem!_uset, hidx] at hv
    simp only [↓reduceIte] at hv
    refine ⟨ih₁, fun i hi => ?_, ?_⟩
    · rw [ih₂ i (by lia), getElem!_uset]
      simp only [hidx]
      split <;> lia
    · obtain ⟨k, hk⟩ : ∃ k, n.toNat - j.toNat = k + 1 := ⟨n.toNat - j.toNat - 1, by lia⟩
      rw [show n.toNat - (j.toNat + 1) = k by lia, ← Nat.add_assoc, ← Nat.add_assoc] at ih₃
      rw [hk, UInt64Array.valAt_succ, UInt64Array.valAt_succ, hv,
        ← USlice.getElem_eq_getElem! a j (USize.lt_of_lt_of_le h hn), Nat.mul_succ, Nat.pow_add]
      have hs1 := hs'.1
      simp only [lshiftStep] at ih₃ hv ⊢
      generalize (foldUInPlace (β := UInt64) _ _ _ _ _ _ _).1.valAt _ _ = R at *
      generalize (foldUInPlace (β := UInt64) _ _ _ _ _ _ _).2.toNat = c' at *
      generalize (a[j]'(USize.lt_of_lt_of_le h hn) >>> (64 - s)).toNat = c₁ at *
      generalize ((a[j]'(USize.lt_of_lt_of_le h hn) <<< s) + c).toNat = o at *
      generalize a.array.valAt _ k = A at *
      generalize (a[j]'(USize.lt_of_lt_of_le h hn)).toNat = x at *
      generalize 2 ^ (64 * k) = P at *
      generalize 2 ^ s.toNat = S at *
      grind
  | case2 arr hr j c h =>
    rw [foldUInPlace_ge _ _ _ _ _ _ _ h]
    have : n.toNat - j.toNat = 0 := by have := USize.lt_iff_toNat_lt (a := j) (b := n); lia
    simp [this]

/--
Writes the limbs of `a 2ˢ`, for `0 < s < 64`, into `r` and returns the bits out of the top, on the
first `min r.size a.size` limbs, like GMP's `mpn_lshift`.
-/
public def lshift (r a : USlice) (s : UInt64) : UInt64Array × UInt64 :=
  foldUInPlaceThen (min a.size r.size) (lshiftStep a s _ (USize.min_le_left ..)) r.array r.start
    (r.loopBound (USize.min_le_right ..)) 0 0 fun arr _ c => (arr, c)

@[simp] public theorem size_lshift (r a : USlice) (s : UInt64) :
    (lshift r a s).1.size = r.array.size := by
  rw [lshift, foldUInPlaceThen_eq]
  exact size_foldUInPlace ..

/-- `lshift` leaves the limbs of `r` outside the ones it writes unchanged. -/
public theorem getElem!_lshift (r a : USlice) (s : UInt64) (hs₀ : 0 < s.toNat)
    (hs : s.toNat < 64) (i : Nat)
    (hi : i < r.start.toNat ∨ r.start.toNat + min a.size.toNat r.size.toNat ≤ i) :
    (lshift r a s).1[i]! = r.array[i]! := by
  rw [lshift, foldUInPlaceThen_eq]
  exact (lshift_spec a s hs₀ hs _ _ _ _ _ 0 0
    (by rw [UInt64.toNat_zero]; exact Nat.two_pow_pos _)).2.1 i
    (by rw [USize.toNat_zero, USize.toNat_min]; lia)

public theorem valAt_lshift (r a : USlice) (s : UInt64) (hs₀ : 0 < s.toNat) (hs : s.toNat < 64)
    (har : a.size ≤ r.size) :
    (lshift r a s).1.valAt r.start.toNat a.size.toNat +
        2 ^ (64 * a.size.toNat) * (lshift r a s).2.toNat =
      a.toNat * 2 ^ s.toNat := by
  have := (lshift_spec a s hs₀ hs _ (USize.min_le_left ..) r.array r.start
    (r.loopBound (USize.min_le_right ..)) 0 0
    (by rw [UInt64.toNat_zero]; exact Nat.two_pow_pos _)).2.2
  have h := USize.le_iff_toNat_le.1 har
  simp only [USize.toNat_zero, Nat.add_zero, Nat.sub_zero, USize.toNat_min,
    show min a.size.toNat r.size.toNat = a.size.toNat by lia, UInt64.toNat_zero] at this
  rw [lshift, foldUInPlaceThen_eq, USlice.toNat_eq_valAt]
  exact this

/-! ## Right shifts -/

/-- `j + 1 < m` from `j < n < m`, in `USize`. -/
public theorem _root_.USize.add_one_lt_of_lt_of_lt {j n m : USize} (h : j < n) (hn : n < m) :
    j + 1 < m := by
  rw [USize.lt_iff_toNat_lt, USize.toNat_add_one_of_lt h]
  have := USize.lt_iff_toNat_lt.1 h
  have := USize.lt_iff_toNat_lt.1 hn
  lia

/--
The step of `rshift`: limb `j` of `a`, which is `x`, shifted right by `s`, with the low bits of the
limb above, which is the next accumulator.
-/
@[inline, expose] public def rshiftStep (a : USlice) (s : UInt64) (n : USize) (hn : n < a.size)
    (j : USize) (h : j < n) (_ x : UInt64) : UInt64 × UInt64 :=
  let y := a[j + 1]'(USize.add_one_lt_of_lt_of_lt h hn)
  ((x >>> s) + (y <<< (64 - s)), y)

private theorem rshift_spec (a : USlice) (s : UInt64) (hs₀ : 0 < s.toNat) (hs : s.toNat < 64)
    (n : USize) (hn : n < a.size) (arr : UInt64Array) (rs : USize) (hr : LoopBound arr rs n)
    (j : USize) (x : UInt64) (hj : j ≤ n) (hx : x = a.array[a.start.toNat + j.toNat]!) :
    (foldUInPlace n (rshiftStep a s n hn) arr rs hr j x).1.size = arr.size ∧
      (∀ i, (i < rs.toNat + j.toNat ∨ rs.toNat + n.toNat ≤ i) →
        (foldUInPlace n (rshiftStep a s n hn) arr rs hr j x).1[i]! = arr[i]!) ∧
      (foldUInPlace n (rshiftStep a s n hn) arr rs hr j x).2 =
        a.array[a.start.toNat + n.toNat]! ∧
      2 ^ s.toNat * (foldUInPlace n (rshiftStep a s n hn) arr rs hr j x).1.valAt
          (rs.toNat + j.toNat) (n.toNat - j.toNat) + x.toNat % 2 ^ s.toNat =
        a.array.valAt (a.start.toNat + j.toNat) (n.toNat - j.toNat) +
          2 ^ (64 * (n.toNat - j.toNat)) *
            ((foldUInPlace n (rshiftStep a s n hn) arr rs hr j x).2.toNat % 2 ^ s.toNat) := by
  induction arr, hr, j, x using foldUInPlace.induct n (rshiftStep a s n hn) rs with
  | case1 arr hr j x h p ih =>
    rw [foldUInPlace_lt _ _ _ _ _ _ _ h]
    have hj' := USize.lt_iff_toNat_lt.1 h
    have hj₁ := USize.toNat_add_one_of_lt h
    have hidx := hr.toNat_add h
    have hy := USlice.getElem_eq_getElem! a (j + 1) (USize.add_one_lt_of_lt_of_lt h hn)
    obtain ⟨ih₁, ih₂, ih₃, ih₄⟩ := ih (USize.le_iff_toNat_le.2 (by lia)) hy
    simp only [p] at ih₁ ih₂ ih₃ ih₄
    rw [hj₁] at ih₂ ih₄
    simp only [UInt64Array.size_uset] at ih₁
    have hv := ih₂ (rs.toNat + j.toNat) (.inl (by lia))
    rw [getElem!_uset, hidx] at hv
    simp only [↓reduceIte] at hv
    refine ⟨ih₁, fun i hi => ?_, ih₃, ?_⟩
    · rw [ih₂ i (by lia), getElem!_uset]
      simp only [hidx]
      split <;> lia
    · obtain ⟨k, hk⟩ : ∃ k, n.toNat - j.toNat = k + 1 := ⟨n.toNat - j.toNat - 1, by lia⟩
      rw [show n.toNat - (j.toNat + 1) = k by lia, ← Nat.add_assoc, ← Nat.add_assoc] at ih₄
      rw [hk, UInt64Array.valAt_succ, UInt64Array.valAt_succ, hv, ← hx, Nat.mul_succ, Nat.pow_add]
      have hs1 := rshift_word x (a[j + 1]'(USize.add_one_lt_of_lt_of_lt h hn)) s hs₀ hs
      simp only [rshiftStep] at ih₄ hv ⊢
      generalize (foldUInPlace (β := UInt64) _ _ _ _ _ _ _).1.valAt _ _ = R at *
      generalize (foldUInPlace (β := UInt64) _ _ _ _ _ _ _).2.toNat % 2 ^ s.toNat = c' at *
      generalize ((x >>> s) + (a[j + 1]'(USize.add_one_lt_of_lt_of_lt h hn) <<< (64 - s))).toNat
        = o at *
      generalize (a[j + 1]'(USize.add_one_lt_of_lt_of_lt h hn)).toNat % 2 ^ s.toNat = c₁ at *
      generalize a.array.valAt _ k = A at *
      generalize x.toNat % 2 ^ s.toNat = x₀ at *
      generalize x.toNat = X at *
      generalize 2 ^ (64 * k) = P at *
      generalize 2 ^ s.toNat = S at *
      grind
  | case2 arr hr j x h =>
    rw [foldUInPlace_ge _ _ _ _ _ _ _ h]
    have hjn : j.toNat = n.toNat := by
      have := USize.lt_iff_toNat_lt (a := j) (b := n); have := USize.le_iff_toNat_le.1 hj; lia
    have : n.toNat - j.toNat = 0 := by lia
    simp only [hx, hjn]
    simp

/-- The low `s` bits of a word, `0 < s < 64`, by a mask. -/
private theorem toNat_mask (x s : UInt64) (hs : s.toNat < 64) :
    (x &&& ((1 <<< s) - 1)).toNat = x.toNat % 2 ^ s.toNat := by
  have h₁ : ((1 : UInt64) <<< s).toNat = 2 ^ s.toNat := by
    rw [UInt64.toNat_shiftLeft, Nat.mod_eq_of_lt hs, Nat.shiftLeft_eq, UInt64.toNat_one,
      Nat.one_mul, Nat.mod_eq_of_lt (Nat.pow_lt_pow_right (by decide) hs)]
  have hm : ((1 : UInt64) <<< s - 1).toNat = 2 ^ s.toNat - 1 := by
    rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.2 (by
      rw [h₁, UInt64.toNat_one]; exact Nat.one_le_two_pow)), h₁, UInt64.toNat_one]
  rw [UInt64.toNat_and, hm, Nat.and_two_pow_sub_one_eq_mod]

private theorem toNat_pred {m : USize} (h : ¬m = 0) : (m - 1).toNat = m.toNat - 1 := by
  have : m.toNat ≠ 0 := fun e => h (USize.toNat_inj.1 (by rw [e]; rfl))
  exact (USize.toNat_sub_of_le m 1 (USize.le_iff_toNat_le.2 (by rw [USize.toNat_one]; lia))).trans
    (by rw [USize.toNat_one])

private theorem rshift_lt {r a : USlice} (h : ¬min a.size r.size = 0) :
    min a.size r.size - 1 < a.size := by
  have := toNat_pred h
  have := USize.toNat_min a.size r.size
  rw [USize.lt_iff_toNat_lt]
  have : (min a.size r.size).toNat ≠ 0 := fun e => h (USize.toNat_inj.1 (by rw [e]; rfl))
  lia

private theorem rshift_le {r a : USlice} (h : ¬min a.size r.size = 0) :
    min a.size r.size - 1 ≤ r.size := by
  have := toNat_pred h
  have := USize.toNat_min a.size r.size
  rw [USize.le_iff_toNat_le]
  lia

private theorem rshift_pos {r a : USlice} (h : ¬min a.size r.size = 0) : (0 : USize) < a.size :=
  USize.lt_of_le_of_lt USize.zero_le (rshift_lt h)

private theorem rshift_idx (r a : USlice) (h : ¬min a.size r.size = 0) (arr : UInt64Array)
    (harr : arr.size = r.array.size) :
    (r.start + (min a.size r.size - 1)).toNat < arr.size := by
  have hlt : min a.size r.size - 1 < min a.size r.size := by
    rw [USize.lt_iff_toNat_lt, toNat_pred h]
    have : (min a.size r.size).toNat ≠ 0 := fun e => h (USize.toNat_inj.1 (by rw [e]; rfl))
    lia
  rw [harr]
  exact (r.loopBound (USize.min_le_right ..)).uset_bound hlt

/--
Writes the limbs of `a / 2ˢ`, for `0 < s < 64`, into `r` and returns the bits out of the bottom,
`a % 2ˢ`, on the first `min r.size a.size` limbs, like GMP's `mpn_rshift`, which returns them in
the top bits of a word instead.
-/
public def rshift (r a : USlice) (s : UInt64) : UInt64Array × UInt64 :=
  if h : min a.size r.size = 0 then (r.array, 0)
  else
    let x₀ := a[(0 : USize)]'(rshift_pos h)
    foldUInPlaceThen (min a.size r.size - 1) (rshiftStep a s _ (rshift_lt h)) r.array r.start
      (r.loopBound (rshift_le h)) 0 x₀ fun arr harr x =>
        (arr.uset (r.start + (min a.size r.size - 1)) (x >>> s) (rshift_idx r a h arr harr),
          x₀ &&& ((1 <<< s) - 1))

@[simp] public theorem size_rshift (r a : USlice) (s : UInt64) :
    (rshift r a s).1.size = r.array.size := by
  rw [rshift]
  split
  · rfl
  · rw [foldUInPlaceThen_eq, size_uset]
    exact size_foldUInPlace ..

/-- `rshift` leaves the limbs of `r` outside the ones it writes unchanged. -/
public theorem getElem!_rshift (r a : USlice) (s : UInt64) (hs₀ : 0 < s.toNat)
    (hs : s.toNat < 64) (i : Nat)
    (hi : i < r.start.toNat ∨ r.start.toNat + min a.size.toNat r.size.toNat ≤ i) :
    (rshift r a s).1[i]! = r.array[i]! := by
  rw [rshift]
  split
  · rfl
  · rename_i h
    have hp := toNat_pred h
    have hm := USize.toNat_min a.size r.size
    have : (min a.size r.size).toNat ≠ 0 := fun e => h (USize.toNat_inj.1 (by rw [e]; rfl))
    have hidx : (r.start + (min a.size r.size - 1)).toNat =
        r.start.toNat + ((min a.size r.size).toNat - 1) := by
      rw [(r.loopBound (USize.min_le_right a.size r.size)).toNat_add
        (USize.lt_iff_toNat_lt.2 (by lia)), hp]
    rw [foldUInPlaceThen_eq, getElem!_uset, hidx]
    simp only [show ¬(r.start.toNat + ((min a.size r.size).toNat - 1) = i) by lia, ↓reduceIte]
    exact (rshift_spec a s hs₀ hs _ (rshift_lt h) _ _ _ 0 _ USize.zero_le
      (by rw [USlice.getElem_eq_getElem!])).2.1 i (by rw [USize.toNat_zero, hp]; lia)

private theorem rshift_full (r a : USlice) (s : UInt64) (hs₀ : 0 < s.toNat) (hs : s.toNat < 64)
    (har : a.size ≤ r.size) :
    2 ^ s.toNat * (rshift r a s).1.valAt r.start.toNat a.size.toNat + (rshift r a s).2.toNat =
      a.toNat ∧ (rshift r a s).2.toNat < 2 ^ s.toNat := by
  have har' := USize.le_iff_toNat_le.1 har
  have hm := USize.toNat_min a.size r.size
  have hma : (min a.size r.size).toNat = a.size.toNat := by lia
  rw [rshift, USlice.toNat_eq_valAt]
  split
  · rename_i h
    rw [h, USize.toNat_zero] at hma
    rw [← hma]
    simp [Nat.two_pow_pos]
  · rename_i h
    have hp := toNat_pred h
    have h₀ : a.size.toNat ≠ 0 := by
      intro e; apply h; apply USize.toNat_inj.1; rw [hma, e]; rfl
    rw [foldUInPlaceThen_eq, toNat_mask _ _ hs]
    obtain ⟨-, -, i₃, i₄⟩ := rshift_spec a s hs₀ hs _ (rshift_lt h) r.array r.start
      (r.loopBound (rshift_le h)) 0 (a[(0 : USize)]'(rshift_pos h)) USize.zero_le
      (by rw [USlice.getElem_eq_getElem!])
    simp only [USize.toNat_zero, Nat.add_zero, Nat.sub_zero, hp, hma] at i₃ i₄
    have hx₀ : (a[(0 : USize)]'(rshift_pos h)) = a.array[a.start.toNat]! := by
      rw [USlice.getElem_eq_getElem!, USize.toNat_zero, Nat.add_zero]
    refine ⟨?_, Nat.mod_lt _ (Nat.two_pow_pos _)⟩
    obtain ⟨k, hk⟩ : ∃ k, a.size.toNat = k + 1 := ⟨a.size.toNat - 1, by lia⟩
    rw [hk, show k + 1 - 1 = k by lia] at i₃ i₄
    have hidx : (r.start + (min a.size r.size - 1)).toNat = r.start.toNat + k := by
      rw [(r.loopBound (USize.min_le_right a.size r.size)).toNat_add
        (USize.lt_iff_toNat_lt.2 (by lia)), hp,
        hma, hk]
      rfl
    rw [hk, UInt64Array.valAt_add, UInt64Array.valAt_add, valAt_one, valAt_one, getElem!_uset, hidx,
      valAt_uset_of _ _ _ _ _ _ (.inr (by rw [hidx]; lia))]
    simp only [↓reduceIte]
    rw [i₃] at i₄ ⊢
    rw [UInt64.toNat_shiftRight, Nat.mod_eq_of_lt hs, Nat.shiftRight_eq_div_pow]
    have hdm := Nat.div_add_mod (a.array[a.start.toNat + k]!).toNat (2 ^ s.toNat)
    generalize (foldUInPlace (β := UInt64) _ _ _ _ _ _ _).1.valAt _ _ = V at *
    generalize (a.array[a.start.toNat + k]!).toNat = X at *
    generalize (a[(0 : USize)]'(rshift_pos h)).toNat % 2 ^ s.toNat = x₀ at *
    generalize a.array.valAt _ k = A at *
    generalize 2 ^ (64 * k) = P at *
    generalize 2 ^ s.toNat = S at *
    generalize X / S = q at *
    generalize X % S = c at *
    subst hdm
    grind

public theorem valAt_rshift (r a : USlice) (s : UInt64) (hs₀ : 0 < s.toNat) (hs : s.toNat < 64)
    (har : a.size ≤ r.size) :
    (rshift r a s).1.valAt r.start.toNat a.size.toNat = a.toNat / 2 ^ s.toNat := by
  obtain ⟨h₁, h₂⟩ := rshift_full r a s hs₀ hs har
  rw [← h₁, Nat.add_comm, Nat.add_mul_div_left _ _ (Nat.two_pow_pos _), Nat.div_eq_of_lt h₂,
    Nat.zero_add]

/-- The bits out of `rshift` are `a % 2ˢ`. -/
public theorem toNat_rshift_snd (r a : USlice) (s : UInt64) (hs₀ : 0 < s.toNat)
    (hs : s.toNat < 64) (har : a.size ≤ r.size) :
    (rshift r a s).2.toNat = a.toNat % 2 ^ s.toNat := by
  obtain ⟨h₁, h₂⟩ := rshift_full r a s hs₀ hs har
  rw [← h₁, Nat.add_comm, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt h₂]

/-! ## Shifts by any number of bits -/

private theorem toNat_q {k n : Nat} (h : k / 64 ≤ n) (hn : n < USize.size) :
    (k / 64).toUSize.toNat = k / 64 :=
  USize.toNat_ofNat_of_lt' (by lia)

private theorem toNat_s (k : Nat) : (k % 64).toUInt64.toNat = k % 64 :=
  UInt64.toNat_ofNat_of_lt' (by have := Nat.mod_lt k (show 64 > 0 by decide); simp; lia)

private theorem size_zeroInto_slice (r : USlice) (q : USize) :
    (zeroInto (r.slice 0 q)).size = r.array.size :=
  (zeroInto_spec _).1

/--
Writes the limbs of `a 2ᵏ`, for any `k`, into the first `k / 64 + a.size` limbs of `r`, and
returns the bits out of the top, like `mpn_lshift` after `k / 64` zero limbs. It writes nothing
unless `k / 64 + a.size ≤ r.size`.
-/
public def shiftLeft (r a : USlice) (k : Nat) : UInt64Array × UInt64 :=
  if k / 64 + a.size.toNat ≤ r.size.toNat then
    let r' := (r.reseat (zeroInto (r.slice 0 (k / 64).toUSize)) (size_zeroInto_slice ..)).slice
      (k / 64).toUSize r.size
    if k % 64 = 0 then add1 r' a 0 else lshift r' a (k % 64).toUInt64
  else (r.array, 0)

/-- `shiftLeft` from the shift of `a` above the zero limbs. -/
private theorem shiftLeft_of (r a : USlice) (k : Nat)
    (h : k / 64 + a.size.toNat ≤ r.size.toNat) (arr : UInt64Array) (c : UInt64)
    (hu : ∀ i, (i < r.start.toNat + k / 64 ∨ r.start.toNat + k / 64 + a.size.toNat ≤ i) →
      arr[i]! = (zeroInto (r.slice 0 (k / 64).toUSize))[i]!)
    (hv : arr.valAt (r.start.toNat + k / 64) a.size.toNat + 2 ^ (64 * a.size.toNat) * c.toNat =
      a.toNat * 2 ^ (k % 64)) :
    (∀ i, (i < r.start.toNat ∨ r.start.toNat + (k / 64 + a.size.toNat) ≤ i) →
      arr[i]! = r.array[i]!) ∧
    arr.valAt r.start.toNat (k / 64 + a.size.toNat) +
        2 ^ (64 * (k / 64 + a.size.toNat)) * c.toNat = a.toNat * 2 ^ k := by
  have hq := toNat_q (show k / 64 ≤ r.size.toNat by lia) r.size.toNat_lt_size
  obtain ⟨-, z₂, z₃⟩ := zeroInto_spec (r.slice 0 (k / 64).toUSize)
  rw [USlice.start_slice _ (by rw [USize.toNat_zero]; lia) (by lia), USlice.size_slice _
    (by rw [USize.toNat_zero]; lia) (by lia), USize.toNat_zero, hq,
    Nat.add_zero, Nat.sub_zero] at z₂ z₃
  refine ⟨fun i hi => ?_, ?_⟩
  · rw [hu i (by lia), z₂ i (by lia)]
    rfl
  · have hlo : arr.valAt r.start.toNat (k / 64) = 0 := by
      rw [← z₃]
      exact valAt_congr _ fun i h₁ h₂ => hu i (.inl h₂)
    rw [UInt64Array.valAt_add, hlo, Nat.zero_add, Nat.mul_add, Nat.pow_add, Nat.mul_assoc, ←
      Nat.mul_add, hv]
    have hk : 2 ^ k = 2 ^ (64 * (k / 64)) * 2 ^ (k % 64) := by
      rw [← Nat.pow_add]; congr 1; lia
    rw [hk, Nat.mul_left_comm]

private theorem shiftLeft_spec (r a : USlice) (k : Nat)
    (h : k / 64 + a.size.toNat ≤ r.size.toNat) :
    (∀ i, (i < r.start.toNat ∨ r.start.toNat + (k / 64 + a.size.toNat) ≤ i) →
      (shiftLeft r a k).1[i]! = r.array[i]!) ∧
    (shiftLeft r a k).1.valAt r.start.toNat (k / 64 + a.size.toNat) +
        2 ^ (64 * (k / 64 + a.size.toNat)) * (shiftLeft r a k).2.toNat = a.toNat * 2 ^ k := by
  have hq := toNat_q (show k / 64 ≤ r.size.toNat by lia) r.size.toNat_lt_size
  -- The slice `r'` above the zero limbs.
  have hst : ((r.reseat (zeroInto (r.slice 0 (k / 64).toUSize))
      (size_zeroInto_slice ..)).slice (k / 64).toUSize r.size).start.toNat =
      r.start.toNat + k / 64 := by
    rw [USlice.start_slice _ (by rw [hq]; lia) (by rw [USlice.size_reseat]; exact Nat.le_refl _),
      hq,
      USlice.start_reseat]
  have hsz : ((r.reseat (zeroInto (r.slice 0 (k / 64).toUSize))
      (size_zeroInto_slice ..)).slice (k / 64).toUSize r.size).size.toNat =
      r.size.toNat - k / 64 := by
    rw [USlice.size_slice _ (by rw [hq]; lia) (by rw [USlice.size_reseat]; exact Nat.le_refl _), hq]
  have har : a.size ≤ ((r.reseat (zeroInto (r.slice 0 (k / 64).toUSize))
      (size_zeroInto_slice ..)).slice (k / 64).toUSize r.size).size :=
    USize.le_iff_toNat_le.2 (by rw [hsz]; lia)
  rw [shiftLeft, ite_eq_left h]
  dsimp only
  split
  · rename_i hs
    apply shiftLeft_of r a k h
    · intro i hi
      rw [getElem!_add1 _ _ _ _ (by rw [hst, hsz]; lia)]
      rfl
    · have := valAt_add1 _ a 0 har
      rw [hst, UInt64.toNat_zero, Nat.add_zero] at this
      rw [this, hs, Nat.pow_zero, Nat.mul_one]
  · rename_i hs
    have hs' := toNat_s k
    have h₀ : 0 < (k % 64).toUInt64.toNat := by rw [hs']; lia
    have h₁ : (k % 64).toUInt64.toNat < 64 := by rw [hs']; exact Nat.mod_lt _ (by decide)
    apply shiftLeft_of r a k h
    · intro i hi
      rw [getElem!_lshift _ _ _ h₀ h₁ _ (by rw [hst, hsz]; lia)]
      rfl
    · have := valAt_lshift _ a _ h₀ h₁ har
      rw [hst, hs'] at this
      exact this

@[simp] public theorem size_shiftLeft (r a : USlice) (k : Nat) :
    (shiftLeft r a k).1.size = r.array.size := by
  rw [shiftLeft]
  split
  · dsimp only
    split
    · rw [size_add1]; exact (zeroInto_spec _).1
    · rw [size_lshift]; exact (zeroInto_spec _).1
  · rfl

/-- `shiftLeft` leaves the limbs of `r` outside the ones it writes unchanged. -/
public theorem getElem!_shiftLeft (r a : USlice) (k i : Nat)
    (hi : i < r.start.toNat ∨ r.start.toNat + (k / 64 + a.size.toNat) ≤ i) :
    (shiftLeft r a k).1[i]! = r.array[i]! := by
  by_cases h : k / 64 + a.size.toNat ≤ r.size.toNat
  · exact (shiftLeft_spec r a k h).1 i hi
  · rw [shiftLeft, ite_eq_right h]

public theorem valAt_shiftLeft (r a : USlice) (k : Nat)
    (h : k / 64 + a.size.toNat ≤ r.size.toNat) :
    (shiftLeft r a k).1.valAt r.start.toNat (k / 64 + a.size.toNat) +
        2 ^ (64 * (k / 64 + a.size.toNat)) * (shiftLeft r a k).2.toNat = a.toNat * 2 ^ k :=
  (shiftLeft_spec r a k h).2

/--
Writes the limbs of `a / 2ᵏ`, for any `k`, into the first `a.size - k / 64` limbs of `r`, like
`mpn_rshift` on the limbs of `a` from `k / 64` on, or a copy of them.
-/
public def shiftRight (r a : USlice) (k : Nat) : UInt64Array :=
  if k / 64 < a.size.toNat then
    let a' := a.slice (k / 64).toUSize a.size
    if k % 64 = 0 then (add1 r a' 0).1 else (rshift r a' (k % 64).toUInt64).1
  else r.array

/-- The limbs of a value from `q` on are its quotient by `2^(64 q)`. -/
private theorem valAt_div (a : UInt64Array) (lo q n : Nat) (h : q ≤ n) :
    a.valAt lo n / 2 ^ (64 * q) = a.valAt (lo + q) (n - q) := by
  rw [show n = q + (n - q) by lia, UInt64Array.valAt_add, show q + (n - q) - q = n - q by lia,
    Nat.add_comm, Nat.mul_add_div (Nat.two_pow_pos _), Nat.div_eq_of_lt (valAt_lt ..),
    Nat.add_zero]

@[simp] public theorem size_shiftRight (r a : USlice) (k : Nat) :
    (shiftRight r a k).size = r.array.size := by
  rw [shiftRight]
  split
  · dsimp only
    split
    · exact size_add1 ..
    · exact size_rshift ..
  · rfl

/-- `shiftRight` leaves the limbs of `r` outside the ones it writes unchanged. -/
public theorem getElem!_shiftRight (r a : USlice) (k i : Nat)
    (hi : i < r.start.toNat ∨ r.start.toNat + (a.size.toNat - k / 64) ≤ i) :
    (shiftRight r a k)[i]! = r.array[i]! := by
  rw [shiftRight]
  split
  · rename_i h
    have hq := toNat_q (Nat.le_of_lt h) a.size.toNat_lt_size
    have hsz : (a.slice (k / 64).toUSize a.size).size.toNat = a.size.toNat - k / 64 := by
      rw [USlice.size_slice _ (by rw [hq]; lia) (Nat.le_refl _), hq]
    dsimp only
    split
    · exact getElem!_add1 _ _ _ _ (by rw [hsz]; lia)
    · have hs' := toNat_s k
      exact getElem!_rshift _ _ _ (by rw [hs']; lia)
        (by rw [hs']; exact Nat.mod_lt _ (by decide)) _ (by rw [hsz]; lia)
  · rfl

public theorem valAt_shiftRight (r a : USlice) (k : Nat)
    (h : a.size.toNat - k / 64 ≤ r.size.toNat) :
    (shiftRight r a k).valAt r.start.toNat (a.size.toNat - k / 64) = a.toNat / 2 ^ k := by
  rw [shiftRight]
  split
  · rename_i hk
    have hq := toNat_q (Nat.le_of_lt hk) a.size.toNat_lt_size
    have hsz : (a.slice (k / 64).toUSize a.size).size.toNat = a.size.toNat - k / 64 := by
      rw [USlice.size_slice _ (by rw [hq]; lia) (Nat.le_refl _), hq]
    have hv : (a.slice (k / 64).toUSize a.size).toNat = a.toNat / 2 ^ (64 * (k / 64)) := by
      rw [USlice.toNat_slice _ (by rw [hq]; lia) (Nat.le_refl _), hq, USlice.toNat_eq_valAt,
        valAt_div _ _ _ _ (by lia)]
    have har : (a.slice (k / 64).toUSize a.size).size ≤ r.size :=
      USize.le_iff_toNat_le.2 (by rw [hsz]; exact h)
    have hk' : 2 ^ k = 2 ^ (64 * (k / 64)) * 2 ^ (k % 64) := by
      rw [← Nat.pow_add]; congr 1; lia
    dsimp only
    split
    · rename_i hs
      have h₁ := valAt_add1 r _ 0 har
      have h₂ := valAt_lt (add1 r (a.slice (k / 64).toUSize a.size) 0).1 r.start.toNat
        (a.slice (k / 64).toUSize a.size).size.toNat
      have h₃ := valAt_lt a.array (a.start.toNat + k / 64) (a.size.toNat - k / 64)
      rw [UInt64.toNat_zero, Nat.add_zero] at h₁
      rw [hsz] at h₁ h₂
      rw [hk', hs, Nat.pow_zero, Nat.mul_one, ← hv]
      rw [USlice.toNat_slice _ (by rw [hq]; lia) (Nat.le_refl _), hq] at h₁
      rw [USlice.toNat_slice _ (by rw [hq]; lia) (Nat.le_refl _), hq]
      generalize (add1 _ _ _).1.valAt _ _ = V at *
      generalize (add1 _ _ _).2.toNat = c at *
      generalize a.array.valAt _ _ = A at *
      generalize 2 ^ (64 * (a.size.toNat - k / 64)) = P at *
      have : c = 0 := by
        rcases Nat.eq_zero_or_pos c with h | h
        · exact h
        · have := Nat.mul_le_mul_left P h; lia
      subst this
      lia
    · have hs' := toNat_s k
      have := valAt_rshift r _ _ (by rw [hs']; lia)
        (by rw [hs']; exact Nat.mod_lt _ (by decide)) har
      rw [hsz, hs', hv] at this
      rw [this, hk', Nat.div_div_eq_div_mul]
  · rename_i hk
    rw [show a.size.toNat - k / 64 = 0 by lia, valAt_zero, Eq.comm, Nat.div_eq_zero_iff_lt
      (Nat.two_pow_pos _), USlice.toNat_eq_valAt]
    exact Nat.lt_of_lt_of_le (valAt_lt ..) (Nat.pow_le_pow_right (by decide) (by lia))

/-! ## Base-two logarithm -/

private theorem pred_lt {a : USlice} {j : USize} (hj : ¬j = 0) (h : j ≤ a.size) :
    j - 1 < a.size := by
  have := toNat_pred hj
  have : j.toNat ≠ 0 := fun e => hj (USize.toNat_inj.1 (by rw [e]; rfl))
  have := USize.le_iff_toNat_le.1 h
  rw [USize.lt_iff_toNat_lt]
  lia

/-- `Nat.log2` of limbs `0` to `j - 1` of `a`, from the top nonzero limb. -/
public def log2Loop (a : USlice) (j : USize) (h : j ≤ a.size) : Nat :=
  if hj : j = 0 then 0
  else
    let x := a[j - 1]'(pred_lt hj h)
    if x = 0 then log2Loop a (j - 1) (USize.le_of_lt (pred_lt hj h))
    else 64 * (j - 1).toNat + x.log2.toNat
termination_by j.toNat
decreasing_by
  have := toNat_pred hj
  have : j.toNat ≠ 0 := fun e => hj (USize.toNat_inj.1 (by rw [e]; rfl))
  lia

/-- `log2` of a value with its top limb `x ≠ 0` above `e` bits. -/
private theorem log2_top {L x e : Nat} (hL : L < 2 ^ e) (hx : x ≠ 0) :
    _root_.Nat.log2 (L + 2 ^ e * x) = e + _root_.Nat.log2 x := by
  have h₁ := Nat.log2_self_le hx
  have h₂ := Nat.lt_log2_self (n := x)
  have hpos : L + 2 ^ e * x ≠ 0 := by
    have := Nat.two_pow_pos e
    have := Nat.mul_le_mul_left (2 ^ e) (show 1 ≤ x by lia)
    lia
  rw [Nat.log2_eq_iff hpos]
  rw [Nat.pow_add, Nat.add_assoc, Nat.pow_add]
  have h₃ := Nat.mul_le_mul_left (2 ^ e) h₁
  have h₄ := Nat.mul_le_mul_left (2 ^ e) (show x + 1 ≤ 2 ^ (_root_.Nat.log2 x + 1) from h₂)
  rw [Nat.pow_add] at h₄
  constructor
  · lia
  · rw [Nat.mul_add, Nat.mul_one] at h₄
    lia

private theorem _root_.UInt64.toNat_log2 (x : UInt64) : x.log2.toNat = _root_.Nat.log2 x.toNat :=
  rfl

private theorem log2Loop_eq (a : USlice) (j : USize) (h : j ≤ a.size) :
    log2Loop a j h = _root_.Nat.log2 (a.array.valAt a.start.toNat j.toNat) := by
  induction j, h using log2Loop.induct a with
  | case1 h =>
    rw [log2Loop]
    simp
  | case2 j h hj x hx ih =>
    rw [log2Loop, dite_eq_right hj]
    simp only [x] at hx ⊢
    rw [ite_eq_left hx, ih]
    have hp := toNat_pred hj
    have : j.toNat ≠ 0 := fun e => hj (USize.toNat_inj.1 (by rw [e]; rfl))
    rw [show j.toNat = (j - 1).toNat + 1 by lia, UInt64Array.valAt_add, valAt_one,
      ← USlice.getElem_eq_getElem! a (j - 1) (pred_lt hj h), hx]
    simp
  | case3 j h hj x hx =>
    rw [log2Loop, dite_eq_right hj]
    simp only [x] at hx ⊢
    rw [ite_eq_right hx, UInt64.toNat_log2]
    have hp := toNat_pred hj
    have : j.toNat ≠ 0 := fun e => hj (USize.toNat_inj.1 (by rw [e]; rfl))
    rw [show j.toNat = (j - 1).toNat + 1 by lia, UInt64Array.valAt_add, valAt_one,
      ← USlice.getElem_eq_getElem! a (j - 1) (pred_lt hj h),
      log2_top (valAt_lt ..) (fun e => hx (UInt64.toNat_inj.1 (by rw [e]; rfl)))]

/-- `Nat.log2 a.toNat`: the position of the top bit of `a`, or `0` when `a` is zero. -/
public def log2 (a : USlice) : Nat := log2Loop a a.size (USize.le_refl _)

@[simp] public theorem log2_eq (a : USlice) : log2 a = _root_.Nat.log2 a.toNat := by
  rw [log2, log2Loop_eq, USlice.toNat_eq_valAt]

end MPN
