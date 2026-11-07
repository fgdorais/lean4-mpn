/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import MPN64.AddSub
public import MPN64.Arch.MulBasecase
public import MPN.Shift
public import MPN.Bitwise
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
* `log2 a` is `Nat.log2 a.toNat`, from the top nonzero limb.

Shifts of arrays by any number of bits are `Num.shl` and `Num.shr`, by `main`'s
`WordArray.shlBits` and `shrBits`.
-/

open ScalarArray UInt64Array

namespace MPN.W64

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

/-! ## Left shifts

`main`'s `WordArray.lshiftW` and `WordArray.rshiftW` on the windows of slices.
-/

/--
Writes the limbs of `a 2ˢ`, for `0 < s < 64`, into `r` and returns the bits out of the top, on the
first `min r.size a.size` limbs, like GMP's `mpn_lshift`.
-/
public def lshift (r a : USlice) (s : UInt64) : UInt64Array × UInt64 :=
  WordArray.lshiftW r.array r.start a.array a.start (min a.size r.size) s
    (r.loopBound (USize.min_le_right ..)) (a.loopBound (USize.min_le_left ..))

@[simp] public theorem size_lshift (r a : USlice) (s : UInt64) :
    (lshift r a s).1.size = r.array.size := by
  rw [lshift, WordArray.lshiftW, wordFolds64.foldThen_eq, WordArray.foldUInPlaceThen]
  exact WordArray.size_foldUInPlace (A := UInt64Array) ..

/-- `lshift` leaves the limbs of `r` outside the ones it writes unchanged. -/
public theorem getElem!_lshift (r a : USlice) (s : UInt64) (hs₀ : 0 < s.toNat)
    (hs : s.toNat < 64) (i : Nat)
    (hi : i < r.start.toNat ∨ r.start.toNat + min a.size.toNat r.size.toNat ≤ i) :
    (lshift r a s).1[i]! = r.array[i]! :=
  (WordArray.lshiftW_spec r.array r.start a.array a.start (min a.size r.size) s _ _ hs₀ hs).2.1 i
    (by rw [USize.toNat_min]; exact hi)

public theorem valAt_lshift (r a : USlice) (s : UInt64) (hs₀ : 0 < s.toNat) (hs : s.toNat < 64)
    (har : a.size ≤ r.size) :
    (lshift r a s).1.valAt r.start.toNat a.size.toNat +
        2 ^ (64 * a.size.toNat) * (lshift r a s).2.toNat =
      a.toNat * 2 ^ s.toNat := by
  have h := (WordArray.lshiftW_spec r.array r.start a.array a.start (min a.size r.size) s
    (r.loopBound (USize.min_le_right ..)) (a.loopBound (USize.min_le_left ..)) hs₀ hs).2.2
  have e : (min a.size r.size).toNat = a.size.toNat := by
    rw [USize.toNat_min]; have := USize.le_iff_toNat_le.1 har; lia
  rw [e] at h
  rw [USlice.toNat_eq_valAt]
  exact h

/-! ## Right shifts -/

/-- `j + 1 < m` from `j < n < m`, in `USize`. -/
public theorem _root_.USize.add_one_lt_of_lt_of_lt {j n m : USize} (h : j < n) (hn : n < m) :
    j + 1 < m := by
  rw [USize.lt_iff_toNat_lt, USize.toNat_add_one_of_lt h]
  have := USize.lt_iff_toNat_lt.1 h
  have := USize.lt_iff_toNat_lt.1 hn
  lia

/-- `m - 1` does not wrap around when `m ≠ 0`. -/
public theorem toNat_pred {m : USize} (h : ¬m = 0) : (m - 1).toNat = m.toNat - 1 := by
  have : m.toNat ≠ 0 := fun e => h (USize.toNat_inj.1 (by rw [e]; rfl))
  exact (USize.toNat_sub_of_le m 1 (USize.le_iff_toNat_le.2 (by rw [USize.toNat_one]; lia))).trans
    (by rw [USize.toNat_one])

private theorem rshift_pos {r a : USlice} (h : ¬min a.size r.size = 0) :
    (0 : USize) < min a.size r.size := by
  have : (min a.size r.size).toNat ≠ 0 := fun e => h (USize.toNat_inj.1 (by rw [e]; rfl))
  rw [USize.lt_iff_toNat_lt]; simp; lia

/--
Writes the limbs of `a / 2ˢ`, for `0 < s < 64`, into `r` and returns the bits out of the bottom,
`a % 2ˢ`, on the first `min r.size a.size` limbs, like GMP's `mpn_rshift`, which returns them in
the top bits of a word instead.
-/
public def rshift (r a : USlice) (s : UInt64) : UInt64Array × UInt64 :=
  if h : min a.size r.size = 0 then (r.array, 0)
  else
    WordArray.rshiftW r.array r.start a.array a.start (min a.size r.size) s
      (r.loopBound (USize.min_le_right ..)) (a.loopBound (USize.min_le_left ..)) (rshift_pos h)

@[simp] public theorem size_rshift (r a : USlice) (s : UInt64) :
    (rshift r a s).1.size = r.array.size := by
  rw [rshift]
  split
  · rfl
  · rw [WordArray.rshiftW, wordFolds64.foldThen_eq, WordArray.foldUInPlaceThen]
    show (UInt64Array.uset _ _ _ _).size = _
    rw [size_uset]
    exact WordArray.size_foldUInPlace (A := UInt64Array) ..

/-- `rshift` leaves the limbs of `r` outside the ones it writes unchanged. -/
public theorem getElem!_rshift (r a : USlice) (s : UInt64) (hs₀ : 0 < s.toNat)
    (hs : s.toNat < 64) (i : Nat)
    (hi : i < r.start.toNat ∨ r.start.toNat + min a.size.toNat r.size.toNat ≤ i) :
    (rshift r a s).1[i]! = r.array[i]! := by
  rw [rshift]
  split
  · rfl
  · exact (WordArray.rshiftW_spec r.array r.start a.array a.start (min a.size r.size) s _ _ _ hs₀
      hs).2.1 i
      (by rw [USize.toNat_min]; exact hi)

private theorem rshift_full (r a : USlice) (s : UInt64) (hs₀ : 0 < s.toNat) (hs : s.toNat < 64)
    (har : a.size ≤ r.size) :
    2 ^ s.toNat * (rshift r a s).1.valAt r.start.toNat a.size.toNat + (rshift r a s).2.toNat =
      a.toNat ∧ (rshift r a s).2.toNat < 2 ^ s.toNat := by
  have e : (min a.size r.size).toNat = a.size.toNat := by
    rw [USize.toNat_min]; have := USize.le_iff_toNat_le.1 har; lia
  rw [rshift]
  split
  · rename_i h
    have h0 : a.size.toNat = 0 := by rw [← e, h]; rfl
    rw [USlice.toNat_eq_valAt, h0]
    simp [Nat.two_pow_pos]
  · rename_i h
    obtain ⟨-, -, h₁, h₂⟩ := WordArray.rshiftW_spec r.array r.start a.array a.start
      (min a.size r.size) s (r.loopBound (USize.min_le_right ..))
      (a.loopBound (USize.min_le_left ..)) (rshift_pos h) hs₀ hs
    rw [e] at h₁
    rw [USlice.toNat_eq_valAt]
    exact ⟨h₁, h₂⟩

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

/-! ## Base-two logarithm -/

/-- `Nat.log2 a.toNat`: the position of the top bit of `a`, or `0` when `a` is zero, by `main`'s
`WordArray.log2W` from the top limb down. -/
public def log2 (a : USlice) : Nat :=
  WordArray.log2W a.array a.start a.size (a.loopBound (USize.le_refl _))

@[simp] public theorem log2_eq (a : USlice) : log2 a = _root_.Nat.log2 a.toNat := by
  rw [log2, WordArray.log2W_eq, USlice.toNat_eq_valAt]
  rfl

end MPN.W64
