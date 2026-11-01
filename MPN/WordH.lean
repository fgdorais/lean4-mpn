/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

/-!
# High words of `UInt32`

The high-word operations of limb arithmetic on `UInt32`, computing in `UInt64`, which both widths
use: `addh c x y` adds the carry out of `x + y` to `c`, `subh b x y` adds the borrow out of
`x - y` to `b`, `mulh x y` is the high word of `x * y`, and `div2 hi lo d` is the quotient of the
double word `hi lo` by `d`. Each comes with a `toNat_*` theorem that states its value in `Nat`.
The `min` of `USize`s, on their values, closes the file.
-/


/-- Adds the high word of `x + y`, which is its carry out, to `c`. -/
@[inline, expose]
public def UInt32.addh (c x y : UInt32) : UInt32 :=
  let t := x.toUInt64 + y.toUInt64
  c + (t >>> 32).toUInt32

public theorem UInt32.toNat_addh (c x y : UInt32) :
    (UInt32.addh c x y).toNat = (c.toNat + (x.toNat + y.toNat) / 2 ^ 32) % 2 ^ 32 := by
  have := x.toNat_lt; have := y.toNat_lt
  simp only [UInt32.addh, UInt32.toNat_add, UInt32.toNat_toUInt64, UInt64.toNat_add,
    UInt64.toNat_shiftRight, UInt64.toNat_toUInt32, Nat.shiftRight_eq_div_pow]
  rw [Nat.mod_eq_of_lt (a := x.toNat + y.toNat) (by lia),
    Nat.mod_eq_of_lt (a := (x.toNat + y.toNat) / _) (by simp; lia)]
  rfl

/--
Subtracts the high word of `x - y`, computed in double width, from `b`. The high word is all ones
when `x - y` borrows, so this adds the borrow to `b`.
-/
@[inline, expose]
public def UInt32.subh (b x y : UInt32) : UInt32 :=
  let t := x.toUInt64 - y.toUInt64
  b - (t >>> 32).toUInt32

public theorem UInt32.toNat_subh (b x y : UInt32) :
    (UInt32.subh b x y).toNat = (b.toNat + if x.toNat < y.toNat then 1 else 0) % 2 ^ 32 := by
  have := x.toNat_lt; have := y.toNat_lt
  simp only [UInt32.subh, UInt32.toNat_sub, UInt32.toNat_toUInt64, UInt64.toNat_sub,
    UInt64.toNat_shiftRight, UInt64.toNat_toUInt32, Nat.shiftRight_eq_div_pow]
  simp only [UInt64.reduceToNat, Nat.reduceMod]
  split
  · have hd : (2 ^ 64 - y.toNat + x.toNat) % 2 ^ 64 = 2 ^ 64 - y.toNat + x.toNat :=
      Nat.mod_eq_of_lt (by lia)
    have hq : (2 ^ 64 - y.toNat + x.toNat) / 2 ^ 32 = 2 ^ 32 - 1 := by lia
    rw [hd, hq]
    lia
  · have hd : (2 ^ 64 - y.toNat + x.toNat) % 2 ^ 64 = x.toNat - y.toNat := by
      rw [show 2 ^ 64 - y.toNat + x.toNat = x.toNat - y.toNat + 2 ^ 64 by lia, Nat.add_mod_right,
        Nat.mod_eq_of_lt (by lia)]
    have hq : (x.toNat - y.toNat) / 2 ^ 32 = 0 := Nat.div_eq_of_lt (by lia)
    rw [hd, hq]
    lia

/-- The high word of `x * y`. -/
@[inline, expose]
public def UInt32.mulh (x y : UInt32) : UInt32 :=
  let t := x.toUInt64 * y.toUInt64
  (t >>> 32).toUInt32

public theorem UInt32.toNat_mulh (x y : UInt32) :
    (UInt32.mulh x y).toNat = x.toNat * y.toNat / 2 ^ 32 := by
  have := Nat.mul_lt_mul'' x.toNat_lt y.toNat_lt
  simp only [UInt32.mulh, UInt32.toNat_toUInt64, UInt64.toNat_mul,
    UInt64.toNat_shiftRight, UInt64.toNat_toUInt32, Nat.shiftRight_eq_div_pow]
  rw [Nat.mod_eq_of_lt (a := x.toNat * y.toNat) (by lia),
    Nat.mod_eq_of_lt (a := x.toNat * y.toNat / _) (by simp; lia)]
  rfl

/--
The low word of the quotient of `hi β + lo` by `d`, where `β = 2³²`, or `0` when `d = 0`. When
`hi < d` the quotient fits in a word, and `lo - q d` is the remainder (`toNat_div2_rem`).
-/
@[inline, expose]
public def UInt32.div2 (hi lo d : UInt32) : UInt32 :=
  (((hi.toUInt64 <<< 32) + lo.toUInt64) / d.toUInt64).toUInt32

public theorem UInt32.toNat_div2 (hi lo d : UInt32) (h : hi.toNat < d.toNat) :
    (UInt32.div2 hi lo d).toNat = (hi.toNat * 2 ^ 32 + lo.toNat) / d.toNat := by
  have := lo.toNat_lt
  have hq : (hi.toNat * 2 ^ 32 + lo.toNat) / d.toNat < 2 ^ 32 := by
    rw [Nat.div_lt_iff_lt_mul (by lia)]
    have := Nat.mul_le_mul_right (2 ^ 32) (show hi.toNat + 1 ≤ d.toNat from h)
    rw [Nat.add_mul, Nat.one_mul] at this
    rw [Nat.mul_comm]
    lia
  have hw : ((hi.toUInt64 <<< 32) + lo.toUInt64).toNat = hi.toNat * 2 ^ 32 + lo.toNat := by
    have := hi.toNat_lt
    simp only [UInt64.toNat_add, UInt64.toNat_shiftLeft, UInt32.toNat_toUInt64,
      UInt64.reduceToNat, Nat.reduceMod, Nat.shiftLeft_eq]
    rw [Nat.mod_eq_of_lt (a := hi.toNat * 2 ^ 32) (by lia), Nat.mod_eq_of_lt (by lia)]
  simp only [UInt32.div2, UInt64.toNat_toUInt32, UInt64.toNat_div, hw, UInt32.toNat_toUInt64]
  exact Nat.mod_eq_of_lt hq

/-- The remainder of `hi β + lo` by `d`, for `hi < d`, from the quotient `q = div2 hi lo d`. -/
public theorem UInt32.toNat_div2_rem (hi lo d : UInt32) (h : hi.toNat < d.toNat) :
    (lo - UInt32.div2 hi lo d * d).toNat = (hi.toNat * 2 ^ 32 + lo.toNat) % d.toNat ∧
      d.toNat * (UInt32.div2 hi lo d).toNat + (lo - UInt32.div2 hi lo d * d).toNat =
        hi.toNat * 2 ^ 32 + lo.toNat := by
  have hq := UInt32.toNat_div2 hi lo d h
  have hdm := Nat.div_add_mod (hi.toNat * 2 ^ 32 + lo.toNat) d.toNat
  have hr := Nat.mod_lt (hi.toNat * 2 ^ 32 + lo.toNat) (show 0 < d.toNat by lia)
  have hd := d.toNat_lt
  -- `lo = r + q d` in words, so `lo - q d = r`.
  have e : lo = UInt32.ofNat ((hi.toNat * 2 ^ 32 + lo.toNat) % d.toNat) +
      UInt32.div2 hi lo d * d := by
    apply UInt32.toNat_inj.1
    rw [UInt32.toNat_add, UInt32.toNat_mul, UInt32.toNat_ofNat', hq, ← Nat.add_mod,
      Nat.mul_comm _ d.toNat]
    generalize (hi.toNat * 2 ^ 32 + lo.toNat) / d.toNat = q at *
    generalize (hi.toNat * 2 ^ 32 + lo.toNat) % d.toNat = r at *
    rw [Nat.add_comm r, hdm, Nat.add_comm, Nat.add_mul_mod_self_right,
      Nat.mod_eq_of_lt lo.toNat_lt]
  have e' : (lo - UInt32.div2 hi lo d * d).toNat = (hi.toNat * 2 ^ 32 + lo.toNat) % d.toNat := by
    generalize (hi.toNat * 2 ^ 32 + lo.toNat) % d.toNat = r at e hr ⊢
    generalize UInt32.div2 hi lo d = Q at e ⊢
    rw [e, UInt32.add_sub_cancel, UInt32.toNat_ofNat', Nat.mod_eq_of_lt (by lia)]
  refine ⟨e', ?_⟩
  rw [e', hq]
  exact hdm

public theorem _root_.USize.toNat_min (a b : USize) : (min a b).toNat = min a.toNat b.toNat := by
  show (if a ≤ b then a else b).toNat = _
  have := @USize.le_iff_toNat_le a b
  split <;> lia

public theorem _root_.USize.min_le_left (a b : USize) : min a b ≤ a :=
  USize.le_iff_toNat_le.2 (by rw [USize.toNat_min]; lia)

public theorem _root_.USize.min_le_right (a b : USize) : min a b ≤ b :=
  USize.le_iff_toNat_le.2 (by rw [USize.toNat_min]; lia)
