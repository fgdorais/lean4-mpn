/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

/-!
# Double-width word operations

The high-word operations of limb arithmetic on `UInt32` and `UInt64`, each computing the high
word of a double-width result:

* `addh c x y` adds the carry out of `x + y` to `c`;
* `subh b x y` adds the borrow out of `x - y` to `b`;
* `mulh x y` is the high word of `x * y`.

The low words are the ordinary wrapping `x + y`, `x - y` and `x * y`, so a limb loop computes
the low word and the carry, borrow or high word separately, without allocating a pair.

The `UInt32` operations compute in `UInt64`. The `UInt64` operations are specified with `Nat` and
implemented by inline C with `__uint128_t`, so their generated C only compiles where the C
compiler has that type, for example, GCC 4.6 or later and Clang 3.3 or later.

Each operation comes with a `toNat_*` theorem that states its value in `Nat`.
-/

/-! ## `UInt32` -/

/-- Adds the high word of `x + y`, which is its carry out, to `c`. -/
@[inline]
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
@[inline]
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
@[inline]
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

/-! ## `UInt64` -/

/-- Adds the high word of `x + y`, which is its carry out, to `c`. -/
@[extern c inline "#1 + (uint64_t)(((__uint128_t)(#2) + (__uint128_t)(#3)) >> 64)"]
public def UInt64.addh (c x y : UInt64) : UInt64 :=
  let t := x.toNat + y.toNat
  c + (t >>> 64).toUInt64

public theorem UInt64.toNat_addh (c x y : UInt64) :
    (UInt64.addh c x y).toNat = (c.toNat + (x.toNat + y.toNat) / 2 ^ 64) % 2 ^ 64 := by
  have := x.toNat_lt; have := y.toNat_lt
  simp only [UInt64.addh, UInt64.toNat_add, UInt64.toNat_ofNat', Nat.shiftRight_eq_div_pow]
  grind

/--
Subtracts the high word of `x - y`, computed in double width, from `b`. The high word is all ones
when `x - y` borrows, so this adds the borrow to `b`.
-/
@[extern c inline "#1 - (uint64_t)(((__uint128_t)(#2) - (__uint128_t)(#3)) >> 64)"]
public def UInt64.subh (b x y : UInt64) : UInt64 :=
  let t := (2 ^ 128 + x.toNat - y.toNat) % 2 ^ 128
  b - (t >>> 64).toUInt64

public theorem UInt64.toNat_subh (b x y : UInt64) :
    (UInt64.subh b x y).toNat = (b.toNat + if x.toNat < y.toNat then 1 else 0) % 2 ^ 64 := by
  have := x.toNat_lt; have := y.toNat_lt
  simp only [UInt64.subh, UInt64.toNat_sub, UInt64.toNat_ofNat', Nat.shiftRight_eq_div_pow]
  split
  · have hd : (2 ^ 128 + x.toNat - y.toNat) % 2 ^ 128 = 2 ^ 128 + x.toNat - y.toNat :=
      Nat.mod_eq_of_lt (by lia)
    have hq : (2 ^ 128 + x.toNat - y.toNat) / 2 ^ 64 = 2 ^ 64 - 1 := by lia
    rw [hd, hq]
    lia
  · have hd : (2 ^ 128 + x.toNat - y.toNat) % 2 ^ 128 = x.toNat - y.toNat := by
      rw [show 2 ^ 128 + x.toNat - y.toNat = x.toNat - y.toNat + 2 ^ 128 by lia, Nat.add_mod_right,
        Nat.mod_eq_of_lt (by lia)]
    have hq : (x.toNat - y.toNat) / 2 ^ 64 = 0 := Nat.div_eq_of_lt (by lia)
    rw [hd, hq]
    lia

/-- The high word of `x * y`. -/
@[extern c inline "(uint64_t)(((__uint128_t)(#1) * (__uint128_t)(#2)) >> 64)"]
public def UInt64.mulh (x y : UInt64) : UInt64 :=
  let t := x.toNat * y.toNat
  (t >>> 64).toUInt64

public theorem UInt64.toNat_mulh (x y : UInt64) :
    (UInt64.mulh x y).toNat = x.toNat * y.toNat / 2 ^ 64 := by
  have := Nat.mul_lt_mul'' x.toNat_lt y.toNat_lt
  simp only [UInt64.mulh, UInt64.toNat_ofNat', Nat.shiftRight_eq_div_pow]
  exact Nat.mod_eq_of_lt (by simp; lia)
