/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

/-!
# Double-width word operations

The primitive operations of limb arithmetic on fixed-width unsigned integers:

* `addWithCarry x y c` is `x + y + c`, as its low word and a carry out;
* `subWithBorrow x y b` is `x - y - b`, as its low word (wrapping) and a borrow out;
* `mulAddAdd x y a b` is `x * y + a + b`, as its low word and its high word.

The last one cannot overflow since `(2ⁿ - 1) * (2ⁿ - 1) + (2ⁿ - 1) + (2ⁿ - 1) = 2²ⁿ - 1`. Each type
computes in the next wider type, and each operation comes with its specification in `Nat`.
-/

/-! ## `UInt8` -/

/-- `x + y + c` as its low word and a carry out. -/
@[inline, expose] public def UInt8.addWithCarry (x y : UInt8) (c : Bool) : UInt8 × Bool :=
  let t := x.toUInt16 + y.toUInt16 + c.toUInt16
  (t.toUInt8, t >>> 8 != 0)

/-- `x - y - b` as its low word, wrapping, and a borrow out. -/
@[inline, expose] public def UInt8.subWithBorrow (x y : UInt8) (b : Bool) : UInt8 × Bool :=
  let t := x.toUInt16 - y.toUInt16 - b.toUInt16
  (t.toUInt8, t >>> 8 != 0)

/-- `x * y + a + b` as its low word and its high word. -/
@[inline, expose] public def UInt8.mulAddAdd (x y a b : UInt8) : UInt8 × UInt8 :=
  let t := x.toUInt16 * y.toUInt16 + a.toUInt16 + b.toUInt16
  (t.toUInt8, (t >>> 8).toUInt8)

private theorem UInt8.high_ne_zero (t : UInt16) : (t >>> 8 != 0) = decide (2 ^ 8 ≤ t.toNat) := by
  rw [Bool.eq_iff_iff]
  simp [← UInt16.toNat_inj, Nat.shiftRight_eq_div_pow]

public theorem UInt8.addWithCarry_spec (x y : UInt8) (c : Bool) :
    (x.addWithCarry y c).1.toNat + (x.addWithCarry y c).2.toNat * 2 ^ 8 =
      x.toNat + y.toNat + c.toNat := by
  have := x.toNat_lt
  have := y.toNat_lt
  rw [addWithCarry, high_ne_zero]
  cases c <;> simp [UInt16.toNat_add, Bool.toUInt16, Bool.toNat] <;> split <;> omega

public theorem UInt8.subWithBorrow_spec (x y : UInt8) (b : Bool) :
    (x.subWithBorrow y b).1.toNat + y.toNat + b.toNat =
      x.toNat + (x.subWithBorrow y b).2.toNat * 2 ^ 8 := by
  have := x.toNat_lt
  have := y.toNat_lt
  rw [subWithBorrow, high_ne_zero]
  cases b <;>
    simp only [UInt16.toNat_toUInt8, UInt16.toNat_sub, UInt8.toNat_toUInt16, Bool.toUInt16,
      Bool.toNat, Bool.cond_false, Bool.cond_true, UInt16.toNat_zero, UInt16.toNat_one,
      Bool.false_eq_true, ↓reduceIte, Bool.cond_decide, Nat.reducePow] <;> split <;> omega

public theorem UInt8.mulAddAdd_spec (x y a b : UInt8) :
    (x.mulAddAdd y a b).1.toNat + (x.mulAddAdd y a b).2.toNat * 2 ^ 8 =
      x.toNat * y.toNat + a.toNat + b.toNat := by
  have := x.toNat_lt
  have := y.toNat_lt
  have := a.toNat_lt
  have := b.toNat_lt
  have : x.toNat * y.toNat ≤ (2 ^ 8 - 1) * (2 ^ 8 - 1) := Nat.mul_le_mul (by omega) (by omega)
  simp only [mulAddAdd, UInt16.toNat_add, UInt16.toNat_mul, UInt16.toNat_toUInt8,
    UInt8.toNat_toUInt16, UInt16.toNat_shiftRight, Nat.shiftRight_eq_div_pow, UInt16.toNat_ofNat,
    Nat.reduceMod, Nat.reducePow] at *
  generalize x.toNat * y.toNat = p at *
  omega

/-! ## `UInt16` -/

/-- `x + y + c` as its low word and a carry out. -/
@[inline, expose] public def UInt16.addWithCarry (x y : UInt16) (c : Bool) : UInt16 × Bool :=
  let t := x.toUInt32 + y.toUInt32 + c.toUInt32
  (t.toUInt16, t >>> 16 != 0)

/-- `x - y - b` as its low word, wrapping, and a borrow out. -/
@[inline, expose] public def UInt16.subWithBorrow (x y : UInt16) (b : Bool) : UInt16 × Bool :=
  let t := x.toUInt32 - y.toUInt32 - b.toUInt32
  (t.toUInt16, t >>> 16 != 0)

/-- `x * y + a + b` as its low word and its high word. -/
@[inline, expose] public def UInt16.mulAddAdd (x y a b : UInt16) : UInt16 × UInt16 :=
  let t := x.toUInt32 * y.toUInt32 + a.toUInt32 + b.toUInt32
  (t.toUInt16, (t >>> 16).toUInt16)

private theorem UInt16.high_ne_zero (t : UInt32) : (t >>> 16 != 0) = decide (2 ^ 16 ≤ t.toNat) := by
  rw [Bool.eq_iff_iff]
  simp [← UInt32.toNat_inj, Nat.shiftRight_eq_div_pow]

public theorem UInt16.addWithCarry_spec (x y : UInt16) (c : Bool) :
    (x.addWithCarry y c).1.toNat + (x.addWithCarry y c).2.toNat * 2 ^ 16 =
      x.toNat + y.toNat + c.toNat := by
  have := x.toNat_lt
  have := y.toNat_lt
  rw [addWithCarry, high_ne_zero]
  cases c <;> simp [UInt32.toNat_add, Bool.toUInt32, Bool.toNat] <;> split <;> omega

public theorem UInt16.subWithBorrow_spec (x y : UInt16) (b : Bool) :
    (x.subWithBorrow y b).1.toNat + y.toNat + b.toNat =
      x.toNat + (x.subWithBorrow y b).2.toNat * 2 ^ 16 := by
  have := x.toNat_lt
  have := y.toNat_lt
  rw [subWithBorrow, high_ne_zero]
  cases b <;>
    simp only [UInt32.toNat_toUInt16, UInt32.toNat_sub, UInt16.toNat_toUInt32, Bool.toUInt32,
      Bool.toNat, Bool.cond_false, Bool.cond_true, UInt32.toNat_zero, UInt32.toNat_one,
      Bool.false_eq_true, ↓reduceIte, Bool.cond_decide, Nat.reducePow] <;> split <;> omega

public theorem UInt16.mulAddAdd_spec (x y a b : UInt16) :
    (x.mulAddAdd y a b).1.toNat + (x.mulAddAdd y a b).2.toNat * 2 ^ 16 =
      x.toNat * y.toNat + a.toNat + b.toNat := by
  have := x.toNat_lt
  have := y.toNat_lt
  have := a.toNat_lt
  have := b.toNat_lt
  have : x.toNat * y.toNat ≤ (2 ^ 16 - 1) * (2 ^ 16 - 1) := Nat.mul_le_mul (by omega) (by omega)
  simp only [mulAddAdd, UInt32.toNat_add, UInt32.toNat_mul, UInt32.toNat_toUInt16,
    UInt16.toNat_toUInt32, UInt32.toNat_shiftRight, Nat.shiftRight_eq_div_pow, UInt32.toNat_ofNat,
    Nat.reduceMod, Nat.reducePow] at *
  generalize x.toNat * y.toNat = p at *
  omega

/-! ## `UInt32` -/

/-- `x + y + c` as its low word and a carry out. -/
@[inline, expose] public def UInt32.addWithCarry (x y : UInt32) (c : Bool) : UInt32 × Bool :=
  let t := x.toUInt64 + y.toUInt64 + c.toUInt64
  (t.toUInt32, t >>> 32 != 0)

/-- `x - y - b` as its low word, wrapping, and a borrow out. -/
@[inline, expose] public def UInt32.subWithBorrow (x y : UInt32) (b : Bool) : UInt32 × Bool :=
  let t := x.toUInt64 - y.toUInt64 - b.toUInt64
  (t.toUInt32, t >>> 32 != 0)

/-- `x * y + a + b` as its low word and its high word. -/
@[inline, expose] public def UInt32.mulAddAdd (x y a b : UInt32) : UInt32 × UInt32 :=
  let t := x.toUInt64 * y.toUInt64 + a.toUInt64 + b.toUInt64
  (t.toUInt32, (t >>> 32).toUInt32)

private theorem UInt32.high_ne_zero (t : UInt64) : (t >>> 32 != 0) = decide (2 ^ 32 ≤ t.toNat) := by
  rw [Bool.eq_iff_iff]
  simp [← UInt64.toNat_inj, Nat.shiftRight_eq_div_pow]

public theorem UInt32.addWithCarry_spec (x y : UInt32) (c : Bool) :
    (x.addWithCarry y c).1.toNat + (x.addWithCarry y c).2.toNat * 2 ^ 32 =
      x.toNat + y.toNat + c.toNat := by
  have := x.toNat_lt
  have := y.toNat_lt
  rw [addWithCarry, high_ne_zero]
  cases c <;> simp [UInt64.toNat_add, Bool.toUInt64, Bool.toNat] <;> split <;> omega

public theorem UInt32.subWithBorrow_spec (x y : UInt32) (b : Bool) :
    (x.subWithBorrow y b).1.toNat + y.toNat + b.toNat =
      x.toNat + (x.subWithBorrow y b).2.toNat * 2 ^ 32 := by
  have := x.toNat_lt
  have := y.toNat_lt
  rw [subWithBorrow, high_ne_zero]
  cases b <;>
    simp only [UInt64.toNat_toUInt32, UInt64.toNat_sub, UInt32.toNat_toUInt64, Bool.toUInt64,
      Bool.toNat, Bool.cond_false, Bool.cond_true, UInt64.toNat_zero, UInt64.toNat_one,
      Bool.false_eq_true, ↓reduceIte, Bool.cond_decide, Nat.reducePow] <;> split <;> omega

public theorem UInt32.mulAddAdd_spec (x y a b : UInt32) :
    (x.mulAddAdd y a b).1.toNat + (x.mulAddAdd y a b).2.toNat * 2 ^ 32 =
      x.toNat * y.toNat + a.toNat + b.toNat := by
  have := x.toNat_lt
  have := y.toNat_lt
  have := a.toNat_lt
  have := b.toNat_lt
  have : x.toNat * y.toNat ≤ (2 ^ 32 - 1) * (2 ^ 32 - 1) := Nat.mul_le_mul (by omega) (by omega)
  simp only [mulAddAdd, UInt64.toNat_add, UInt64.toNat_mul, UInt64.toNat_toUInt32,
    UInt32.toNat_toUInt64, UInt64.toNat_shiftRight, Nat.shiftRight_eq_div_pow, UInt64.toNat_ofNat,
    Nat.reduceMod, Nat.reducePow] at *
  generalize x.toNat * y.toNat = p at *
  omega
