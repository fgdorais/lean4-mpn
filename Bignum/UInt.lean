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

The last one cannot overflow since `(2ⁿ - 1) * (2ⁿ - 1) + (2ⁿ - 1) + (2ⁿ - 1) = 2²ⁿ - 1`.

The narrow types compute in the next wider type. `UInt64` has no wider type, so its addition and
subtraction detect overflow by comparison, and its multiplication is implemented in C
(`c/bignum.c`) with `unsigned __int128` where the compiler has it. The multiplication is split
into separate low and high word functions, since an extern returning a pair would allocate it;
their Lean definitions are the specification.
-/

/-- `x + y + c` as its low word and a carry out. -/
@[inline] public def UInt8.addWithCarry (x y : UInt8) (c : Bool) : UInt8 × Bool :=
  let t := x.toUInt16 + y.toUInt16 + c.toUInt16
  (t.toUInt8, t >>> 8 != 0)

/-- `x - y - b` as its low word, wrapping, and a borrow out. -/
@[inline] public def UInt8.subWithBorrow (x y : UInt8) (b : Bool) : UInt8 × Bool :=
  let t := x.toUInt16 - y.toUInt16 - b.toUInt16
  (t.toUInt8, t >>> 8 != 0)

/-- `x * y + a + b` as its low word and its high word. -/
@[inline] public def UInt8.mulAddAdd (x y a b : UInt8) : UInt8 × UInt8 :=
  let t := x.toUInt16 * y.toUInt16 + a.toUInt16 + b.toUInt16
  (t.toUInt8, (t >>> 8).toUInt8)

/-- `x + y + c` as its low word and a carry out. -/
@[inline] public def UInt16.addWithCarry (x y : UInt16) (c : Bool) : UInt16 × Bool :=
  let t := x.toUInt32 + y.toUInt32 + c.toUInt32
  (t.toUInt16, t >>> 16 != 0)

/-- `x - y - b` as its low word, wrapping, and a borrow out. -/
@[inline] public def UInt16.subWithBorrow (x y : UInt16) (b : Bool) : UInt16 × Bool :=
  let t := x.toUInt32 - y.toUInt32 - b.toUInt32
  (t.toUInt16, t >>> 16 != 0)

/-- `x * y + a + b` as its low word and its high word. -/
@[inline] public def UInt16.mulAddAdd (x y a b : UInt16) : UInt16 × UInt16 :=
  let t := x.toUInt32 * y.toUInt32 + a.toUInt32 + b.toUInt32
  (t.toUInt16, (t >>> 16).toUInt16)

/-- `x + y + c` as its low word and a carry out. -/
@[inline] public def UInt32.addWithCarry (x y : UInt32) (c : Bool) : UInt32 × Bool :=
  let t := x.toUInt64 + y.toUInt64 + c.toUInt64
  (t.toUInt32, t >>> 32 != 0)

/-- `x - y - b` as its low word, wrapping, and a borrow out. -/
@[inline] public def UInt32.subWithBorrow (x y : UInt32) (b : Bool) : UInt32 × Bool :=
  let t := x.toUInt64 - y.toUInt64 - b.toUInt64
  (t.toUInt32, t >>> 32 != 0)

/-- `x * y + a + b` as its low word and its high word. -/
@[inline] public def UInt32.mulAddAdd (x y a b : UInt32) : UInt32 × UInt32 :=
  let t := x.toUInt64 * y.toUInt64 + a.toUInt64 + b.toUInt64
  (t.toUInt32, (t >>> 32).toUInt32)

/-- `x + y + c` as its low word and a carry out. -/
@[inline] public def UInt64.addWithCarry (x y : UInt64) (c : Bool) : UInt64 × Bool :=
  let s := x + y
  let t := s + c.toUInt64
  -- At most one of the two additions wraps.
  (t, s < x || t < s)

/-- `x - y - b` as its low word, wrapping, and a borrow out. -/
@[inline] public def UInt64.subWithBorrow (x y : UInt64) (b : Bool) : UInt64 × Bool :=
  let d := x - y
  let t := d - b.toUInt64
  -- At most one of the two subtractions wraps.
  (t, x < y || d < b.toUInt64)

/-- The low word of `x * y + a + b`. -/
@[extern "bignum_uint64_mul_add_add_lo"]
public def UInt64.mulAddAddLo (x y a b : UInt64) : UInt64 :=
  (x.toNat * y.toNat + a.toNat + b.toNat).toUInt64

/-- The high word of `x * y + a + b`. -/
@[extern "bignum_uint64_mul_add_add_hi"]
public def UInt64.mulAddAddHi (x y a b : UInt64) : UInt64 :=
  ((x.toNat * y.toNat + a.toNat + b.toNat) / 2 ^ 64).toUInt64

/-- `x * y + a + b` as its low word and its high word. -/
@[inline] public def UInt64.mulAddAdd (x y a b : UInt64) : UInt64 × UInt64 :=
  (mulAddAddLo x y a b, mulAddAddHi x y a b)
