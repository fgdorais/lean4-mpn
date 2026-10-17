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
  cases c <;> simp [UInt16.toNat_add, Bool.toUInt16, Bool.toNat] <;> split <;> lia

public theorem UInt8.subWithBorrow_spec (x y : UInt8) (b : Bool) :
    (x.subWithBorrow y b).1.toNat + y.toNat + b.toNat =
      x.toNat + (x.subWithBorrow y b).2.toNat * 2 ^ 8 := by
  have := x.toNat_lt
  have := y.toNat_lt
  rw [subWithBorrow, high_ne_zero]
  cases b <;>
    simp only [UInt16.toNat_toUInt8, UInt16.toNat_sub, UInt8.toNat_toUInt16, Bool.toUInt16,
      Bool.toNat, Bool.cond_false, Bool.cond_true, UInt16.toNat_zero, UInt16.toNat_one,
      Bool.false_eq_true, ↓reduceIte, Bool.cond_decide, Nat.reducePow] <;> split <;> lia

public theorem UInt8.mulAddAdd_spec (x y a b : UInt8) :
    (x.mulAddAdd y a b).1.toNat + (x.mulAddAdd y a b).2.toNat * 2 ^ 8 =
      x.toNat * y.toNat + a.toNat + b.toNat := by
  have := x.toNat_lt
  have := y.toNat_lt
  have := a.toNat_lt
  have := b.toNat_lt
  have : x.toNat * y.toNat ≤ (2 ^ 8 - 1) * (2 ^ 8 - 1) := Nat.mul_le_mul (by lia) (by lia)
  simp only [mulAddAdd, UInt16.toNat_add, UInt16.toNat_mul, UInt16.toNat_toUInt8,
    UInt8.toNat_toUInt16, UInt16.toNat_shiftRight, Nat.shiftRight_eq_div_pow, UInt16.toNat_ofNat,
    Nat.reduceMod, Nat.reducePow] at *
  generalize x.toNat * y.toNat = p at *
  lia

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
  cases c <;> simp [UInt32.toNat_add, Bool.toUInt32, Bool.toNat] <;> split <;> lia

public theorem UInt16.subWithBorrow_spec (x y : UInt16) (b : Bool) :
    (x.subWithBorrow y b).1.toNat + y.toNat + b.toNat =
      x.toNat + (x.subWithBorrow y b).2.toNat * 2 ^ 16 := by
  have := x.toNat_lt
  have := y.toNat_lt
  rw [subWithBorrow, high_ne_zero]
  cases b <;>
    simp only [UInt32.toNat_toUInt16, UInt32.toNat_sub, UInt16.toNat_toUInt32, Bool.toUInt32,
      Bool.toNat, Bool.cond_false, Bool.cond_true, UInt32.toNat_zero, UInt32.toNat_one,
      Bool.false_eq_true, ↓reduceIte, Bool.cond_decide, Nat.reducePow] <;> split <;> lia

public theorem UInt16.mulAddAdd_spec (x y a b : UInt16) :
    (x.mulAddAdd y a b).1.toNat + (x.mulAddAdd y a b).2.toNat * 2 ^ 16 =
      x.toNat * y.toNat + a.toNat + b.toNat := by
  have := x.toNat_lt
  have := y.toNat_lt
  have := a.toNat_lt
  have := b.toNat_lt
  have : x.toNat * y.toNat ≤ (2 ^ 16 - 1) * (2 ^ 16 - 1) := Nat.mul_le_mul (by lia) (by lia)
  simp only [mulAddAdd, UInt32.toNat_add, UInt32.toNat_mul, UInt32.toNat_toUInt16,
    UInt16.toNat_toUInt32, UInt32.toNat_shiftRight, Nat.shiftRight_eq_div_pow, UInt32.toNat_ofNat,
    Nat.reduceMod, Nat.reducePow] at *
  generalize x.toNat * y.toNat = p at *
  lia

/-! ## `UInt32` -/

/-- `x + y + c` as its low word and a carry out. -/
@[inline, expose] public def UInt32.addWithCarry (x y : UInt32) (c : Bool) : UInt32 × Bool :=
  let t := x.toUInt64 + y.toUInt64 + c.toUInt64
  (t.toUInt32, t >>> 32 != 0)

/-- `x - y - b` as its low word, wrapping, and a borrow out. -/
@[inline, expose] public def UInt32.subWithBorrow (x y : UInt32) (b : Bool) : UInt32 × Bool :=
  let t := x.toUInt64 - y.toUInt64 - b.toUInt64
  (t.toUInt32, t >>> 32 != 0)

/--
`x * y + a + b` as its low word and its high word. In a loop, `b` is the carry, and it joins last,
after `p = x y + a`, which is also used for the low word: with `x y + a + b` written as one sum,
LLVM adds the carry first, which puts the multiplication on the carry's dependency chain (on
AArch64 the multiply-accumulate `umaddl`, a chain of about 5 cycles per limb, against 2 here).
-/
@[inline, expose] public def UInt32.mulAddAdd (x y a b : UInt32) : UInt32 × UInt32 :=
  let p := x.toUInt64 * y.toUInt64 + a.toUInt64
  (p.toUInt32 + b, ((p + b.toUInt64) >>> 32).toUInt32)

private theorem UInt32.high_ne_zero (t : UInt64) : (t >>> 32 != 0) = decide (2 ^ 32 ≤ t.toNat) := by
  rw [Bool.eq_iff_iff]
  simp [← UInt64.toNat_inj, Nat.shiftRight_eq_div_pow]

/--
The low word of `p + h` from the low word of `p`. The steps of the compiled loops compute their low
word this way, as `lo p + h` with the carry `h`, and their carry from `p + h`: using `p` twice keeps
LLVM from adding the carry first, which would put the rest of the step on its dependency chain.
-/
public theorem UInt32.toUInt32_add (p : UInt64) (h : UInt32) :
    p.toUInt32 + h = (p + h.toUInt64).toUInt32 := by
  apply UInt32.toNat_inj.1
  simp only [UInt32.toNat_add, UInt64.toNat_toUInt32, UInt64.toNat_add, UInt32.toNat_toUInt64]
  have := h.toNat_lt
  lia

/-- The low word of `p - b` from the low word of `p`, as in `toUInt32_add`. -/
public theorem UInt32.toUInt32_sub (p : UInt64) (b : UInt32) :
    p.toUInt32 - b = (p - b.toUInt64).toUInt32 := by
  apply UInt32.toNat_inj.1
  simp only [UInt32.toNat_sub, UInt64.toNat_toUInt32, UInt64.toNat_sub, UInt32.toNat_toUInt64]
  have := b.toNat_lt
  have := p.toNat_lt
  lia

public theorem UInt32.addWithCarry_spec (x y : UInt32) (c : Bool) :
    (x.addWithCarry y c).1.toNat + (x.addWithCarry y c).2.toNat * 2 ^ 32 =
      x.toNat + y.toNat + c.toNat := by
  have := x.toNat_lt
  have := y.toNat_lt
  rw [addWithCarry, high_ne_zero]
  cases c <;> simp [UInt64.toNat_add, Bool.toUInt64, Bool.toNat] <;> split <;> lia

public theorem UInt32.subWithBorrow_spec (x y : UInt32) (b : Bool) :
    (x.subWithBorrow y b).1.toNat + y.toNat + b.toNat =
      x.toNat + (x.subWithBorrow y b).2.toNat * 2 ^ 32 := by
  have := x.toNat_lt
  have := y.toNat_lt
  rw [subWithBorrow, high_ne_zero]
  cases b <;>
    simp only [UInt64.toNat_toUInt32, UInt64.toNat_sub, UInt32.toNat_toUInt64, Bool.toUInt64,
      Bool.toNat, Bool.cond_false, Bool.cond_true, UInt64.toNat_zero, UInt64.toNat_one,
      Bool.false_eq_true, ↓reduceIte, Bool.cond_decide, Nat.reducePow] <;> split <;> lia

public theorem UInt32.mulAddAdd_spec (x y a b : UInt32) :
    (x.mulAddAdd y a b).1.toNat + (x.mulAddAdd y a b).2.toNat * 2 ^ 32 =
      x.toNat * y.toNat + a.toNat + b.toNat := by
  have := x.toNat_lt
  have := y.toNat_lt
  have := a.toNat_lt
  have := b.toNat_lt
  have : x.toNat * y.toNat ≤ (2 ^ 32 - 1) * (2 ^ 32 - 1) := Nat.mul_le_mul (by lia) (by lia)
  simp only [mulAddAdd, UInt32.toNat_add, UInt64.toNat_add, UInt64.toNat_mul,
    UInt64.toNat_toUInt32, UInt32.toNat_toUInt64, UInt64.toNat_shiftRight,
    Nat.shiftRight_eq_div_pow, UInt64.toNat_ofNat, Nat.reduceMod, Nat.reducePow] at *
  generalize x.toNat * y.toNat = p at *
  lia

/--
`addWithCarry` with the carry as a word, `0` or `1`. The compiled loops thread this carry, which
compiles to a shorter dependency chain than a `Bool`. As in `mulAddAdd`, the carry joins `x + y`
last, and that sum is also used for the low word, so that LLVM does not add the carry first.
-/
@[inline, expose] public def UInt32.addWithCarryWord (x y c : UInt32) : UInt32 × UInt32 :=
  let s := x.toUInt64 + y.toUInt64
  (s.toUInt32 + c, ((s + c.toUInt64) >>> 32).toUInt32)

/--
`x - y` with a carry word `c = 1 - b`, `0` or `1`, in place of the borrow `b`: `x + ~y + c`, which
is `x - y - b + 2 ^ 32`, by `addWithCarryWord`, whose carry out is `1` exactly when there is no
borrow out. A borrow taken from `x - y` last, as the sign of `x - y - b`, compiles to a compare and
a flag read on AArch64, which makes a longer dependency chain than the add and shift of
`addWithCarryWord`.
-/
@[inline, expose] public def UInt32.subWithCarryWord (x y c : UInt32) : UInt32 × UInt32 :=
  x.addWithCarryWord (~~~y) c

public theorem UInt32.addWithCarryWord_toUInt32 (x y : UInt32) (c : Bool) :
    x.addWithCarryWord y c.toUInt32 =
      ((x.addWithCarry y c).1, (x.addWithCarry y c).2.toUInt32) := by
  have := x.toNat_lt
  have := y.toNat_lt
  have h : c.toUInt32.toUInt64 = c.toUInt64 := by cases c <;> rfl
  simp only [addWithCarryWord, addWithCarry, h, Prod.mk.injEq]
  refine ⟨UInt32.toNat_inj.1 ?_, UInt32.toNat_inj.1 ?_⟩
  · -- The low words: `(s mod β + c) mod β = (s + c) mod β`.
    cases c <;> simp [UInt32.toNat_add, Bool.toUInt64, Bool.toUInt32] <;> lia
  · cases c <;> simp [UInt64.toNat_add, Bool.toUInt64, Bool.toUInt32, bne, ← UInt64.toNat_inj,
      Nat.shiftRight_eq_div_pow] <;> split <;> simp only [UInt32.toNat_zero, UInt32.toNat_one] <;>
      omega -- `lia` and `grind` fail or time out here

public theorem UInt32.subWithCarryWord_toUInt32 (x y : UInt32) (b : Bool) :
    x.subWithCarryWord y (!b).toUInt32 =
      ((x.subWithBorrow y b).1, (!(x.subWithBorrow y b).2).toUInt32) := by
  rw [subWithCarryWord, addWithCarryWord_toUInt32]
  have := x.toNat_lt
  have := y.toNat_lt
  have hy : (~~~y).toUInt64.toNat = 2 ^ 32 - 1 - y.toNat := by simp; lia
  simp only [addWithCarry, subWithBorrow, Prod.mk.injEq]
  refine ⟨?_, congrArg Bool.toUInt32 (Bool.eq_iff_iff.2 ?_)⟩
  · -- The low words: `x + (β - 1 - y) + (1 - b) ≡ x - y - b` mod `β`.
    rw [← UInt32.toNat_inj, UInt64.toNat_toUInt32, UInt64.toNat_toUInt32]
    cases b <;> simp only [UInt64.toNat_add, UInt64.toNat_sub, hy, UInt32.toNat_toUInt64,
      Bool.not_false, Bool.not_true, Bool.toUInt64, UInt64.reduceToNat, ite_true, ite_false,
      Bool.false_eq_true, Nat.reducePow] <;> lia
  · -- The carry out is `1` exactly when there is no borrow out.
    cases b <;> simp only [bne_iff_ne, ne_eq, ← UInt64.toNat_inj, UInt64.toNat_shiftRight,
      UInt64.toNat_add, UInt64.toNat_sub, hy, UInt32.toNat_toUInt64, Bool.not_false,
      Bool.not_true, Bool.toUInt64, UInt64.reduceToNat, Nat.shiftRight_eq_div_pow,
      Bool.not_eq_eq_eq_not, bne_eq_false_iff_eq, Bool.false_eq_true, ite_true, ite_false,
      Nat.reducePow, Nat.reduceMod] <;> lia

/--
`2 x + d + c` as its low word and its high word, the step of `mpn_sqr_diag_addlsh1`-style
squaring: twice a limb of the cross products plus a limb of the diagonal and the carry, which is
at most `2`.
-/
@[inline, expose] public def UInt32.dblAddAdd (x d c : UInt32) : UInt32 × UInt32 :=
  let p := x.toUInt64 + x.toUInt64 + d.toUInt64
  (p.toUInt32 + c, ((p + c.toUInt64) >>> 32).toUInt32)

private theorem UInt32.dblAddAdd_eq (x d c : UInt32) :
    x.dblAddAdd d c = ((x.toUInt64 + x.toUInt64 + d.toUInt64 + c.toUInt64).toUInt32,
      ((x.toUInt64 + x.toUInt64 + d.toUInt64 + c.toUInt64) >>> 32).toUInt32) := by
  simp only [dblAddAdd, toUInt32_add]

public theorem UInt32.dblAddAdd_spec (x d c : UInt32) :
    (x.dblAddAdd d c).1.toNat + (x.dblAddAdd d c).2.toNat * 2 ^ 32 =
      2 * x.toNat + d.toNat + c.toNat := by
  have := x.toNat_lt
  have := d.toNat_lt
  have := c.toNat_lt
  rw [dblAddAdd_eq]
  simp only [UInt64.toNat_add, UInt64.toNat_toUInt32, UInt32.toNat_toUInt64,
    UInt64.toNat_shiftRight, Nat.shiftRight_eq_div_pow, UInt64.toNat_ofNat, Nat.reduceMod,
    Nat.reducePow] at *
  lia

/-- Adding a carry alone: `x + 1`, with a carry out exactly when `x` is the largest word. -/
public theorem UInt32.addWithCarry_zero_true (x : UInt32) :
    x.addWithCarry 0 true = (x + 1, x == 0xFFFFFFFF) := by
  have := x.toNat_lt
  simp only [addWithCarry, Prod.mk.injEq]
  constructor
  · apply UInt32.toNat_inj.1
    simp [UInt32.toNat_add, Bool.toUInt64]
  · rw [Bool.eq_iff_iff]
    simp only [bne_iff_ne, ne_eq, beq_iff_eq, ← UInt64.toNat_inj, ← UInt32.toNat_inj]
    simp [UInt64.toNat_add, Nat.shiftRight_eq_div_pow, Bool.toUInt64]
    lia

/-- Subtracting a borrow alone: `x - 1`, with a borrow out exactly when `x` is zero. -/
public theorem UInt32.subWithBorrow_zero_true (x : UInt32) :
    x.subWithBorrow 0 true = (x - 1, x == 0) := by
  have := x.toNat_lt
  simp only [subWithBorrow, Prod.mk.injEq]
  constructor
  · apply UInt32.toNat_inj.1
    simp [UInt32.toNat_sub, Bool.toUInt64]
  · rw [Bool.eq_iff_iff]
    simp only [bne_iff_ne, ne_eq, beq_iff_eq, ← UInt64.toNat_inj, ← UInt32.toNat_inj]
    simp [UInt64.toNat_sub, Nat.shiftRight_eq_div_pow, Bool.toUInt64]
    lia

/--
`y - (x * v + c)` as its low word, wrapping, and the borrow word `b`, so that
`lo + x * v + c = y + b * 2³²`; the step of `subMul1`. The borrow fits in a word since
`x * v + c < 2⁶⁴`. It computes `y - (x * v + c)` modulo `2⁶⁴`, whose high word is `-b`.
-/
@[inline, expose] public def UInt32.subMul (y x v c : UInt32) : UInt32 × UInt32 :=
  let t := y.toUInt64 - (x.toUInt64 * v.toUInt64 + c.toUInt64)
  (t.toUInt32, ((0 : UInt64) - (t >>> 32)).toUInt32)

public theorem UInt32.subMul_spec (y x v c : UInt32) :
    (y.subMul x v c).1.toNat + x.toNat * v.toNat + c.toNat =
      y.toNat + (y.subMul x v c).2.toNat * 2 ^ 32 := by
  have := y.toNat_lt
  have := x.toNat_lt
  have := v.toNat_lt
  have := c.toNat_lt
  have : x.toNat * v.toNat ≤ (2 ^ 32 - 1) * (2 ^ 32 - 1) := Nat.mul_le_mul (by lia) (by lia)
  simp only [subMul, UInt64.toNat_sub, UInt64.toNat_add, UInt64.toNat_mul, UInt64.toNat_toUInt32,
    UInt32.toNat_toUInt64, UInt64.toNat_shiftRight, Nat.shiftRight_eq_div_pow, UInt64.toNat_ofNat,
    Nat.reduceMod, Nat.reducePow] at *
  generalize x.toNat * v.toNat = p at *
  lia

/--
`subMul` with the borrow `c` carried as `h = 2³² - 1 - c`, which shortens the dependency chain
from one limb to the next. The value `y - x v - c` lies in `[2³² - 2⁶⁴, 2³²)`, so adding
`2⁶⁴ - 2³²` makes it a word, whose low half is the limb and whose high half is `2³² - 1` minus the
next borrow: the step is `y - x v - (2³³ - 1) + h`, without the negation of the borrow.
-/
@[inline, expose] public def UInt32.subMulBiased (y x v h : UInt32) : UInt32 × UInt32 :=
  let p := y.toUInt64 - x.toUInt64 * v.toUInt64 - 0x1FFFFFFFF
  (p.toUInt32 + h, ((p + h.toUInt64) >>> 32).toUInt32)

private theorem UInt32.subMulBiased_eq (y x v h : UInt32) :
    y.subMulBiased x v h =
      ((y.toUInt64 - x.toUInt64 * v.toUInt64 - 0x1FFFFFFFF + h.toUInt64).toUInt32,
        ((y.toUInt64 - x.toUInt64 * v.toUInt64 - 0x1FFFFFFFF + h.toUInt64) >>> 32).toUInt32) := by
  simp only [subMulBiased, toUInt32_add]

public theorem UInt32.subMulBiased_not (y x v c : UInt32) :
    y.subMulBiased x v (~~~c) = ((y.subMul x v c).1, ~~~(y.subMul x v c).2) := by
  have := y.toNat_lt
  have := x.toNat_lt
  have := v.toNat_lt
  have := c.toNat_lt
  have : x.toNat * v.toNat ≤ (2 ^ 32 - 1) * (2 ^ 32 - 1) := Nat.mul_le_mul (by lia) (by lia)
  rw [subMulBiased_eq]
  simp only [subMul, Prod.mk.injEq]
  constructor
  · apply UInt32.toNat_inj.1
    simp only [UInt64.toNat_toUInt32, UInt64.toNat_sub, UInt64.toNat_add, UInt64.toNat_mul,
      UInt32.toNat_toUInt64, UInt32.toNat_not, UInt64.toNat_ofNat, Nat.reduceMod, Nat.reducePow,
      UInt32.size] at *
    generalize x.toNat * v.toNat = p at *
    lia
  · apply UInt32.toNat_inj.1
    simp only [UInt64.toNat_toUInt32, UInt64.toNat_sub, UInt64.toNat_add, UInt64.toNat_mul,
      UInt32.toNat_toUInt64, UInt32.toNat_not, UInt64.toNat_shiftRight, Nat.shiftRight_eq_div_pow,
      UInt64.toNat_ofNat, Nat.reduceMod, Nat.reducePow, UInt32.size] at *
    generalize x.toNat * v.toNat = p at *
    omega -- `lia` and `grind` fail or time out here
