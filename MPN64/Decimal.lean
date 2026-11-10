/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import MPN.Generic.Radix
public import MPN64.Generic.Ops64
public import MPN.DecChunks
public import MPN.DecWord
import Std.Data.String.ToNat

/-!
# Decimal strings

`main`'s decimal strings by chunks (`MPN.DecChunks`) with chunks of nineteen decimal digits, the
largest power of ten below `β` (`dec64`): `toDecimal` divides by `10¹⁹` until nothing is left,
and `DecChunks.step` reads nineteen digits at a time and adds them to the limbs, by `main`'s
`WordArray.divRem1A` and `mulAddA` (`MPN.DecWord`). Both take quadratic time; `Num.toDecimal` and
`Num.ofDecimal?` switch to divide and conquer (`NatOps.toDec`, `NatOps.fromDec`) on long numbers.
-/

open ScalarArray UInt64Array

namespace MPN.W64

/-! ## Chunks of nineteen digits -/

/-- The state of reading decimal digits, with unboxed fields, for `DecChunks`. -/
public structure DecState where
  acc : UInt64Array
  chunk : UInt64
  count : UInt32

/-- The value of an array, as `DecChunks` reads it. -/
public theorem decVA_eq (x : UInt64Array) : DecChunks.vA x = x.toNat := (toNat_eq_valAt x).symm

/-- Decimal strings by chunks of nineteen digits, the largest power of ten below `β`. -/
public instance dec64 : DecOps UInt64Array UInt64 where
  k := 19
  one_le_k := by decide
  k_lt := by decide
  kU := 19
  toNat_kU := rfl
  base := 10000000000000000000
  val_base := rfl
  pow10 j := (10 ^ j).toUInt64
  val_pow10 j hj := by
    show (10 ^ j).toUInt64.toNat = 10 ^ j
    have : 10 ^ j ≤ 10 ^ 19 := Nat.pow_le_pow_right (by decide) hj
    rw [Nat.toUInt64_eq, UInt64.toNat_ofNat', Nat.mod_eq_of_lt (by lia)]
  empty := UInt64Array.replicate 0 0
  vA_empty := by rw [decVA_eq]; simp [toNat_eq_valAt]
  isZero := WordArray.isZeroA
  isZero_iff := WordArray.isZeroA_iff
  divRem a := WordArray.divRem1InA 1 div1RecipU a 10000000000000000000
  divRem_spec a := WordArray.divRem1InA_spec 1 div1RecipU a _ (by decide)
  mulAdd := WordArray.mulAddA 1
  vA_mulAdd a m v _ := WordArray.mulAddA_spec 1 a m v
  chunkWord x := x
  toNat_chunkWord _ := rfl
  chunk0 := 0
  val_chunk0 := rfl
  push c d := c * 10 + d.toUInt64
  val_push c d hc hd := by
    show (c * 10 + d.toUInt64).toNat = c.toNat * 10 + d.toNat
    change c.toNat < 10 ^ 18 at hc
    rw [UInt64.toNat_add, UInt64.toNat_mul, UInt32.toNat_toUInt64]
    simp only [UInt64.reduceToNat]
    rw [Nat.mod_eq_of_lt (a := c.toNat * 10) (by lia), Nat.mod_eq_of_lt (by lia)]
  St := DecState
  mkSt := DecState.mk
  acc := DecState.acc
  chunk := DecState.chunk
  count := DecState.count
  acc_mkSt _ _ _ := rfl
  chunk_mkSt _ _ _ := rfl
  count_mkSt _ _ _ := rfl

/-- The decimal digits of `a`, like `Nat.repr`, by chunks of nineteen digits. -/
public def toDecimal (a : UInt64Array) : String := DecChunks.toDecimal a

public theorem toDecimal_eq (a : UInt64Array) : toDecimal a = Nat.repr a.toNat := by
  rw [toDecimal, DecChunks.toDecimal_eq, decVA_eq]

/-- The limbs of the digits of `l` by chunks, skipping `_`. -/
public theorem toNat_finish_foldl (l : List Char) (hl : ∀ c ∈ l, c.isDigit = true ∨ c = '_') :
    (DecChunks.finish (l.foldl DecChunks.step (DecChunks.init UInt64Array))).toNat =
      Nat.ofDigitChars 10 (l.filter (· != '_')) 0 := by
  rw [← decVA_eq]; exact DecChunks.vA_finish_foldl l hl

/-! ## Divide and conquer

`main`'s `DecChunks.toDecimalWith` and `DecChunks.ofDecimalWith` on `ops64`, whose numbers are the
arrays themselves.
-/

/-- The size below which divide and conquer writes digits by chunks. -/
public def decBaseSize : Nat := 16

/-- The size, in digits, below which divide and conquer reads digits by chunks. -/
public def parseBaseSize : Nat := 300

private theorem hto (x : UInt64Array) : DecChunks.vA (id x) = ops64.val x := by
  rw [ops64_val, id, decVA_eq]

private theorem hof (a : UInt64Array) : ops64.val (id a) = DecChunks.vA a := by
  rw [ops64_val, id, decVA_eq]

/--
The decimal digits of `a`: by chunks of nineteen digits below `strDC` limbs, and by divide and
conquer from `strDC` limbs (`NatOps.toDec`), down to `decBaseSize` limbs.
-/
public def toDecimalWith (strDC : Nat) (a : UInt64Array) : String :=
  DecChunks.toDecimalWith ops64 id id strDC decBaseSize a

public theorem toDecimalWith_eq (strDC : Nat) (a : UInt64Array) :
    toDecimalWith strDC a = Nat.repr a.toNat := by
  rw [toDecimalWith, DecChunks.toDecimalWith_eq _ _ _ hto hof, decVA_eq]

/--
The number that a string of decimal digits denotes, like `String.toNat?`: from `19 parseDC`
digits by divide and conquer (`NatOps.fromDec`), and below by chunks of nineteen digits.
-/
public def ofDecimalWith (parseDC : Nat) (s : String) : Option UInt64Array :=
  if isNatFast s then some (DecChunks.ofDecimalWith ops64 id id parseDC parseBaseSize s) else none

public theorem ofDecimalWith_eq (parseDC : Nat) (s : String) :
    (ofDecimalWith parseDC s).map UInt64Array.toNat = s.toNat? := by
  by_cases h : s.isNat = true
  · rw [ofDecimalWith, isNatFast_eq, ite_eq_left h, Option.map_some,
      DecChunks.ofDecimalWith_spec _ _ _ hto hof _ _ s h, decVA_eq]
  · rw [ofDecimalWith, isNatFast_eq, ite_eq_right h, String.toNat?_eq_none (by simpa using h),
      Option.map_none]

/-- The decimal digits of `a`, like `Nat.repr a.toNat`. -/
public def Num.toDecimal (a : UInt64Array) : String := toDecimalWith config.strDC a

@[simp] public theorem Num.toDecimal_eq (a : UInt64Array) : Num.toDecimal a = Nat.repr a.toNat :=
  toDecimalWith_eq ..

/-- The number that a string of decimal digits denotes, like `String.toNat?`. -/
public def Num.ofDecimal? (s : String) : Option UInt64Array := ofDecimalWith config.parseDC s

@[simp] public theorem Num.ofDecimal?_eq (s : String) :
    (Num.ofDecimal? s).map UInt64Array.toNat = s.toNat? :=
  ofDecimalWith_eq ..

end MPN.W64
