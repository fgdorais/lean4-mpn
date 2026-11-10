/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import MPN32.Add
public import MPN32.Div.Limb
public import MPN32.Mul.Limb
public import MPN.Generic.Radix
public import MPN.DecChunks
public import MPN.DecWord
public import MPN32.Basic
public import MPN32.Arch.UIntArray

/-!
# Decimal strings

`main`'s decimal strings by chunks (`MPN.DecChunks`) with chunks of nine decimal digits, the
largest power of ten below `β` (`dec32`): `toDecimal` divides by `10⁹` until nothing is left, and
`DecChunks.step` reads nine digits at a time and adds them to the limbs, by `main`'s
`WordArray.divRem1A` and `mulAddA` (`MPN.DecWord`). Both take quadratic time.
-/

open ScalarArray

namespace MPN.W32

/-! ## Chunks of nine digits -/

/-- `10⁹`, the largest power of ten below `β`. -/
public abbrev chunkBase : UInt32 := 1000000000

/-- The state of reading decimal digits, with unboxed fields, for `DecChunks`. -/
public structure DecState where
  acc : UInt32Array
  chunk : UInt32
  count : UInt32

/-- The value of an array, as `DecChunks` reads it. -/
public theorem decVA_eq (a : UInt32Array) : DecChunks.vA a = toNat a :=
  (toNat_array_eq_valAt a).symm

/-- Decimal strings by chunks of nine digits, the largest power of ten below `β`. -/
public instance dec32 : DecOps UInt32Array UInt32 where
  k := 9
  one_le_k := by decide
  k_lt := by decide
  kU := 9
  toNat_kU := rfl
  base := chunkBase
  val_base := rfl
  pow10 j := (10 ^ j).toUInt32
  val_pow10 j hj := by
    show (10 ^ j).toUInt32.toNat = 10 ^ j
    have : 10 ^ j ≤ 10 ^ 9 := Nat.pow_le_pow_right (by decide) hj
    rw [Nat.toUInt32_eq, UInt32.toNat_ofNat', Nat.mod_eq_of_lt (by lia)]
  empty := .empty
  vA_empty := by rw [decVA_eq, toNat_toSlice]; simp
  isZero := WordArray.isZeroA
  isZero_iff := WordArray.isZeroA_iff
  divRem a := WordArray.divRem1InA 0 div1RecipU a chunkBase
  divRem_spec a := WordArray.divRem1InA_spec 0 div1RecipU a _ (by decide)
  mulAdd := WordArray.mulAddA 0
  vA_mulAdd a m v _ := WordArray.mulAddA_spec 0 a m v
  chunkWord x := x.toUInt64
  toNat_chunkWord x := UInt32.toNat_toUInt64 x
  chunk0 := 0
  val_chunk0 := rfl
  push c d := c * 10 + d
  val_push c d hc hd := by
    show (c * 10 + d).toNat = c.toNat * 10 + d.toNat
    change c.toNat < 10 ^ 8 at hc
    rw [UInt32.toNat_add, UInt32.toNat_mul]
    simp only [UInt32.reduceToNat]
    rw [Nat.mod_eq_of_lt (a := c.toNat * 10) (by lia), Nat.mod_eq_of_lt (by lia)]
  St := DecState
  mkSt := DecState.mk
  acc := DecState.acc
  chunk := DecState.chunk
  count := DecState.count
  acc_mkSt _ _ _ := rfl
  chunk_mkSt _ _ _ := rfl
  count_mkSt _ _ _ := rfl

/-- The decimal digits of trimmed limbs, like `Nat.repr`, by chunks of nine digits. -/
public def toDecimal (a : UInt32Array) (_h : isTrimmed a = true) : String := DecChunks.toDecimal a

public theorem toDecimal_eq (a : UInt32Array) (h : isTrimmed a = true) :
    toDecimal a h = Nat.repr (toNat a) := by
  rw [toDecimal, DecChunks.toDecimal_eq, decVA_eq]

/-- The limbs of the digits of `l` by chunks, skipping `_`. -/
public theorem toNat_finish_foldl (l : List Char) (hl : ∀ c ∈ l, c.isDigit = true ∨ c = '_') :
    toNat (DecChunks.finish (A := UInt32Array)
        (l.foldl DecChunks.step (DecChunks.init UInt32Array))) =
      Nat.ofDigitChars 10 (l.filter (· != '_')) 0 := by
  rw [← decVA_eq]; exact DecChunks.vA_finish_foldl l hl

end MPN.W32
