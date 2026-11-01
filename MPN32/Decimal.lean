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
public import MPN32.ValAt
public import MPN32.Arch.UIntArray

/-!
# Decimal strings

`main`'s decimal strings by chunks (`MPN.DecChunks`) with chunks of nine decimal digits, the
largest power of ten below `β` (`dec32`): `toDecimal` divides by `10⁹` with `divRem1` until nothing
is left, and `DecChunks.step` reads nine digits at a time and adds them to the limbs
(`mulAddLimb`). Both take quadratic time.
-/

open ScalarArray

namespace MPN.W32

/-! ## Chunks of nine digits -/

/-- `10⁹`, the largest power of ten below `β`. -/
public abbrev chunkBase : UInt32 := 1000000000

private theorem pos_of_isTrimmed {a : UInt32Array} (h : isTrimmed a = true) (hz : a.size ≠ 0) :
    0 < toNat a := by
  rw [toNat_toSlice]
  rw [isTrimmed_iff] at h
  exact h.ofLimbs_pos (by simpa [← List.length_eq_zero_iff] using hz)

private theorem divRem1_chunk (a : UInt32Array) :
    toNat (divRem1 a chunkBase).1 = toNat a / 10 ^ 9 ∧
      (divRem1 a chunkBase).2.toNat = toNat a % 10 ^ 9 := by
  have ⟨h, hr⟩ := divRem1_spec a chunkBase (by decide)
  have hd : chunkBase.toNat = 10 ^ 9 := rfl
  rw [hd] at h hr
  constructor
  · rw [← h, Nat.add_comm, Nat.add_mul_div_right _ _ (by decide), Nat.div_eq_of_lt hr,
      Nat.zero_add]
  · rw [← h, Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hr]

/--
Whether `a` is zero: at once when its top limb is not, and otherwise when `trim` leaves no limbs.
-/
@[inline] public def isZeroA (a : UInt32Array) : Bool :=
  if a.size = 0 then true else if a[a.size - 1]! != 0 then false else (trim a).size == 0

public theorem isZeroA_iff (a : UInt32Array) : isZeroA a = true ↔ toNat a = 0 := by
  have key : isZeroA a = true ↔ (trim a).size = 0 := by
    unfold isZeroA
    split
    · rename_i h
      simp only [true_iff]
      have := toNat_trim a
      exact Decidable.byContradiction fun hs => by
        have := pos_of_isTrimmed (isTrimmed_trim a) hs
        rw [toNat_trim, toNat_of_size_eq_zero (by simpa using h)] at this
        lia
    · split
      · rename_i h0 hn
        simp only [Bool.false_eq_true, false_iff]
        intro hs
        have hp : 0 < toNat a := by
          have ht : a[a.size - 1]!.toNat ≠ 0 := fun e =>
            (bne_iff_ne.1 hn) (UInt32.toNat_inj.1 (by rw [e]; rfl))
          rw [toNat_array_eq_valAt, show a.size = (a.size - 1) + 1 by lia, UInt32Array.valAt_add,
            UInt32Array.valAt_one, Nat.zero_add]
          have := Nat.mul_le_mul_left (2 ^ (32 * (a.size - 1))) (Nat.one_le_iff_ne_zero.2 ht)
          have := Nat.two_pow_pos (32 * (a.size - 1))
          lia
        have h0' := toNat_of_size_eq_zero (s := (trim a).toSlice) (by simpa using hs)
        rw [toNat_trim] at h0'
        lia
      · exact beq_iff_eq
  rw [key, ← toNat_trim a]
  constructor
  · intro h; exact toNat_of_size_eq_zero (by simpa using h)
  · intro h
    exact Decidable.byContradiction fun hs => by
      have := pos_of_isTrimmed (isTrimmed_trim a) hs
      lia

/-- The quotient, trimmed, and the remainder of `a` by `10⁹`. -/
public def divRemChunk (a : UInt32Array) : UInt32Array × UInt32 :=
  let p := divRem1 a chunkBase
  (trim p.1, p.2)

public theorem divRemChunk_spec (a : UInt32Array) :
    toNat (divRemChunk a).1 = toNat a / 10 ^ 9 ∧ (divRemChunk a).2.toNat = toNat a % 10 ^ 9 := by
  have ⟨h, hr⟩ := divRem1_spec a chunkBase (by decide)
  have hd : chunkBase.toNat = 10 ^ 9 := rfl
  rw [hd] at h hr
  simp only [divRemChunk, toNat_trim]
  constructor
  · rw [← h, Nat.add_comm, Nat.add_mul_div_right _ _ (by decide), Nat.div_eq_of_lt hr,
      Nat.zero_add]
  · rw [← h, Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hr]

/-- `a m + v`, trimmed. -/
public def mulAddLimb (a : UInt32Array) (m v : UInt32) : UInt32Array :=
  trim (addInto (mulRow a m) 0 (limbArray v))

public theorem toNat_mulAddLimb (a : UInt32Array) (m v : UInt32) (hv : v.toNat < m.toNat) :
    toNat (mulAddLimb a m v) = toNat a * m.toNat + v.toNat := by
  have hA : toNat a < 2 ^ (32 * a.size) := by
    have := toNat_lt a
    simpa using this
  have hfit : toNat (mulRow a m) + 2 ^ (32 * 0) * toNat (limbArray v) <
      2 ^ (32 * (mulRow a m).size) := by
    rw [toNat_mulRow, toNat_limbArray, size_mulRow, Nat.mul_zero, Nat.pow_zero, Nat.one_mul,
      UInt32Array.size_toSlice, Nat.min_self, Nat.sub_zero, Nat.mul_succ, Nat.pow_add]
    -- `a m + v < (a + 1) m ≤ β^n m < β^(n + 1)`.
    have h₁ : toNat a * m.toNat + v.toNat < (toNat a + 1) * m.toNat := by
      rw [Nat.succ_mul]; lia
    have h₂ : (toNat a + 1) * m.toNat ≤ 2 ^ (32 * a.size) * m.toNat := Nat.mul_le_mul_right _ hA
    have h₃ : 2 ^ (32 * a.size) * m.toNat ≤ 2 ^ (32 * a.size) * 2 ^ 32 :=
      Nat.mul_le_mul_left _ (Nat.le_of_lt m.toNat_lt)
    lia
  rw [mulAddLimb, toNat_trim, toNat_addInto_of_lt _ _ _ (by simp [limbArray]) hfit,
    toNat_mulRow, toNat_limbArray, Nat.mul_zero, Nat.pow_zero, Nat.one_mul]

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
  isZero := isZeroA
  isZero_iff a := by rw [decVA_eq]; exact isZeroA_iff a
  divRem := divRemChunk
  divRem_spec a := by rw [decVA_eq, decVA_eq]; exact divRemChunk_spec a
  mulAdd := mulAddLimb
  vA_mulAdd a m v h := by rw [decVA_eq, decVA_eq]; exact toNat_mulAddLimb a m v h
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
