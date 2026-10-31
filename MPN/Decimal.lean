/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import MPN.Generic.Radix
public import MPN.Generic.Ops64
public import MPN.DecChunks
import Std.Data.String.ToNat

/-!
# Decimal strings

`main`'s decimal strings by chunks (`MPN.DecChunks`) with chunks of nineteen decimal digits, the
largest power of ten below `β` (`dec64`): `toDecimal` divides by `10¹⁹` with `divRem1` until
nothing is left, and `DecChunks.step` reads nineteen digits at a time and adds them to the limbs
with `mul1` (`mulAddLimb`). Both take quadratic time; `Num.toDecimal` and `Num.ofDecimal?` switch
to divide and conquer (`NatOps.toDec`, `NatOps.fromDec`) on long numbers. Like `ops64`, the limb
operations check that their arrays are small enough (`fits`) and otherwise compute with `Nat`,
which cannot happen.
-/

open ScalarArray UInt64Array

namespace MPN

/-! ## Chunks of nineteen digits -/

/-- Whether `a` is zero. -/
public def isZero (a : UInt64Array) : Bool :=
  if a.size == 0 then true
  else if fits (a.size + 1) then MPN.log2 a.toUSlice == 0 && a[0]! == 0 else a.toNat == 0

public theorem isZero_iff (a : UInt64Array) : isZero a = true ↔ a.toNat = 0 := by
  unfold isZero
  split
  · rename_i h0
    simp only [beq_iff_eq] at h0
    simp [toNat_eq_valAt, h0]
  split
  · rename_i h
    have hS := lt_of_fits h
    rw [Bool.and_eq_true, beq_iff_eq, beq_iff_eq, log2_eq, toUSlice_toNat a (by lia)]
    have hv : a.toNat % 2 ^ 64 = a[0]!.toNat := by
      rw [toNat_eq_valAt]
      rcases Nat.eq_zero_or_pos a.size with h0 | h0
      · rw [h0, valAt_zero, Nat.zero_mod, getElem!_neg a 0 (by lia)]; rfl
      · rw [show a.size = (a.size - 1) + 1 by lia, valAt_succ, Nat.add_mul_mod_self_left,
          Nat.mod_eq_of_lt (UInt64.toNat_lt _)]
    constructor
    · rintro ⟨h₁, h₂⟩
      have : a.toNat < 2 := by
        rcases Nat.eq_zero_or_pos a.toNat with e | e
        · lia
        · have := Nat.lt_log2_self (n := a.toNat); rw [h₁] at this; simpa using this
      rw [h₂] at hv
      simp at hv
      lia
    · intro h0
      refine ⟨by rw [h0]; rfl, ?_⟩
      rw [h0, Nat.zero_mod] at hv
      exact UInt64.toNat_inj.1 (by rw [← hv]; rfl)
  · simp

/-- `(a / d, a mod d)` by `divRem1`. -/
public def divRem1N (a : UInt64Array) (d : UInt64) : UInt64Array × UInt64 :=
  if fits (a.size + 1) then MPN.divRem1 (UInt64Array.replicate a.size 0).toUSlice a.toUSlice d
  else (ofNat (a.toNat / d.toNat), (a.toNat % d.toNat).toUInt64)

public theorem divRem1N_spec (a : UInt64Array) (d : UInt64) (hd : 0 < d.toNat) :
    (divRem1N a d).1.toNat = a.toNat / d.toNat ∧ (divRem1N a d).2.toNat = a.toNat % d.toNat := by
  unfold divRem1N
  split
  · rename_i h
    have hS := lt_of_fits h
    have hz : (UInt64Array.replicate a.size 0).toUSlice.size.toNat = a.size := by
      rw [size_toUSlice _ (by simp; lia)]; simp
    have ha : a.toUSlice.size.toNat = a.size := size_toUSlice _ (by lia)
    have har : a.toUSlice.size ≤ (UInt64Array.replicate a.size 0).toUSlice.size :=
      USize.le_iff_toNat_le.2 (by rw [hz, ha]; exact Nat.le_refl _)
    have h₁ := valAt_divRem1 _ a.toUSlice d hd har
    have h₂ := toNat_divRem1_snd _ a.toUSlice d hd har
    rw [toUSlice_toNat a (by lia), ha, start_toUSlice, USize.toNat_zero] at h₁
    rw [toUSlice_toNat a (by lia)] at h₂
    refine ⟨?_, h₂⟩
    rw [toNat_eq_valAt, size_divRem1]
    simpa using h₁
  · refine ⟨toNat_ofNat _, ?_⟩
    rw [Nat.toUInt64_eq, UInt64.toNat_ofNat', Nat.mod_eq_of_lt
      (Nat.lt_trans (Nat.mod_lt _ hd) d.toNat_lt)]

/-- `a m + v`, by `mul1` with the carry in `v`. -/
public def mulAddLimb (a : UInt64Array) (m v : UInt64) : UInt64Array :=
  if fits (a.size + 2) then
    let p := MPN.mul1 (UInt64Array.replicate (a.size + 1) 0).toUSlice a.toUSlice m v
    p.1.set! a.size p.2
  else ofNat (a.toNat * m.toNat + v.toNat)

public theorem toNat_mulAddLimb (a : UInt64Array) (m v : UInt64) :
    (mulAddLimb a m v).toNat = a.toNat * m.toNat + v.toNat := by
  unfold mulAddLimb
  split
  · rename_i h
    have hS := lt_of_fits h
    have hz : (UInt64Array.replicate (a.size + 1) 0).toUSlice.size.toNat = a.size + 1 := by
      rw [size_toUSlice _ (by simp; lia)]; simp
    have ha : a.toUSlice.size.toNat = a.size := size_toUSlice _ (by lia)
    have h₁ := valAt_mul1 (UInt64Array.replicate (a.size + 1) 0).toUSlice a.toUSlice m v
      (USize.le_iff_toNat_le.2 (by rw [hz, ha]; lia))
    rw [ha, start_toUSlice, USize.toNat_zero, toUSlice_toNat a (by lia)] at h₁
    dsimp only
    rw [toNat_eq_valAt, size_set!, size_mul1, array_toUSlice, size_replicate,
      UInt64Array.valAt_add, valAt_one, Nat.zero_add, getElem!_set!_self _ _ _ (by simp),
      valAt_congr (b := (MPN.mul1 (UInt64Array.replicate (a.size + 1) 0).toUSlice a.toUSlice m
        v).1) _ fun i _ hi => getElem!_set!_of_ne _ _ (by lia)]
    exact h₁
  · exact toNat_ofNat _

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
  isZero := isZero
  isZero_iff a := by rw [decVA_eq]; exact isZero_iff a
  divRem a := divRem1N a 10000000000000000000
  divRem_spec a := by
    rw [decVA_eq, decVA_eq]
    exact divRem1N_spec a _ (by decide)
  mulAdd := mulAddLimb
  vA_mulAdd a m v _ := by rw [decVA_eq, decVA_eq]; exact toNat_mulAddLimb a m v
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

/-! ## Divide and conquer -/

/-- The decimal digits of limbs by chunks (`toDecimal`), the base case of `NatOps.toDec`. -/
public def decBase (x : UInt64Array) : String := toDecimal x

private theorem decBase_spec (x : UInt64Array) :
    (decBase x).toList = Nat.toDigits 10 (ops64.val x) := by
  rw [decBase, toDecimal_eq, Nat.toList_repr, ops64_val]

/-- The size below which divide and conquer writes digits by chunks (`decBase`). -/
public def decBaseSize : Nat := 16

/--
The decimal digits of `a`: by chunks of nineteen digits below `strDC` limbs (`toDecimal`), and by
divide and conquer from `strDC` limbs (`NatOps.toDec`), down to `decBaseSize` limbs.
-/
public def toDecimalWith (strDC : Nat) (a : UInt64Array) : String :=
  if strDC ≤ a.size then ops64.toDec decBase decBaseSize a else toDecimal a

public theorem toDecimalWith_eq (strDC : Nat) (a : UInt64Array) :
    toDecimalWith strDC a = Nat.repr a.toNat := by
  unfold toDecimalWith
  split
  · rw [← String.toList_inj, ops64.toDec_spec decBase decBaseSize decBase_spec, Nat.toList_repr,
      ops64_val]
  · exact toDecimal_eq a

/-- The value of `len` digits of `arr` from `start` by chunks, the base case of `fromDec`. -/
public def parseBase (arr : Array Char) (start len : Nat) : UInt64Array :=
  (DecChunks.finish (arr.foldl DecChunks.step (DecChunks.init UInt64Array) start (start + len)))

private theorem foldl_chars (arr : Array Char) (start len : Nat) :
    arr.foldl DecChunks.step (DecChunks.init UInt64Array) start (start + len) =
      (NatOps.chars arr start len).foldl DecChunks.step (DecChunks.init UInt64Array) := by
  rw [Array.foldl_eq_foldl_extract, ← Array.foldl_toList, Array.toList_extract,
    List.extract_eq_take_drop, Nat.add_sub_cancel_left, NatOps.chars]

/-- The size, in digits, below which divide and conquer reads digits by chunks (`parseBase`). -/
public def parseBaseSize : Nat := 300

private theorem parseBase_spec (arr : Array Char) (hd : ∀ c ∈ arr.toList, c.isDigit = true)
    (start len : Nat) :
    ops64.val (parseBase arr start len) =
      Nat.ofDigitChars 10 (NatOps.chars arr start len) 0 := by
  have hc : ∀ c ∈ NatOps.chars arr start len, c.isDigit = true := fun c hc =>
    hd c (List.mem_of_mem_drop (List.mem_of_mem_take hc))
  rw [ops64_val, parseBase, foldl_chars, toNat_finish_foldl _ (fun c h => Or.inl (hc c h))]
  congr 1
  apply List.filter_eq_self.2
  intro c h
  have := hc c h
  simp only [bne_iff_ne, ne_eq]
  rintro rfl
  exact absurd this (by decide)

/--
The number that a string of decimal digits denotes, like `String.toNat?`: from `19 parseDC`
digits by divide and conquer (`NatOps.fromDec`), and below by chunks of nineteen digits.
-/
public def ofDecimalWith (parseDC : Nat) (s : String) : Option UInt64Array :=
  if s.isNat then
    if 19 * parseDC ≤ s.length then
      some (ops64.fromDec parseBase parseBaseSize (s.toList.filter (· != '_')).toArray)
    else some (DecChunks.finish (s.foldl DecChunks.step (DecChunks.init UInt64Array)))
  else
    none

public theorem ofDecimalWith_eq (parseDC : Nat) (s : String) :
    (ofDecimalWith parseDC s).map UInt64Array.toNat = s.toNat? := by
  by_cases h : s.isNat = true
  · rw [ofDecimalWith, ite_eq_left h, String.toNat?_eq_some_ofDigitChars h]
    split
    · rw [Option.map_some, Option.some.injEq]
      have hd : ∀ c ∈ (s.toList.filter (· != '_')).toArray.toList, c.isDigit = true := by
        intro c hc
        simp only [List.mem_filter, bne_iff_ne, ne_eq] at hc
        rcases (String.isNat_iff.1 h).2.1 c hc.1 with h' | h'
        · exact h'
        · exact absurd h' hc.2
      have := ops64.fromDec_spec parseBase parseBaseSize _
        (fun st ln _ => parseBase_spec _ hd st ln)
      rw [ops64_val] at this
      rw [this, List.toList_toArray]
    · rw [Option.map_some, Option.some.injEq, String.foldl_eq_foldl_toList]
      exact toNat_finish_foldl _ (String.isNat_iff.1 h).2.1
  · rw [ofDecimalWith, ite_eq_right h, String.toNat?_eq_none (by simpa using h), Option.map_none]

/-- The decimal digits of `a`, like `Nat.repr a.toNat`. -/
public def Num.toDecimal (a : UInt64Array) : String := toDecimalWith config.strDC a

@[simp] public theorem Num.toDecimal_eq (a : UInt64Array) : Num.toDecimal a = Nat.repr a.toNat :=
  toDecimalWith_eq ..

/-- The number that a string of decimal digits denotes, like `String.toNat?`. -/
public def Num.ofDecimal? (s : String) : Option UInt64Array := ofDecimalWith config.parseDC s

@[simp] public theorem Num.ofDecimal?_eq (s : String) :
    (Num.ofDecimal? s).map UInt64Array.toNat = s.toNat? :=
  ofDecimalWith_eq ..

end MPN
