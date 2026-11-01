/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import MPN.Generic.Ops
public import MPN64.Num
public import MPN.Join

/-!
# The operations of the 64-bit instance of `NatOps`

`ops64With div` runs the base-generic algorithms on whole arrays of 64-bit limbs with the
operations of `MPN.Num` and the division `div`: the schoolbook division for the base-generic
divide-and-conquer division (`ops64B`, `MPN.Div.DC`), and `Num.divMod` for the others (`ops64`,
`MPN.Generic.Ops64`). Those are proved for arrays of fewer than `USize.size`
limbs, which every array that fits in memory has, but which the logical model of arrays does not
know; so each operation checks that its operands are small enough (`fits`, on constants that are
machine words), and otherwise computes with `Nat` (`ofNatN`). That branch cannot run: it would
need arrays of more than `2³¹` limbs on a 32-bit platform or `2⁶²` on a 64-bit one.
-/

open ScalarArray UInt64Array

namespace MPN.W64

/-! ## Sizes -/

/-- Whether `n` is below `USize.size`, decided on constants that are machine words. -/
@[inline] public def fits (n : Nat) : Bool :=
  n < 2147483648 || (System.Platform.numBits == 64 && n < 4611686018427387904)

public theorem lt_of_fits {n : Nat} (h : fits n = true) : n < USize.size := by
  simp only [fits, Bool.or_eq_true, decide_eq_true_eq, Bool.and_eq_true, beq_iff_eq] at h
  have := USize.size_eq
  rcases h with h | ⟨h₁, h₂⟩
  · rcases this with e | e <;> rw [e] <;> lia
  · rw [USize.size, h₁]; lia

/-! ## The fallback -/

/-- The `len` low limbs of `n`: `main`'s `WordArray.ofNatLen`, by halves. -/
public def ofNatN (n len : Nat) : UInt64Array := WordArray.ofNatLen n len

public theorem size_ofNatN (n len : Nat) : (ofNatN n len).size = len := by
  rw [ofNatN]; exact WordArray.size_ofNatLen (A := UInt64Array) n len

public theorem toNat_ofNatN (n len : Nat) : (ofNatN n len).toNat = n % 2 ^ (64 * len) := by
  rw [toNat_eq_valAt, size_ofNatN, ofNatN]
  exact WordArray.valAt_ofNatLen (A := UInt64Array) n len

/-- The limbs of `n`. -/
public def ofNat (n : Nat) : UInt64Array := ofNatN n (n.log2 / 64 + 1)

public theorem toNat_ofNat (n : Nat) : (ofNat n).toNat = n := by
  rw [ofNat, toNat_ofNatN, Nat.mod_eq_of_lt]
  rcases Nat.eq_zero_or_pos n with h | h
  · subst h; exact Nat.two_pow_pos _
  · exact Nat.lt_of_lt_of_le Nat.lt_log2_self (Nat.pow_le_pow_right (by decide) (by lia))

public theorem toNat_lt_pow (x : UInt64Array) : x.toNat < (2 ^ 64) ^ x.size := by
  rw [toNat_eq_valAt, ← Nat.pow_mul]; exact valAt_lt ..

/-! ## Trimming -/

/--
`x` without its zero limbs on top, but at least one limb: the operations of `MPN.Num` leave such
limbs, and the generic algorithms decide by sizes. It is `main`'s `WordArray.trimTo 1`, which pops
them, in place when `x` is not shared, which the fresh results of `MPN.Num` never are; it is `x`
itself when its top limb is nonzero.
-/
public def trimA (x : UInt64Array) : UInt64Array := WordArray.trimTo 1 x

@[simp] public theorem toNat_trimA (x : UInt64Array) : (trimA x).toNat = x.toNat := by
  rw [toNat_eq_valAt, toNat_eq_valAt, trimA]
  exact WordArray.valAt_trimTo 1 x

public theorem size_trimA_le (x : UInt64Array) : (trimA x).size ≤ max x.size 1 := by
  rw [trimA]; exact Nat.le_trans (WordArray.size_trimTo_le 1 x) (Nat.le_max_left ..)

/-- `trimA x` has at most one limb or a nonzero top limb. -/
public theorem trimA_trimmed (x : UInt64Array) :
    (trimA x).size ≤ 1 ∨ (trimA x)[(trimA x).size - 1]! ≠ 0 := by
  rw [trimA]
  rcases (WordArray.trimTo_spec 1 x).2.2.2 with h | h
  · exact .inl h
  · exact .inr fun e => h (by
      show (WordArray.trimTo 1 x)[(WordArray.trimTo 1 x).size - 1]!.toNat = 0; rw [e]; rfl)

/-- `trimA x` is one limb or has a nonzero top limb, for `x` of one limb at least. -/
public theorem trimA_top (x : UInt64Array) (h : 1 ≤ x.size) :
    (trimA x).size = 1 ∨ (1 < (trimA x).size ∧ (trimA x)[(trimA x).size - 1]! ≠ 0) := by
  have hge : 1 ≤ (trimA x).size := by
    have := WordArray.le_size_trimTo 1 x
    rw [trimA]
    exact Nat.le_trans (by show 1 ≤ min 1 x.size; lia) this
  rcases trimA_trimmed x with e | e
  · exact .inl (by lia)
  · rcases Nat.lt_or_ge 1 (trimA x).size with h' | h'
    · exact .inr ⟨h', e⟩
    · exact .inl (by lia)

/-! ## The instance -/

/-- The value `1`. -/
public def Num.one : UInt64Array := UInt64Array.replicate 1 1

public theorem Num.toNat_one : Num.one.toNat = 1 := by simp [Num.one, toNat_eq_valAt]

public theorem Num.size_one : Num.one.size = 1 := by simp [Num.one]

/-- `x b`, by `Num.mul`. -/
public def mul64 (x y : UInt64Array) : UInt64Array :=
  if fits (x.size + y.size + 1) then trimA (Num.mul x y) else ofNat (x.toNat * y.toNat)

/-- The size of the modulus of `mulMod64 n`: `n` rounded up to a multiple of `2ᵏ`, `k = fftK n`. -/
@[expose] public def modSize64 (n : Nat) : Nat :=
  (n + 2 ^ FFT.fftK n - 1) / 2 ^ FFT.fftK n * 2 ^ FFT.fftK n

public theorem le_modSize64 (n : Nat) : n ≤ modSize64 n := by
  rw [modSize64]
  have h₀ : 0 < 2 ^ FFT.fftK n := Nat.two_pow_pos _
  generalize 2 ^ FFT.fftK n = P at *
  have h₁ := Nat.div_add_mod (n + P - 1) P
  have h₂ := Nat.mod_lt (n + P - 1) h₀
  rw [Nat.mul_comm] at h₁
  lia

/--
`x y` modulo `2^(64 modSize64 n) - 1`, up to a multiple: by `Num.mulModB` when the product is
longer than the modulus, and otherwise by `Num.mul`, since it would not wrap.
-/
public def mulMod64 (n : Nat) (x y : UInt64Array) : UInt64Array :=
  if fits (x.size + y.size + 1) then
    if x.size + y.size ≤ modSize64 n then Num.mul x y
    else Num.mulModB x y (FFT.fftK n) ((n + 2 ^ FFT.fftK n - 1) / 2 ^ FFT.fftK n)
  else ofNat (x.toNat * y.toNat)

public theorem val_mulMod64 (n : Nat) (x y : UInt64Array) :
    (mulMod64 n x y).toNat % ((2 ^ 64) ^ modSize64 n - 1) =
      x.toNat * y.toNat % ((2 ^ 64) ^ modSize64 n - 1) := by
  rw [mulMod64]
  split
  · rename_i h
    split
    · rw [Num.toNat_mul _ _ (by have := lt_of_fits h; lia)]
    · rw [modSize64, ← Nat.pow_mul]
      exact Num.toNat_mulModB _ _ _ _ (by have := lt_of_fits h; lia)
  · rw [toNat_ofNat]

/-- `x²`, by `Num.sqr`. -/
public def sqr64 (x : UInt64Array) : UInt64Array :=
  if fits (2 * x.size + 1) then trimA (Num.sqr x) else ofNat (x.toNat * x.toNat)

/-- `x + y`, by `Num.add`. -/
public def add64 (x y : UInt64Array) : UInt64Array :=
  if fits (x.size + y.size + 1) then trimA (Num.add x y) else ofNat (x.toNat + y.toNat)

/-- `x - y`, by `Num.sub`. -/
public def sub64 (x y : UInt64Array) : UInt64Array :=
  if fits (x.size + y.size + 1) then trimA (Num.sub x y) else ofNat (x.toNat - y.toNat)

/-- Whether `x ≤ y`, by `Num.lt`. -/
public def le64 (x y : UInt64Array) : Bool :=
  if fits (x.size + y.size + 1) then !Num.lt y x else decide (x.toNat ≤ y.toNat)

/-- `x mod βᵏ`, by `Num.low`. -/
public def lo64 (k : Nat) (x : UInt64Array) : UInt64Array :=
  if fits (x.size + 1) then Num.low x k else ofNat (x.toNat % 2 ^ (64 * k))

/-- `x / βᵏ`, by `Num.shr`, in `x.size - k` limbs. -/
public def hi64 (k : Nat) (x : UInt64Array) : UInt64Array :=
  if fits (x.size + 1) then Num.shr x (64 * k) else ofNatN (x.toNat / 2 ^ (64 * k)) (x.size - k)

/-- `x βᵏ`, by `Num.shl`. -/
public def shl64 (k : Nat) (x : UInt64Array) : UInt64Array :=
  if fits (k + x.size + 2) then Num.shl x (64 * k) else ofNat (x.toNat * 2 ^ (64 * k))

private theorem toNat_toUSize' {n : Nat} (h : n < USize.size) : n.toUSize.toNat = n := by
  rw [Nat.toUSize_eq, USize.toNat_ofNat_of_lt' h]

private theorem join_ok (k : Nat) (x y : UInt64Array) (h : fits (k + x.size + y.size + 1) = true) :
    WordArray.JoinOK k.toUSize x 0 x.size.toUSize y 0 y.size.toUSize
      (UInt64Array.replicate (k + x.size) 0) := by
  have hU := lt_of_fits h
  have e₁ := toNat_toUSize' (show k < USize.size by lia)
  have e₂ := toNat_toUSize' (show x.size < USize.size by lia)
  have e₃ := toNat_toUSize' (show y.size < USize.size by lia)
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ?_, ?_, fun i => ?_⟩
  · show _ ≤ x.size; rw [USize.toNat_zero, e₂]; lia
  · rw [USize.toNat_zero, e₂]; lia
  · show _ ≤ y.size; rw [USize.toNat_zero, e₃]; lia
  · rw [USize.toNat_zero, e₃]; lia
  · rw [e₁, e₂]; lia
  · show (UInt64Array.replicate _ 0).size = _; rw [UInt64Array.size_replicate, e₁, e₂]
  · show ((UInt64Array.replicate (k + x.size) 0)[i]!).toNat = 0
    by_cases hi : i < k + x.size
    · rw [getElem!_pos _ i (by simpa using hi), UInt64Array.getElem_replicate]; rfl
    · rw [getElem!_neg _ i (by simpa using hi)]; rfl

/-- `x βᵏ + y mod βᵏ`, by `main`'s `WordArray.joinW` in one array. -/
public def join64 (k : Nat) (x y : UInt64Array) : UInt64Array :=
  if h : fits (k + x.size + y.size + 1) then
    WordArray.joinW UInt64Array k.toUSize x 0 x.size.toUSize y 0 y.size.toUSize
      (UInt64Array.replicate (k + x.size) 0) (join_ok k x y h)
  else ofNat (x.toNat * 2 ^ (64 * k) + y.toNat % 2 ^ (64 * k))

public theorem val_join64 (k : Nat) (x y : UInt64Array) :
    (join64 k x y).toNat = x.toNat * (2 ^ 64) ^ k + y.toNat % (2 ^ 64) ^ k := by
  rw [← Nat.pow_mul, join64]
  split
  · rename_i h
    have hU := lt_of_fits h
    have e₁ := toNat_toUSize' (show k < USize.size by lia)
    have e₂ := toNat_toUSize' (show x.size < USize.size by lia)
    have e₃ := toNat_toUSize' (show y.size < USize.size by lia)
    obtain ⟨j₁, j₂⟩ := WordArray.joinW_spec (A := UInt64Array) k.toUSize x 0 x.size.toUSize y 0
      y.size.toUSize _ (join_ok k x y h)
    simp only [e₁, e₂, e₃, USize.toNat_zero] at j₁ j₂
    rw [toNat_eq_valAt, toNat_eq_valAt, toNat_eq_valAt]
    rw [show (WordArray.joinW UInt64Array _ x 0 _ y 0 _ _ _).size = k + x.size from j₁]
    exact j₂
  · exact toNat_ofNat _

/-- `βᵏ`. -/
public def pow64 (k : Nat) : UInt64Array := shl64 k Num.one

public theorem val_shl64 (k : Nat) (x : UInt64Array) :
    (shl64 k x).toNat = x.toNat * (2 ^ 64) ^ k := by
  rw [← Nat.pow_mul, shl64]
  split
  · rename_i h; have := lt_of_fits h
    exact Num.toNat_shl _ _ (by lia)
  · exact toNat_ofNat _

/-- `(x / y, x mod y)` by the schoolbook division `Num.divModBase`. -/
public def divBase64 (x y : UInt64Array) : UInt64Array × UInt64Array :=
  if fits (x.size + y.size + 1) then
    let p := Num.divModBase x y
    (trimA p.1, trimA p.2)
  else (ofNat (x.toNat / y.toNat), ofNat (x.toNat % y.toNat))

public theorem val_divBase64 (x y : UInt64Array) (hy : y.toNat ≠ 0) :
    (divBase64 x y).1.toNat = x.toNat / y.toNat ∧ (divBase64 x y).2.toNat = x.toNat % y.toNat := by
  rw [divBase64]; split
  · rename_i h
    dsimp only
    rw [toNat_trimA, toNat_trimA]
    exact Num.toNat_divModBase _ _ (by lia) (lt_of_fits h)
  · exact ⟨toNat_ofNat _, toNat_ofNat _⟩

/-- The operations of `MPN.Num` as `NatOps` at base `2⁶⁴`, with the division `div`. -/
@[expose] public def ops64With (div : UInt64Array → UInt64Array → UInt64Array × UInt64Array)
    (hdiv : ∀ x y, y.toNat ≠ 0 →
      (div x y).1.toNat = x.toNat / y.toNat ∧ (div x y).2.toNat = x.toNat % y.toNat) :
    NatOps UInt64Array where
  B := 2 ^ 64
  one_lt_B := by decide
  val := UInt64Array.toNat
  size := UInt64Array.size
  val_lt := toNat_lt_pow
  mul := mul64
  val_mul x y := by
    rw [mul64]; split
    · rename_i h; rw [toNat_trimA]; exact Num.toNat_mul _ _ (by have := lt_of_fits h; lia)
    · exact toNat_ofNat _
  sqr := sqr64
  val_sqr x := by
    rw [sqr64]; split
    · rename_i h; rw [toNat_trimA]; exact Num.toNat_sqr _ (by have := lt_of_fits h; lia)
    · exact toNat_ofNat _
  add := add64
  val_add x y := by
    rw [add64]; split
    · rename_i h; rw [toNat_trimA]; exact Num.toNat_add _ _ (lt_of_fits h)
    · exact toNat_ofNat _
  sub := sub64
  val_sub x y hle := by
    rw [sub64]; split
    · rename_i h; have := lt_of_fits h; rw [toNat_trimA]
      exact Num.toNat_sub _ _ hle (by lia) (by lia)
    · exact toNat_ofNat _
  le := le64
  le_iff x y := by
    rw [le64]; split
    · rename_i h
      rw [Bool.not_eq_true', ← Bool.not_eq_true, Num.lt_iff _ _ (by have := lt_of_fits h; lia)]
      lia
    · simp
  lo := lo64
  val_lo k x := by
    rw [lo64, ← Nat.pow_mul]; split
    · rename_i h; exact Num.toNat_low _ _ (by have := lt_of_fits h; lia)
    · exact toNat_ofNat _
  hi := hi64
  val_hi k x := by
    rw [hi64, ← Nat.pow_mul]; split
    · rename_i h; exact Num.toNat_shr _ _ (by have := lt_of_fits h; lia)
    · rw [toNat_ofNatN, Nat.mod_eq_of_lt]
      have hx : x.toNat < 2 ^ (64 * x.size) := by rw [toNat_eq_valAt]; exact valAt_lt ..
      apply (Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _)).2
      rw [← Nat.pow_add]
      exact Nat.lt_of_lt_of_le hx (Nat.pow_le_pow_right (by decide) (by lia))
  size_hi k x := by
    rw [hi64]; split
    · rw [Num.size_shr]; lia
    · rw [size_ofNatN]
  shl := shl64
  val_shl := val_shl64
  join := join64
  val_join := val_join64
  pow := pow64
  val_pow k := by rw [pow64, val_shl64, Num.toNat_one, Nat.one_mul]
  one := Num.one
  val_one := Num.toNat_one
  mulModSize := modSize64
  le_mulModSize := le_modSize64
  mulMod := mulMod64
  val_mulMod := val_mulMod64
  divRem := div
  val_divRem := hdiv

/-- The instance with the schoolbook division, for the divide-and-conquer division over it. -/
@[expose] public def ops64B : NatOps UInt64Array := ops64With divBase64 val_divBase64

@[simp] public theorem ops64B_val (x : UInt64Array) : ops64B.val x = x.toNat := rfl

@[simp] public theorem ops64B_B : ops64B.B = 2 ^ 64 := rfl

end MPN.W64
