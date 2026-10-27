/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import MPN.Generic.Ops
public import MPN.Num

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

namespace MPN

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

/-- The `len` low limbs of `n`. -/
public def ofNatN (n len : Nat) : UInt64Array :=
  UInt64Array.ofFn (n := len) fun i => (n / 2 ^ (64 * i.1)).toUInt64

public theorem size_ofNatN (n len : Nat) : (ofNatN n len).size = len := by simp [ofNatN]

private theorem valAt_ofNatN (n len : Nat) : ∀ m lo, lo + m ≤ len →
    (ofNatN n len).valAt lo m = n / 2 ^ (64 * lo) % 2 ^ (64 * m) := by
  intro m
  induction m with
  | zero => intro lo _; simp [Nat.mod_one]
  | succ m ih =>
    intro lo h
    rw [valAt_succ, ih (lo + 1) (by lia), getElem!_eq_getElem _ _ (by rw [size_ofNatN]; lia)]
    simp only [ofNatN, getElem_ofFn, Nat.toUInt64_eq, UInt64.toNat_ofNat']
    rw [show 64 * (lo + 1) = 64 * lo + 64 by lia, Nat.pow_add, ← Nat.div_div_eq_div_mul,
      show 64 * (m + 1) = 64 + 64 * m by lia, Nat.pow_add, Nat.mod_mul]

public theorem toNat_ofNatN (n len : Nat) : (ofNatN n len).toNat = n % 2 ^ (64 * len) := by
  rw [toNat_eq_valAt, size_ofNatN, valAt_ofNatN n len len 0 (by lia)]
  simp

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
limbs, and the generic algorithms decide by sizes. It pops them, in place when `x` is not shared,
which the fresh results of `MPN.Num` never are; it is `x` itself when its top limb is nonzero.
-/
public def trimA (x : UInt64Array) : UInt64Array :=
  if h : 1 < x.size then
    if x[x.size - 1] = 0 then trimA x.pop else x
  else x
termination_by x.size
decreasing_by simp only [UInt64Array.size_pop]; lia

@[simp] public theorem toNat_trimA (x : UInt64Array) : (trimA x).toNat = x.toNat := by
  induction x using trimA.induct with
  | case1 x h₁ h₂ ih =>
    rw [trimA, dite_eq_left h₁, ite_eq_left h₂, ih]
    have hs : x.size = (x.size - 1) + 1 := by lia
    rw [toNat_eq_valAt, toNat_eq_valAt, UInt64Array.size_pop, hs, UInt64Array.valAt_add,
      UInt64Array.valAt_one, Nat.zero_add, ← hs, getElem!_eq_getElem _ _ (by lia), h₂,
      UInt64.toNat_zero, Nat.mul_zero, Nat.add_zero]
    exact UInt64Array.valAt_congr _ fun i _ hi => by
      rw [getElem!_eq_getElem _ _ (by simp only [UInt64Array.size_pop]; lia),
        getElem!_eq_getElem _ _ (by lia), UInt64Array.getElem_pop]
  | case2 x h₁ h₂ => rw [trimA, dite_eq_left h₁, ite_eq_right h₂]
  | case3 x h => rw [trimA, dite_eq_right h]

public theorem size_trimA_le (x : UInt64Array) : (trimA x).size ≤ max x.size 1 := by
  induction x using trimA.induct with
  | case1 x h₁ h₂ ih =>
    rw [trimA, dite_eq_left h₁, ite_eq_left h₂]
    simp only [UInt64Array.size_pop] at ih
    lia
  | case2 x h₁ h₂ => rw [trimA, dite_eq_left h₁, ite_eq_right h₂]; lia
  | case3 x h => rw [trimA, dite_eq_right h]; lia

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

end MPN
