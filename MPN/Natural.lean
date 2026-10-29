/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import MPN.Generic.Sqrt
import Std.Data.String.ToNat
import all Init.Data.Repr

/-!
# Natural numbers

`GNat A` is a natural number as a machine word below `2⁶⁴` and as trimmed limbs `A` above, so that
each natural number has exactly one representation: `toNat` and `ofNat` are inverse bijections
between `GNat A` and `Nat`, and equality, comparison and hashing work on the representation.

The arithmetic takes a fast path on words when both numbers are small, checking for overflow,
and otherwise works on limbs with the operations of the instance of `NatLimbs A`, which are
whole-number operations on trimmed arrays with their values. Every operation is proved correct
against `Nat`. `main32` and `main64` instantiate it on their arrays of 32-bit and 64-bit limbs as
`MPN.Nat`, and add the square root and the greatest common divisor by their own algorithms.

Lean's own `Nat` stores small values in the pointer itself; a type defined in Lean cannot, so
a small `GNat` is a heap object holding its word, which costs an allocation per result.
-/

namespace MPN

/--
Whole-number operations on trimmed arrays of limbs `A`, with their values: each takes trimmed
arrays and returns a trimmed array, the representation of each number being unique.
-/
public class NatLimbs (A : Type) where
  /-- The value of an array. -/
  val : A → Nat
  /-- Whether an array is trimmed: no zero limb on top. -/
  trimmed : A → Bool
  eq_of_val : ∀ a b, trimmed a = true → trimmed b = true → val a = val b → a = b
  /-- Equality of arrays. -/
  decEq : DecidableEq A
  /-- A hash of an array. -/
  hash : A → UInt64
  /-- The array of a natural number. -/
  ofNat : Nat → A
  trimmed_ofNat : ∀ n, trimmed (ofNat n) = true
  val_ofNat : ∀ n, val (ofNat n) = n
  /-- The array of a word. -/
  ofWord : UInt64 → A
  trimmed_ofWord : ∀ w, trimmed (ofWord w) = true
  val_ofWord : ∀ w, val (ofWord w) = w.toNat
  /-- The array of `lo + 2⁶⁴ hi`, for `hi ≠ 0`. -/
  wide : UInt64 → UInt64 → A
  wide_spec : ∀ lo hi, hi ≠ 0 →
    trimmed (wide lo hi) = true ∧ val (wide lo hi) = lo.toNat + 2 ^ 64 * hi.toNat
  /-- Whether a trimmed array is below `2⁶⁴`. -/
  fits : A → Bool
  fits_iff : ∀ a, trimmed a = true → (fits a = true ↔ val a < 2 ^ 64)
  /-- The word of an array below `2⁶⁴`. -/
  toWord : A → UInt64
  val_toWord : ∀ a, trimmed a = true → val a < 2 ^ 64 → (toWord a).toNat = val a
  add : A → A → A
  trimmed_add : ∀ a b, trimmed (add a b) = true
  val_add : ∀ a b, val (add a b) = val a + val b
  /-- `a - b`, for `b ≤ a`. -/
  sub : A → A → A
  trimmed_sub : ∀ a b, trimmed (sub a b) = true
  val_sub : ∀ a b, val b ≤ val a → val (sub a b) = val a - val b
  /-- Whether `a < b`. -/
  lt : A → A → Bool
  lt_iff : ∀ a b, lt a b = true ↔ val a < val b
  mul : A → A → A
  trimmed_mul : ∀ a b, trimmed (mul a b) = true
  val_mul : ∀ a b, val (mul a b) = val a * val b
  sqr : A → A
  trimmed_sqr : ∀ a, trimmed (sqr a) = true
  val_sqr : ∀ a, val (sqr a) = val a * val a
  /-- `a / b`, and `0` for `b = 0`. -/
  div : A → A → A
  trimmed_div : ∀ a b, trimmed (div a b) = true
  val_div : ∀ a b, val (div a b) = val a / val b
  /-- `a % b`, and `a` for `b = 0`. -/
  mod : A → A → A
  trimmed_mod : ∀ a b, trimmed (mod a b) = true
  val_mod : ∀ a b, val (mod a b) = val a % val b
  /-- `a / b` for a nonzero word `b`. -/
  divW : A → UInt64 → A
  trimmed_divW : ∀ a b, trimmed (divW a b) = true
  val_divW : ∀ a b, b ≠ 0 → val (divW a b) = val a / b.toNat
  /-- `a % b` for a nonzero word `b`. -/
  modW : A → UInt64 → UInt64
  val_modW : ∀ a b, b ≠ 0 → (modW a b).toNat = val a % b.toNat
  /-- `a 2ⁿ`. -/
  shl : A → Nat → A
  trimmed_shl : ∀ a n, trimmed (shl a n) = true
  val_shl : ∀ a n, val (shl a n) = val a * 2 ^ n
  /-- `⌊a / 2ⁿ⌋`. -/
  shr : A → Nat → A
  trimmed_shr : ∀ a n, trimmed (shr a n) = true
  val_shr : ∀ a n, val (shr a n) = val a / 2 ^ n
  land : A → A → A
  trimmed_land : ∀ a b, trimmed (land a b) = true
  val_land : ∀ a b, val (land a b) = val a &&& val b
  lor : A → A → A
  trimmed_lor : ∀ a b, trimmed (lor a b) = true
  val_lor : ∀ a b, val (lor a b) = val a ||| val b
  xor : A → A → A
  trimmed_xor : ∀ a b, trimmed (xor a b) = true
  val_xor : ∀ a b, val (xor a b) = val a ^^^ val b
  /-- `⌊log₂ a⌋`, from the top limb. -/
  log2 : A → Nat
  log2_eq : ∀ a, trimmed a = true → log2 a = (val a).log2
  /-- The decimal digits. -/
  toDecimal : A → String
  toDecimal_eq : ∀ a, trimmed a = true → toDecimal a = _root_.Nat.repr (val a)
  /-- The value of a string of decimal digits, for a string that `String.isNat` accepts. -/
  ofDecimal : String → A
  ofDecimal_spec : ∀ s, s.isNat = true →
    trimmed (ofDecimal s) = true ∧ s.toNat? = some (val (ofDecimal s))

/-- A natural number: a machine word below `2⁶⁴`, trimmed limbs above. -/
public inductive GNat (A : Type) [C : NatLimbs A] where
  /-- A number below `2⁶⁴`. -/
  | small (n : UInt64)
  /-- A number of at least `2⁶⁴`, as trimmed limbs. -/
  | large (a : A) (h : C.trimmed a = true ∧ 2 ^ 64 ≤ C.val a)

namespace GNat

variable {A : Type} [C : NatLimbs A]

/-- The natural number that a `GNat` denotes. -/
@[expose] public def toNat : GNat A → Nat
  | small n => n.toNat
  | large a _ => C.val a

/-- The `GNat` of a natural number. -/
@[expose, specialize] public def ofNat (n : Nat) : GNat A :=
  if h : n < 2 ^ 64 then
    small n.toUInt64
  else
    large (C.ofNat n) ⟨C.trimmed_ofNat n, by rw [C.val_ofNat]; lia⟩

@[simp] public theorem toNat_ofNat (n : Nat) : (ofNat n : GNat A).toNat = n := by
  unfold ofNat
  split
  · rename_i h
    simp [toNat, Nat.mod_eq_of_lt h]
  · exact C.val_ofNat n

public theorem toNat_small (n : UInt64) : (small n : GNat A).toNat = n.toNat := rfl

/-- `toNat` is injective, since each number has one representation. -/
public theorem toNat_inj {x y : GNat A} : x.toNat = y.toNat ↔ x = y := by
  refine ⟨fun h => ?_, fun h => h ▸ rfl⟩
  cases x with
  | small m =>
    cases y with
    | small n => exact congrArg small (UInt64.toNat_inj.1 h)
    | large b hb =>
      have := m.toNat_lt
      simp only [toNat] at h
      lia
  | large a ha =>
    cases y with
    | small n =>
      have := n.toNat_lt
      simp only [toNat] at h
      lia
    | large b hb =>
      simp only [toNat] at h
      have : a = b := C.eq_of_val a b ha.1 hb.1 h
      subst this
      rfl

@[simp] public theorem ofNat_toNat (x : GNat A) : ofNat x.toNat = x :=
  toNat_inj.1 (toNat_ofNat _)

/-- The limbs of a `GNat`, trimmed. -/
@[expose, specialize] public def limbs : GNat A → A
  | small n => C.ofWord n
  | large a _ => a

public theorem val_limbs (x : GNat A) : C.val x.limbs = x.toNat := by
  cases x with
  | small n => exact C.val_ofWord n
  | large a _ => rfl

public theorem trimmed_limbs (x : GNat A) : C.trimmed x.limbs = true := by
  cases x with
  | small n => exact C.trimmed_ofWord n
  | large a h => exact h.1

/-- The `GNat` of trimmed limbs. -/
@[expose, specialize] public def ofLimbs (a : A) (h : C.trimmed a = true) : GNat A :=
  if hs : C.fits a = true then
    small (C.toWord a)
  else
    large a ⟨h, Nat.le_of_not_lt fun h' => hs ((C.fits_iff a h).2 h')⟩

@[simp] public theorem toNat_ofLimbs (a : A) (h : C.trimmed a = true) :
    (ofLimbs a h).toNat = C.val a := by
  unfold ofLimbs
  split
  · rename_i hs
    exact C.val_toWord a h ((C.fits_iff a h).1 hs)
  · rfl

/-! ## Results of two words

A sum or product of two words can overflow 64 bits. `mulWide` computes the whole product of two
words from the four products of their halves, and `wideOf` makes the `GNat` of a two-word
number directly, as one array (`NatLimbs.wide`), where the general arithmetic would make an array
for each word first.
-/

/-- The `GNat` `lo + 2⁶⁴ hi`. -/
@[expose, specialize] public def wideOf (lo hi : UInt64) : GNat A :=
  if h : hi = 0 then small lo
  else large (C.wide lo hi) ⟨(C.wide_spec lo hi h).1, by
    rw [(C.wide_spec lo hi h).2]
    have : hi.toNat ≠ 0 := fun e => h (UInt64.toNat_inj.1 (by simpa using e))
    have := Nat.mul_le_mul_left (2 ^ 64) (Nat.one_le_iff_ne_zero.2 this)
    lia⟩

private theorem toNat_wideOf (lo hi : UInt64) :
    (wideOf lo hi : GNat A).toNat = lo.toNat + 2 ^ 64 * hi.toNat := by
  unfold wideOf
  split
  · rename_i h
    subst h
    simp [toNat]
  · rename_i h
    exact (C.wide_spec lo hi h).2

end GNat

/-- The product of two words as its low word and its high word, from the products of halves. -/
@[inline, expose] public def mulWide (a b : UInt64) : UInt64 × UInt64 :=
  let a₀ := a &&& 0xFFFFFFFF
  let a₁ := a >>> 32
  let b₀ := b &&& 0xFFFFFFFF
  let b₁ := b >>> 32
  let p₀₀ := a₀ * b₀
  let p₀₁ := a₀ * b₁
  let p₁₀ := a₁ * b₀
  let mid := (p₀₀ >>> 32) + (p₀₁ &&& 0xFFFFFFFF) + (p₁₀ &&& 0xFFFFFFFF)
  ((mid <<< 32) + (p₀₀ &&& 0xFFFFFFFF), a₁ * b₁ + (p₀₁ >>> 32) + (p₁₀ >>> 32) + (mid >>> 32))

public theorem mulWide_spec (a b : UInt64) :
    (mulWide a b).1.toNat + 2 ^ 64 * (mulWide a b).2.toNat = a.toNat * b.toNat := by
  have ha := a.toNat_lt
  have hb := b.toNat_lt
  have hm : ∀ x : Nat, x &&& 4294967295 = x % 2 ^ 32 := fun x =>
    Nat.and_two_pow_sub_one_eq_mod x 32
  simp only [mulWide, UInt64.toNat_add, UInt64.toNat_mul, UInt64.toNat_and,
    UInt64.toNat_shiftRight, UInt64.toNat_shiftLeft, UInt64.reduceToNat, Nat.reduceMod,
    Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq, hm]
  -- The halves and their products.
  have e₁ : a.toNat = 2 ^ 32 * (a.toNat / 2 ^ 32) + a.toNat % 2 ^ 32 := (Nat.div_add_mod _ _).symm
  have e₂ : b.toNat = 2 ^ 32 * (b.toNat / 2 ^ 32) + b.toNat % 2 ^ 32 := (Nat.div_add_mod _ _).symm
  have hA₀ : a.toNat % 2 ^ 32 < 2 ^ 32 := Nat.mod_lt _ (by decide)
  have hB₀ : b.toNat % 2 ^ 32 < 2 ^ 32 := Nat.mod_lt _ (by decide)
  have hA₁ : a.toNat / 2 ^ 32 < 2 ^ 32 := by lia
  have hB₁ : b.toNat / 2 ^ 32 < 2 ^ 32 := by lia
  generalize a.toNat % 2 ^ 32 = A₀ at *
  generalize b.toNat % 2 ^ 32 = B₀ at *
  generalize a.toNat / 2 ^ 32 = A₁ at *
  generalize b.toNat / 2 ^ 32 = B₁ at *
  have hprod : a.toNat * b.toNat =
      2 ^ 64 * (A₁ * B₁) + 2 ^ 32 * (A₀ * B₁) + 2 ^ 32 * (A₁ * B₀) + A₀ * B₀ := by
    rw [e₁, e₂]
    simp only [Nat.mul_add, Nat.add_mul]
    grind
  have b₀₀ : A₀ * B₀ ≤ 4294967295 * 4294967295 := Nat.mul_le_mul (by lia) (by lia)
  have b₀₁ : A₀ * B₁ ≤ 4294967295 * 4294967295 := Nat.mul_le_mul (by lia) (by lia)
  have b₁₀ : A₁ * B₀ ≤ 4294967295 * 4294967295 := Nat.mul_le_mul (by lia) (by lia)
  have b₁₁ : A₁ * B₁ ≤ 4294967295 * 4294967295 := Nat.mul_le_mul (by lia) (by lia)
  rw [hprod]
  generalize A₀ * B₀ = P₀₀ at *
  generalize A₀ * B₁ = P₀₁ at *
  generalize A₁ * B₀ = P₁₀ at *
  generalize A₁ * B₁ = P₁₁ at *
  rw [Nat.mod_eq_of_lt (show P₀₀ < 2 ^ 64 by lia), Nat.mod_eq_of_lt (show P₀₁ < 2 ^ 64 by lia),
    Nat.mod_eq_of_lt (show P₁₀ < 2 ^ 64 by lia), Nat.mod_eq_of_lt (show P₁₁ < 2 ^ 64 by lia)]
  lia

namespace GNat

variable {A : Type} [C : NatLimbs A]

/-! ## Arithmetic -/

/-- Addition: on words unless the sum overflows. -/
@[expose, specialize] public def add : GNat A → GNat A → GNat A
  | small a, small b =>
    let s := a + b
    if s < a then wideOf s 1 else small s
  | x, y => ofLimbs (C.add x.limbs y.limbs) (C.trimmed_add _ _)

/-- Truncated subtraction, like `Nat`'s: `x - y = 0` when `x < y`. -/
@[expose, specialize] public def sub : GNat A → GNat A → GNat A
  | small a, small b => if b ≤ a then small (a - b) else small 0
  | x, y =>
    if C.lt x.limbs y.limbs then small 0
    else ofLimbs (C.sub x.limbs y.limbs) (C.trimmed_sub _ _)

/-- Multiplication: on words when both factors are below `2³²`. -/
@[expose, specialize] public def mul : GNat A → GNat A → GNat A
  | small a, small b =>
    if a < 4294967296 ∧ b < 4294967296 then small (a * b)
    else wideOf (mulWide a b).1 (mulWide a b).2
  | x, y => ofLimbs (C.mul x.limbs y.limbs) (C.trimmed_mul _ _)

/-- Division, like `Nat`'s: `x / 0 = 0`. -/
@[expose, specialize] public def div : GNat A → GNat A → GNat A
  | small a, small b => small (a / b)
  | small _, large _ _ => small 0
  | large a _, small b =>
    if b = 0 then small 0 else ofLimbs (C.divW a b) (C.trimmed_divW _ _)
  | x, y => ofLimbs (C.div x.limbs y.limbs) (C.trimmed_div _ _)

/-- The remainder, like `Nat`'s: `x % 0 = x`. -/
@[expose, specialize] public def mod : GNat A → GNat A → GNat A
  | small a, small b => small (a % b)
  | small a, large _ _ => small a
  | large a ha, small b =>
    if b = 0 then large a ha else small (C.modW a b)
  | x, y => ofLimbs (C.mod x.limbs y.limbs) (C.trimmed_mod _ _)

private theorem small_lt_large (a : UInt64) (b : A)
    (hb : C.trimmed b = true ∧ 2 ^ 64 ≤ C.val b) : (small a : GNat A).toNat < (large b hb).toNat := by
  have := a.toNat_lt
  simp only [toNat]
  lia

@[simp] public theorem toNat_add (x y : GNat A) : (add x y).toNat = x.toNat + y.toNat := by
  have hgen : ∀ x y : GNat A, (ofLimbs (C.add x.limbs y.limbs) (C.trimmed_add _ _)).toNat =
      x.toNat + y.toNat := fun x y => by
    rw [toNat_ofLimbs, C.val_add, val_limbs, val_limbs]
  cases x with
  | small a =>
    cases y with
    | small b =>
      have ha := a.toNat_lt
      have hb := b.toNat_lt
      rw [add]
      split
      · rename_i h
        rw [UInt64.lt_iff_toNat_lt, UInt64.toNat_add] at h
        rw [toNat_wideOf, UInt64.toNat_add]
        simp only [toNat, UInt64.toNat_one]
        lia
      · rename_i h
        rw [UInt64.lt_iff_toNat_lt, UInt64.toNat_add] at h
        simp only [toNat, UInt64.toNat_add]
        lia
    | large b hb => exact hgen _ _
  | large a ha => exact hgen _ _

@[simp] public theorem toNat_sub (x y : GNat A) : (sub x y).toNat = x.toNat - y.toNat := by
  have hgen : ∀ x y : GNat A, (if C.lt x.limbs y.limbs then small 0
      else ofLimbs (C.sub x.limbs y.limbs) (C.trimmed_sub _ _)).toNat =
      x.toNat - y.toNat := fun x y => by
    by_cases h : C.lt x.limbs y.limbs = true
    · rw [ite_eq_left h]
      rw [C.lt_iff, val_limbs, val_limbs] at h
      rw [toNat_small, UInt64.toNat_zero]
      lia
    · rw [ite_eq_right h]
      have h' : y.toNat ≤ x.toNat := by
        rw [C.lt_iff, val_limbs, val_limbs] at h
        lia
      rw [toNat_ofLimbs, C.val_sub _ _ (by rw [val_limbs, val_limbs]; exact h'), val_limbs,
        val_limbs]
  cases x with
  | small a =>
    cases y with
    | small b =>
      simp only [sub]
      split
      · rename_i h
        simp only [toNat, UInt64.toNat_sub_of_le _ _ h]
      · rename_i h
        rw [UInt64.le_iff_toNat_le] at h
        simp only [toNat, UInt64.toNat_zero]
        lia
    | large b hb => exact hgen _ _
  | large a ha => exact hgen _ _

@[simp] public theorem toNat_mul (x y : GNat A) : (mul x y).toNat = x.toNat * y.toNat := by
  have hgen : ∀ x y : GNat A, (ofLimbs (C.mul x.limbs y.limbs) (C.trimmed_mul _ _)).toNat =
      x.toNat * y.toNat := fun x y => by
    rw [toNat_ofLimbs, C.val_mul, val_limbs, val_limbs]
  cases x with
  | small a =>
    cases y with
    | small b =>
      simp only [mul]
      split
      · rename_i h
        obtain ⟨h₁, h₂⟩ := h
        rw [UInt64.lt_iff_toNat_lt] at h₁ h₂
        simp only [UInt64.reduceToNat] at h₁ h₂
        have : a.toNat * b.toNat < 2 ^ 64 :=
          Nat.lt_of_lt_of_le (Nat.mul_lt_mul'' h₁ h₂) (by decide)
        simp only [toNat, UInt64.toNat_mul, Nat.mod_eq_of_lt this]
      · rw [toNat_wideOf, mulWide_spec]
        rfl
    | large b hb => exact hgen _ _
  | large a ha => exact hgen _ _

@[simp] public theorem toNat_div (x y : GNat A) : (div x y).toNat = x.toNat / y.toNat := by
  have hgen : ∀ x y : GNat A, (ofLimbs (C.div x.limbs y.limbs) (C.trimmed_div _ _)).toNat =
      x.toNat / y.toNat := fun x y => by
    rw [toNat_ofLimbs, C.val_div, val_limbs, val_limbs]
  cases x with
  | small a =>
    cases y with
    | small b => simp [div, toNat, UInt64.toNat_div]
    | large b hb =>
      have := small_lt_large a b hb
      simp only [div]
      rw [Nat.div_eq_of_lt this]
      rfl
  | large a ha =>
    cases y with
    | small b =>
      simp only [div]
      split
      · rename_i h
        subst h
        simp [toNat]
      · rename_i h
        rw [toNat_ofLimbs, C.val_divW _ _ h]
        rfl
    | large b hb => exact hgen _ _

@[simp] public theorem toNat_mod (x y : GNat A) : (mod x y).toNat = x.toNat % y.toNat := by
  have hgen : ∀ x y : GNat A, (ofLimbs (C.mod x.limbs y.limbs) (C.trimmed_mod _ _)).toNat =
      x.toNat % y.toNat := fun x y => by
    rw [toNat_ofLimbs, C.val_mod, val_limbs, val_limbs]
  cases x with
  | small a =>
    cases y with
    | small b => simp [mod, toNat, UInt64.toNat_mod]
    | large b hb =>
      have := small_lt_large a b hb
      simp only [mod]
      rw [Nat.mod_eq_of_lt this]
  | large a ha =>
    cases y with
    | small b =>
      simp only [mod]
      split
      · rename_i h
        subst h
        simp [toNat]
      · rename_i h
        rw [toNat_small, C.val_modW _ _ h]
        rfl
    | large b hb => exact hgen _ _

/-! ## Comparison -/

/-- Whether `x < y`. -/
@[expose, specialize] public def blt : GNat A → GNat A → Bool
  | small a, small b => a < b
  | small _, large _ _ => true
  | large _ _, small _ => false
  | large a _, large b _ => C.lt a b

public theorem blt_iff (x y : GNat A) : blt x y = true ↔ x.toNat < y.toNat := by
  cases x with
  | small a =>
    cases y with
    | small b => simp [blt, toNat, UInt64.lt_iff_toNat_lt]
    | large b hb => simp only [blt, true_iff]; exact small_lt_large a b hb
  | large a ha =>
    cases y with
    | small b =>
      have := small_lt_large b a ha
      simp only [blt, Bool.false_eq_true, false_iff, Nat.not_lt]
      lia
    | large b hb => simp only [blt, C.lt_iff]; rfl

/-- Decides equality on the representation, which is unique. -/
@[expose, specialize] public def decEq : (x y : GNat A) → Decidable (x = y)
  | small a, small b =>
    if h : a = b then isTrue (h ▸ rfl) else isFalse fun h' => h (by cases h'; rfl)
  | small a, large b hb => isFalse fun h' => by cases h'
  | large a ha, small b => isFalse fun h' => by cases h'
  | large a ha, large b hb =>
    have := C.decEq
    if h : a = b then isTrue (by subst h; rfl) else isFalse fun h' => h (by cases h'; rfl)

/-! ## Shifts, bits and `log2` -/

/-- `x <<< n = x * 2ⁿ`: on words when it fits. -/
@[expose, specialize] public def shiftLeft (x : GNat A) (n : Nat) : GNat A :=
  match x with
  | small a =>
    if n = 0 then small a
    else if n < 64 ∧ a >>> (64 - n).toUInt64 = 0 then small (a <<< n.toUInt64)
    else ofLimbs (C.shl (C.ofWord a) n) (C.trimmed_shl _ _)
  | large a _ => ofLimbs (C.shl a n) (C.trimmed_shl _ _)

/-- `x >>> n = x / 2ⁿ`. -/
@[expose, specialize] public def shiftRight (x : GNat A) (n : Nat) : GNat A :=
  match x with
  | small a => if n < 64 then small (a >>> n.toUInt64) else small 0
  | large a _ => ofLimbs (C.shr a n) (C.trimmed_shr _ _)

@[simp] public theorem toNat_shiftLeft (x : GNat A) (n : Nat) :
    (shiftLeft x n).toNat = x.toNat * 2 ^ n := by
  cases x with
  | small a =>
    have ha := a.toNat_lt
    simp only [shiftLeft]
    split
    · rename_i h; subst h; simp [toNat]
    · rename_i h0
      split
      · rename_i h
        obtain ⟨h₁, h₂⟩ := h
        have h₂ := congrArg UInt64.toNat h₂
        rw [UInt64.toNat_shiftRight, UInt64.toNat_zero, Nat.shiftRight_eq_div_pow] at h₂
        have hn : (64 - n).toUInt64.toNat % 64 = 64 - n := by
          simp only [Nat.toUInt64, UInt64.toNat_ofNat']
          rw [Nat.mod_eq_of_lt (by lia), Nat.mod_eq_of_lt (by lia)]
        have hn' : n.toUInt64.toNat % 64 = n := by
          simp only [Nat.toUInt64, UInt64.toNat_ofNat']
          rw [Nat.mod_eq_of_lt (by lia), Nat.mod_eq_of_lt (by lia)]
        rw [hn] at h₂
        have hlt : a.toNat < 2 ^ (64 - n) := by
          rcases Nat.eq_zero_or_pos (a.toNat / 2 ^ (64 - n)) with h | h
          · exact (Nat.div_eq_zero_iff_lt (Nat.two_pow_pos _)).1 h
          · lia
        have : a.toNat * 2 ^ n < 2 ^ 64 := by
          have := Nat.mul_lt_mul_of_pos_right hlt (Nat.two_pow_pos n)
          rwa [← Nat.pow_add, show 64 - n + n = 64 by lia] at this
        simp only [toNat, UInt64.toNat_shiftLeft, hn', Nat.shiftLeft_eq]
        exact Nat.mod_eq_of_lt this
      · rw [toNat_ofLimbs, C.val_shl, C.val_ofWord]
        rfl
  | large a ha =>
    simp only [shiftLeft]
    rw [toNat_ofLimbs, C.val_shl]
    rfl

@[simp] public theorem toNat_shiftRight (x : GNat A) (n : Nat) :
    (shiftRight x n).toNat = x.toNat / 2 ^ n := by
  cases x with
  | small a =>
    have ha := a.toNat_lt
    simp only [shiftRight]
    split
    · rename_i h
      have hn' : n.toUInt64.toNat % 64 = n := by
        simp only [Nat.toUInt64, UInt64.toNat_ofNat']
        rw [Nat.mod_eq_of_lt (by lia), Nat.mod_eq_of_lt (by lia)]
      simp only [toNat, UInt64.toNat_shiftRight, hn', Nat.shiftRight_eq_div_pow]
    · rename_i h
      have : 2 ^ 64 ≤ 2 ^ n := Nat.pow_le_pow_right (by decide) (by lia)
      simp only [toNat, UInt64.toNat_zero]
      exact (Nat.div_eq_of_lt (by lia)).symm
  | large a ha =>
    simp only [shiftRight]
    rw [toNat_ofLimbs, C.val_shr]
    rfl

/-- `x &&& y`: on words when both are small. -/
@[expose, specialize] public def land : GNat A → GNat A → GNat A
  | small a, small b => small (a &&& b)
  | x, y => ofLimbs (C.land x.limbs y.limbs) (C.trimmed_land _ _)

/-- `x ||| y`: on words when both are small. -/
@[expose, specialize] public def lor : GNat A → GNat A → GNat A
  | small a, small b => small (a ||| b)
  | x, y => ofLimbs (C.lor x.limbs y.limbs) (C.trimmed_lor _ _)

/-- `x ^^^ y`: on words when both are small. -/
@[expose, specialize] public def xor : GNat A → GNat A → GNat A
  | small a, small b => small (a ^^^ b)
  | x, y => ofLimbs (C.xor x.limbs y.limbs) (C.trimmed_xor _ _)

@[simp] public theorem toNat_land (x y : GNat A) : (land x y).toNat = x.toNat &&& y.toNat := by
  have hgen : ∀ x y : GNat A, (ofLimbs (C.land x.limbs y.limbs) (C.trimmed_land _ _)).toNat =
      x.toNat &&& y.toNat := fun x y => by
    rw [toNat_ofLimbs, C.val_land, val_limbs, val_limbs]
  cases x with
  | small a => cases y with
    | small b => simp [land, toNat, UInt64.toNat_and]
    | large b hb => exact hgen _ _
  | large a ha => exact hgen _ _

@[simp] public theorem toNat_lor (x y : GNat A) : (lor x y).toNat = x.toNat ||| y.toNat := by
  have hgen : ∀ x y : GNat A, (ofLimbs (C.lor x.limbs y.limbs) (C.trimmed_lor _ _)).toNat =
      x.toNat ||| y.toNat := fun x y => by
    rw [toNat_ofLimbs, C.val_lor, val_limbs, val_limbs]
  cases x with
  | small a => cases y with
    | small b => simp [lor, toNat, UInt64.toNat_or]
    | large b hb => exact hgen _ _
  | large a ha => exact hgen _ _

@[simp] public theorem toNat_xor (x y : GNat A) : (xor x y).toNat = x.toNat ^^^ y.toNat := by
  have hgen : ∀ x y : GNat A, (ofLimbs (C.xor x.limbs y.limbs) (C.trimmed_xor _ _)).toNat =
      x.toNat ^^^ y.toNat := fun x y => by
    rw [toNat_ofLimbs, C.val_xor, val_limbs, val_limbs]
  cases x with
  | small a => cases y with
    | small b => simp [xor, toNat, UInt64.toNat_xor]
    | large b hb => exact hgen _ _
  | large a ha => exact hgen _ _

/-- `⌊log₂ x⌋`, and `0` for `0`, like `Nat.log2`. -/
@[expose, specialize] public def log2 : GNat A → Nat
  | small a => a.toNat.log2
  | large a _ => C.log2 a

@[simp] public theorem log2_eq (x : GNat A) : x.log2 = x.toNat.log2 := by
  cases x with
  | small a => rfl
  | large a ha => exact C.log2_eq a ha.1

/-! ## Powers and square roots -/

/-- `x * x`: on words below `2³²`, with the instance's squaring above. -/
@[expose, specialize] public def sqr : GNat A → GNat A
  | small a =>
    if a < 4294967296 then small (a * a)
    else wideOf (mulWide a a).1 (mulWide a a).2
  | large a _ => ofLimbs (C.sqr a) (C.trimmed_sqr _)

@[simp] public theorem toNat_sqr (x : GNat A) : (sqr x).toNat = x.toNat * x.toNat := by
  cases x with
  | small a =>
    simp only [sqr]
    split
    · rename_i h
      rw [UInt64.lt_iff_toNat_lt] at h
      simp only [UInt64.reduceToNat] at h
      have : a.toNat * a.toNat < 2 ^ 64 := Nat.lt_of_lt_of_le (Nat.mul_lt_mul'' h h) (by decide)
      simp only [toNat, UInt64.toNat_mul, Nat.mod_eq_of_lt this]
    · rw [toNat_wideOf, mulWide_spec]
      rfl
  | large a ha =>
    simp only [sqr]
    rw [toNat_ofLimbs, C.val_sqr]
    rfl

/-- `xⁿ`, by repeated squaring. -/
@[expose, specialize] public def pow (x : GNat A) (n : Nat) : GNat A :=
  if n = 0 then small 1
  else if n % 2 = 0 then pow (sqr x) (n / 2)
  else mul x (pow (sqr x) (n / 2))
termination_by n
decreasing_by all_goals lia

@[simp] public theorem toNat_pow (x : GNat A) (n : Nat) : (pow x n).toNat = x.toNat ^ n := by
  induction n using Nat.strongRecOn generalizing x with
  | ind n ih =>
    rw [pow]
    split
    · rename_i h; subst h; rfl
    · rename_i h0
      have hn := Nat.div_add_mod n 2
      split
      · rename_i h
        rw [ih _ (by lia), toNat_sqr, ← Nat.pow_two, ← Nat.pow_mul]
        congr 1
        lia
      · rename_i h
        rw [toNat_mul, ih _ (by lia), toNat_sqr, ← Nat.pow_two, ← Nat.pow_mul, ← Nat.pow_succ']
        congr 1
        lia

/--
Steps down from `x ≥ ⌊√n⌋` to `⌊√n⌋`, while `x² > n`, with `sq = x²`: `(x - 1)² = x² - 2 x + 1`
needs no product. The guard also checks what the termination needs, which always holds.
-/
@[expose, specialize] public def sqrtFix (n x sq : GNat A) : GNat A :=
  if _h : blt n sq = true ∧ blt (small 0) x = true then
    sqrtFix n (sub x (small 1)) (sub (add sq (small 1)) (shiftLeft x 1))
  else x
termination_by x.toNat
decreasing_by
  rw [blt_iff, blt_iff, toNat_small] at _h
  rw [toNat_sub, toNat_small]
  simp only [UInt64.toNat_zero, UInt64.toNat_one] at *
  lia

private theorem toNat_sqrtFix (n x sq : GNat A) (hsq : sq.toNat = x.toNat * x.toNat)
    (hx : n.toNat < (x.toNat + 1) * (x.toNat + 1)) :
    (sqrtFix n x sq).toNat = _root_.Nat.sqrt n.toNat := by
  induction x, sq using sqrtFix.induct (C := C) n with
  | case1 x sq h ih =>
    rw [sqrtFix, dite_eq_left h]
    rw [blt_iff, blt_iff, toNat_small, UInt64.toNat_zero] at h
    obtain ⟨h₁, h₂⟩ := h
    apply ih
    · rw [toNat_sub, toNat_add, toNat_sub, toNat_shiftLeft, toNat_small, UInt64.toNat_one, hsq,
        Nat.pow_one]
      -- `(x - 1)² = x² + 1 - 2 x` for `x ≥ 1`.
      generalize x.toNat = X at h₂ ⊢
      obtain ⟨y, rfl⟩ : ∃ y, X = y + 1 := ⟨X - 1, by lia⟩
      simp only [Nat.add_sub_cancel, Nat.add_mul, Nat.mul_add, Nat.mul_one, Nat.one_mul]
      lia
    · rw [toNat_sub, toNat_small, UInt64.toNat_one, Nat.sub_add_cancel (by lia)]
      rw [hsq] at h₁
      exact h₁
  | case2 x sq h =>
    rw [sqrtFix, dite_eq_right h]
    rw [blt_iff, blt_iff, toNat_small, UInt64.toNat_zero] at h
    -- The loop stopped: `x² ≤ n`, or `x = 0` and then `n < 1`.
    refine eq_sqrt ?_ hx
    rw [hsq] at h
    rcases Nat.eq_zero_or_pos x.toNat with h0 | h0
    · rw [h0]; lia
    · lia

/--
`⌊√n⌋`: from `Nat.sqrt` on words, and above by Newton's iteration at growing precision: the root
`s` of the top half `n / 4ᵏ`, for `k` about a quarter of the bits of `n`, gives the start
`(s + 1) 2ᵏ` above `√n` and within `2ᵏ` of it. One Newton step from there is at least `⌊√n⌋`, by
AM-GM, and at most two above it; `sqrtFix` steps down to `⌊√n⌋` with one square, where checking
the step with a second division would cost more.
-/
@[expose, specialize] public def sqrtNewton (n : GNat A) : GNat A :=
  match hn : n with
  | small a => small (_root_.Nat.sqrt a.toNat).toUInt64
  | large _ ha =>
    let k := log2 n / 4 + 1
    let x₀ := shiftLeft (add (sqrtNewton (shiftRight n (2 * k))) (small 1)) k
    let x₁ := shiftRight (add x₀ (div n x₀)) 1
    sqrtFix n x₁ (sqr x₁)
termination_by n.toNat
decreasing_by
  rw [toNat_shiftRight]
  have hpos : 0 < n.toNat := by rw [hn]; simp only [toNat]; lia
  rw [← hn]
  apply Nat.div_lt_self hpos
  apply Nat.one_lt_two_pow
  lia

@[simp] public theorem toNat_sqrtNewton (n : GNat A) :
    (sqrtNewton n).toNat = _root_.Nat.sqrt n.toNat := by
  induction n using sqrtNewton.induct (C := C) with
  | case1 a =>
    rw [sqrtNewton]
    have ha := a.toNat_lt
    have hs : _root_.Nat.sqrt a.toNat < 2 ^ 64 := by
      have := Nat.sqrt_le a.toNat
      have := Nat.le_mul_self (_root_.Nat.sqrt a.toNat)
      lia
    simp only [toNat, Nat.toUInt64, UInt64.toNat_ofNat', Nat.mod_eq_of_lt hs]
  | case2 a ha k ih =>
    rw [sqrtNewton]
    have hx₀ :
        0 < (shiftLeft (add (sqrtNewton (shiftRight (large a ha) (2 * k))) (small 1)) k).toNat := by
      rw [toNat_shiftLeft, toNat_add, toNat_small, UInt64.toNat_one]
      exact Nat.mul_pos (by lia) (Nat.two_pow_pos _)
    -- One Newton step stays at or above the root.
    have hge := le_newton hx₀ (Nat.sqrt_le (large a ha).toNat)
    apply toNat_sqrtFix _ _ _ (toNat_sqr _)
    rw [toNat_shiftRight, toNat_add, toNat_div, Nat.pow_one]
    exact Nat.lt_of_lt_of_le (Nat.lt_succ_sqrt _) (Nat.mul_self_le_mul_self (Nat.succ_le_succ hge))

/-! ## Decimal strings -/

/--
The decimal digits, like `Nat.repr`. A word that fits in a `USize` goes to the runtime's
`USize.repr` directly, without a `Nat` above `2⁶³`, which would be a GMP number.
-/
@[expose, specialize] public def repr : GNat A → String
  | small n => if n.toUSize.toUInt64 = n then n.toUSize.repr else _root_.Nat.repr n.toNat
  | large a _ => C.toDecimal a

private theorem usize_repr (n : USize) : n.repr = _root_.Nat.repr n.toNat := by
  unfold USize.repr
  rfl

public theorem repr_eq (x : GNat A) : x.repr = _root_.Nat.repr x.toNat := by
  cases x with
  | small n =>
    show (if n.toUSize.toUInt64 = n then n.toUSize.repr else _root_.Nat.repr n.toNat) =
      _root_.Nat.repr n.toNat
    by_cases h : n.toUSize.toUInt64 = n
    · have := congrArg UInt64.toNat h
      rw [USize.toNat_toUInt64] at this
      rw [ite_eq_left h, usize_repr, this]
    · rw [ite_eq_right h]
  | large a h => exact C.toDecimal_eq a h.1

/-- The number that a string of decimal digits denotes, like `String.toNat?`. -/
@[expose, specialize] public def ofString? (s : String) : Option (GNat A) :=
  if h : s.isNat then some (ofLimbs (C.ofDecimal s) (C.ofDecimal_spec s h).1) else none

public theorem ofString?_eq (s : String) : (ofString? s : Option (GNat A)) = s.toNat?.map ofNat := by
  unfold ofString?
  split
  · rename_i h
    rw [(C.ofDecimal_spec s h).2, Option.map_some, Option.some.injEq, ← toNat_inj, toNat_ofLimbs,
      toNat_ofNat]
  · rename_i h
    rw [String.toNat?_eq_none (by simpa using h), Option.map_none]

/-! ## Instances -/

public instance : DecidableEq (GNat A) := decEq
public instance : Add (GNat A) := ⟨add⟩
public instance : Sub (GNat A) := ⟨sub⟩
public instance : Mul (GNat A) := ⟨mul⟩
public instance : Div (GNat A) := ⟨div⟩
public instance : Mod (GNat A) := ⟨mod⟩
public instance : LT (GNat A) := ⟨fun x y => x.toNat < y.toNat⟩
public instance : LE (GNat A) := ⟨fun x y => x.toNat ≤ y.toNat⟩
public instance (x y : GNat A) : Decidable (x < y) :=
  decidable_of_iff (blt x y = true) (blt_iff x y)
public instance (x y : GNat A) : Decidable (x ≤ y) :=
  decidable_of_iff (blt y x = false) (by
    show blt y x = false ↔ x.toNat ≤ y.toNat
    rw [← Bool.not_eq_true, blt_iff]
    lia)
public instance : Ord (GNat A) := ⟨fun x y => compareOfLessAndEq x y⟩
public instance : HShiftLeft (GNat A) Nat (GNat A) := ⟨shiftLeft⟩
public instance : HShiftRight (GNat A) Nat (GNat A) := ⟨shiftRight⟩
public instance : AndOp (GNat A) := ⟨land⟩
public instance : OrOp (GNat A) := ⟨lor⟩
public instance : XorOp (GNat A) := ⟨xor⟩
public instance : Pow (GNat A) Nat := ⟨pow⟩
public instance (n : Nat) : OfNat (GNat A) n := ⟨ofNat n⟩
public instance : Inhabited (GNat A) := ⟨small 0⟩
public instance : Hashable (GNat A) where
  hash
    | small n => hash n
    | large a _ => C.hash a
public instance : ToString (GNat A) := ⟨repr⟩
public instance : Repr (GNat A) := ⟨fun x _ => x.repr⟩

@[simp] public theorem toNat_hAdd (x y : GNat A) : (x + y).toNat = x.toNat + y.toNat :=
  toNat_add x y
@[simp] public theorem toNat_hSub (x y : GNat A) : (x - y).toNat = x.toNat - y.toNat :=
  toNat_sub x y
@[simp] public theorem toNat_hMul (x y : GNat A) : (x * y).toNat = x.toNat * y.toNat :=
  toNat_mul x y
@[simp] public theorem toNat_hDiv (x y : GNat A) : (x / y).toNat = x.toNat / y.toNat :=
  toNat_div x y
@[simp] public theorem toNat_hMod (x y : GNat A) : (x % y).toNat = x.toNat % y.toNat :=
  toNat_mod x y
@[simp] public theorem toNat_ofNat' (n : Nat) : (OfNat.ofNat n : GNat A).toNat = n :=
  toNat_ofNat n
public theorem lt_iff_toNat_lt {x y : GNat A} : x < y ↔ x.toNat < y.toNat := Iff.rfl
public theorem le_iff_toNat_le {x y : GNat A} : x ≤ y ↔ x.toNat ≤ y.toNat := Iff.rfl

end GNat

end MPN
