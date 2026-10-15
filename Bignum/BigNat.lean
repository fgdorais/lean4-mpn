/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bignum.Add
public import Bignum.Sub
public import Bignum.Cmp
public import Bignum.Mul
public import Bignum.Sqr
public import Bignum.Div

/-!
# Natural numbers

`BigNat` is a natural number as a machine word below `2⁶⁴` and as trimmed limbs above, so that
each natural number has exactly one representation: `toNat` and `ofNat` are inverse bijections
between `BigNat` and `Nat`, and equality, comparison and hashing work on the representation.

The arithmetic takes a fast path on words when both numbers are small, checking for overflow,
and otherwise works on limbs with the operations of this library. Every operation is proved
correct against `Nat`.

Lean's own `Nat` stores small values in the pointer itself; a type defined in Lean cannot, so
a small `BigNat` is a heap object holding its word, which costs an allocation per result.
-/

open ScalarArray

namespace Bignum

/-! ## Limbs and words -/

/-- A trimmed array of limbs is at least `β ^ (n - 1)` for `n` limbs. -/
private theorem pow_le_toNat_of_isTrimmed {a : UInt32Array} (h : isTrimmed a = true)
    (hpos : 0 < a.size) : 2 ^ (32 * (a.size - 1)) ≤ toNat a := by
  refine Nat.le_of_not_lt fun hlt => ?_
  rw [toNat_toSlice] at hlt
  have := getElem_eq_zero_of_ofLimbs_lt (l := a.toList) (k := a.size - 1) (by simp; omega) hlt
  rw [isTrimmed_iff, IsTrimmed, List.getLast?_eq_getElem?] at h
  simp only [UInt32Array.length_toList] at h
  rw [List.getElem?_eq_getElem (by simp; omega), this] at h
  exact h rfl

/-- The limbs of a word: none for `0`, one below `2³²`, two otherwise. -/
def limbsOfWord (n : UInt64) : UInt32Array :=
  if n = 0 then
    .empty
  else if n < 4294967296 then
    (UInt32Array.emptyWithCapacity 1).push n.toUInt32
  else
    ((UInt32Array.emptyWithCapacity 2).push n.toUInt32).push (n >>> 32).toUInt32

private theorem isTrimmed_of_getLast {a : UInt32Array} {x : UInt32} (h : a.toList.getLast? = some x)
    (hx : x ≠ 0) : isTrimmed a = true := by
  rw [isTrimmed_iff, IsTrimmed, h]
  intro h'
  exact hx (Option.some.inj h')

private theorem limbsOfWord_spec (n : UInt64) :
    toNat (limbsOfWord n) = n.toNat ∧ isTrimmed (limbsOfWord n) = true := by
  have hn := n.toNat_lt
  by_cases h : n = 0
  · have heq : limbsOfWord n = .empty := by rw [limbsOfWord, ite_eq_left h]
    rw [heq, h]
    exact ⟨by rw [toNat_toSlice]; rfl, by rw [isTrimmed_iff]; simp⟩
  · have h0 : n.toNat ≠ 0 := fun h'' => h (UInt64.toNat_inj.1 (by simpa using h''))
    by_cases h' : n < 4294967296
    · have heq : limbsOfWord n = (UInt32Array.emptyWithCapacity 1).push n.toUInt32 := by
        rw [limbsOfWord, ite_eq_right h, ite_eq_left h']
      have h' : n.toNat < 2 ^ 32 := by simpa [UInt64.lt_iff_toNat_lt] using h'
      have hl : (limbsOfWord n).toList = [n.toUInt32] := by
        rw [heq, UInt32Array.toList_push, UInt32Array.emptyWithCapacity_eq_empty]
        simp
      have hx : n.toUInt32 ≠ 0 := fun h'' => by
        have := congrArg UInt32.toNat h''
        simp only [UInt64.toNat_toUInt32, UInt32.toNat_zero] at this
        omega
      refine ⟨?_, isTrimmed_of_getLast (by rw [hl]; rfl) hx⟩
      rw [toNat_toSlice, hl]
      simp only [ofLimbs_cons, ofLimbs_nil, Nat.mul_zero, Nat.add_zero, UInt64.toNat_toUInt32]
      omega
    · have heq : limbsOfWord n =
          ((UInt32Array.emptyWithCapacity 2).push n.toUInt32).push (n >>> 32).toUInt32 := by
        rw [limbsOfWord, ite_eq_right h, ite_eq_right h']
      have h' : 2 ^ 32 ≤ n.toNat := by simpa [UInt64.lt_iff_toNat_lt] using h'
      have hhi : (n >>> 32).toNat = n.toNat / 2 ^ 32 := by
        simp [UInt64.toNat_shiftRight, Nat.shiftRight_eq_div_pow]
      have hl : (limbsOfWord n).toList = [n.toUInt32, (n >>> 32).toUInt32] := by
        rw [heq, UInt32Array.toList_push, UInt32Array.toList_push,
          UInt32Array.emptyWithCapacity_eq_empty]
        simp
      have hx : (n >>> 32).toUInt32 ≠ 0 := fun h'' => by
        have := congrArg UInt32.toNat h''
        simp only [UInt64.toNat_toUInt32, UInt32.toNat_zero, hhi] at this
        omega
      refine ⟨?_, isTrimmed_of_getLast (by rw [hl]; rfl) hx⟩
      rw [toNat_toSlice, hl]
      simp only [ofLimbs_cons, ofLimbs_nil, Nat.mul_zero, Nat.add_zero, UInt64.toNat_toUInt32, hhi]
      have : n.toNat / 2 ^ 32 < 2 ^ 32 := by omega
      rw [Nat.mod_eq_of_lt this]
      omega

/-- The word of an array of at most two limbs. -/
def wordOfLimbs (a : UInt32Array) : UInt64 :=
  (a.getD 0 0).toUInt64 + ((a.getD 1 0).toUInt64 <<< 32)

private theorem toNat_wordOfLimbs (a : UInt32Array) (h : a.size ≤ 2) :
    (wordOfLimbs a).toNat = toNat a := by
  have h₀ := (a.getD 0 0).toNat_lt
  have h₁ := (a.getD 1 0).toNat_lt
  have hw : (wordOfLimbs a).toNat = (a.getD 0 0).toNat + (a.getD 1 0).toNat * 2 ^ 32 := by
    simp only [wordOfLimbs, UInt64.toNat_add, UInt64.toNat_shiftLeft, UInt32.toNat_toUInt64,
      UInt64.reduceToNat, Nat.reduceMod, Nat.shiftLeft_eq]
    rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
  rw [hw, toNat_toSlice]
  have hl : a.toList = (a.toList.take 2) := (List.take_of_length_le (by simp; omega)).symm
  rw [hl, ofLimbs_take_add_one_getD, ofLimbs_take_add_one_getD]
  simp only [List.take_zero, ofLimbs_nil, Nat.mul_zero, Nat.pow_zero, Nat.one_mul, Nat.zero_add,
    UInt32Array.getD_eq_getD_getElem?, List.getD_eq_getElem?_getD, UInt32Array.getElem?_toList]
  omega

/-! ## The type -/

/-- A natural number: a machine word below `2⁶⁴`, trimmed limbs above. -/
public inductive BigNat where
  /-- A number below `2⁶⁴`. -/
  | small (n : UInt64)
  /-- A number of at least `2⁶⁴`, as trimmed limbs. -/
  | large (a : UInt32Array) (h : isTrimmed a = true ∧ 2 ^ 64 ≤ toNat a)

namespace BigNat

/-- The natural number that a `BigNat` denotes. -/
@[expose] public def toNat : BigNat → Nat
  | small n => n.toNat
  | large a _ => Bignum.toNat a

/-- The `BigNat` of a natural number. -/
public def ofNat (n : Nat) : BigNat :=
  if h : n < 2 ^ 64 then
    small n.toUInt64
  else
    large (Bignum.ofNat n) ⟨isTrimmed_ofNat n, by rw [toNat_ofNat]; omega⟩

@[simp] public theorem toNat_ofNat (n : Nat) : (ofNat n).toNat = n := by
  unfold ofNat
  split
  · rename_i h
    simp [toNat, Nat.mod_eq_of_lt h]
  · exact Bignum.toNat_ofNat n

public theorem toNat_small (n : UInt64) : (small n).toNat = n.toNat := rfl

/-- `toNat` is injective, since each number has one representation. -/
public theorem toNat_inj {x y : BigNat} : x.toNat = y.toNat ↔ x = y := by
  refine ⟨fun h => ?_, fun h => h ▸ rfl⟩
  cases x with
  | small m =>
    cases y with
    | small n => exact congrArg small (UInt64.toNat_inj.1 h)
    | large b hb =>
      have := m.toNat_lt
      simp only [toNat] at h
      omega
  | large a ha =>
    cases y with
    | small n =>
      have := n.toNat_lt
      simp only [toNat] at h
      omega
    | large b hb =>
      simp only [toNat] at h
      have : a = b := by rw [← ofNat_toNat ha.1, ← ofNat_toNat hb.1, h]
      subst this
      rfl

@[simp] public theorem ofNat_toNat (x : BigNat) : ofNat x.toNat = x :=
  toNat_inj.1 (toNat_ofNat _)

/-- The limbs of a `BigNat`, trimmed. -/
public def limbs : BigNat → UInt32Array
  | small n => limbsOfWord n
  | large a _ => a

public theorem toNat_limbs (x : BigNat) : Bignum.toNat x.limbs = x.toNat := by
  cases x with
  | small n => exact (limbsOfWord_spec n).1
  | large a _ => rfl

/-- The `BigNat` of trimmed limbs. -/
public def ofLimbs (a : UInt32Array) (h : isTrimmed a = true) : BigNat :=
  if hs : a.size ≤ 2 then
    small (wordOfLimbs a)
  else
    large a ⟨h, by
      have := pow_le_toNat_of_isTrimmed h (by omega)
      have : 2 ^ 64 ≤ 2 ^ (32 * (a.size - 1)) := Nat.pow_le_pow_right (by decide) (by omega)
      omega⟩

@[simp] public theorem toNat_ofLimbs (a : UInt32Array) (h : isTrimmed a = true) :
    (ofLimbs a h).toNat = Bignum.toNat a := by
  unfold ofLimbs
  split
  · rename_i hs
    exact toNat_wordOfLimbs a hs
  · rfl

/-! ## Arithmetic -/

/-- Addition: on words unless the sum overflows. -/
public def add : BigNat → BigNat → BigNat
  | small a, small b =>
    let s := a + b
    if s < a then
      ofLimbs (Bignum.add (limbsOfWord a) (limbsOfWord b)) (isTrimmed_add _ _)
    else
      small s
  | x, y => ofLimbs (Bignum.add x.limbs y.limbs) (isTrimmed_add _ _)

/-- Truncated subtraction, like `Nat`'s: `x - y = 0` when `x < y`. -/
public def sub : BigNat → BigNat → BigNat
  | small a, small b => if b ≤ a then small (a - b) else small 0
  | x, y =>
    if lt x.limbs y.limbs then small 0
    else ofLimbs (trim (subVal x.limbs y.limbs)) (isTrimmed_trim _)

/-- Multiplication: on words when both factors are below `2³²`. -/
public def mul : BigNat → BigNat → BigNat
  | small a, small b =>
    if a < 4294967296 ∧ b < 4294967296 then small (a * b)
    else ofLimbs (Bignum.mul (limbsOfWord a) (limbsOfWord b)) (isTrimmed_mul _ _)
  | x, y => ofLimbs (Bignum.mul x.limbs y.limbs) (isTrimmed_mul _ _)

/-- Division, like `Nat`'s: `x / 0 = 0`. -/
public def div : BigNat → BigNat → BigNat
  | small a, small b => small (a / b)
  | small _, large _ _ => small 0
  | x, y => ofLimbs (Bignum.div x.limbs y.limbs) (isTrimmed_div _ _)

/-- The remainder, like `Nat`'s: `x % 0 = x`. -/
public def mod : BigNat → BigNat → BigNat
  | small a, small b => small (a % b)
  | small a, large _ _ => small a
  | x, y => ofLimbs (Bignum.mod x.limbs y.limbs) (isTrimmed_mod _ _)

private theorem small_lt_large (a : UInt64) (b : UInt32Array)
    (hb : isTrimmed b = true ∧ 2 ^ 64 ≤ Bignum.toNat b) : (small a).toNat < (large b hb).toNat := by
  have := a.toNat_lt
  simp only [toNat]
  omega

@[simp] public theorem toNat_add (x y : BigNat) : (add x y).toNat = x.toNat + y.toNat := by
  have hgen : ∀ x y : BigNat, (ofLimbs (Bignum.add x.limbs y.limbs) (isTrimmed_add _ _)).toNat =
      x.toNat + y.toNat := fun x y => by
    rw [toNat_ofLimbs, Bignum.toNat_add, toNat_limbs, toNat_limbs]
  cases x with
  | small a =>
    cases y with
    | small b =>
      have ha := a.toNat_lt
      have hb := b.toNat_lt
      rw [add]
      split
      · rename_i h
        rw [toNat_ofLimbs, Bignum.toNat_add, (limbsOfWord_spec a).1, (limbsOfWord_spec b).1]
        rfl
      · rename_i h
        rw [UInt64.lt_iff_toNat_lt, UInt64.toNat_add] at h
        simp only [toNat, UInt64.toNat_add]
        omega
    | large b hb => exact hgen _ _
  | large a ha => exact hgen _ _

@[simp] public theorem toNat_sub (x y : BigNat) : (sub x y).toNat = x.toNat - y.toNat := by
  have hgen : ∀ x y : BigNat, (if lt x.limbs y.limbs then small 0
      else ofLimbs (trim (subVal x.limbs y.limbs)) (isTrimmed_trim _)).toNat =
      x.toNat - y.toNat := fun x y => by
    by_cases h : lt x.limbs y.limbs = true
    · rw [ite_eq_left h]
      rw [lt_iff, toNat_limbs, toNat_limbs] at h
      rw [toNat_small, UInt64.toNat_zero]
      omega
    · rw [ite_eq_right h]
      have h' : y.toNat ≤ x.toNat := by
        rw [lt_iff, toNat_limbs, toNat_limbs] at h
        omega
      rw [toNat_ofLimbs, toNat_trim, toNat_subVal _ _ (by rw [toNat_limbs, toNat_limbs]; exact h'),
        toNat_limbs, toNat_limbs]
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
        omega
    | large b hb => exact hgen _ _
  | large a ha => exact hgen _ _

@[simp] public theorem toNat_mul (x y : BigNat) : (mul x y).toNat = x.toNat * y.toNat := by
  have hgen : ∀ x y : BigNat, (ofLimbs (Bignum.mul x.limbs y.limbs) (isTrimmed_mul _ _)).toNat =
      x.toNat * y.toNat := fun x y => by
    rw [toNat_ofLimbs, Bignum.toNat_mul, toNat_limbs, toNat_limbs]
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
      · rw [toNat_ofLimbs, Bignum.toNat_mul, (limbsOfWord_spec a).1, (limbsOfWord_spec b).1]
        rfl
    | large b hb => exact hgen _ _
  | large a ha => exact hgen _ _

@[simp] public theorem toNat_div (x y : BigNat) : (div x y).toNat = x.toNat / y.toNat := by
  have hgen : ∀ x y : BigNat, (ofLimbs (Bignum.div x.limbs y.limbs) (isTrimmed_div _ _)).toNat =
      x.toNat / y.toNat := fun x y => by
    rw [toNat_ofLimbs, Bignum.toNat_div, toNat_limbs, toNat_limbs]
  cases x with
  | small a =>
    cases y with
    | small b => simp [div, toNat, UInt64.toNat_div]
    | large b hb =>
      have := small_lt_large a b hb
      simp only [div]
      rw [Nat.div_eq_of_lt this]
      rfl
  | large a ha => exact hgen _ _

@[simp] public theorem toNat_mod (x y : BigNat) : (mod x y).toNat = x.toNat % y.toNat := by
  have hgen : ∀ x y : BigNat, (ofLimbs (Bignum.mod x.limbs y.limbs) (isTrimmed_mod _ _)).toNat =
      x.toNat % y.toNat := fun x y => by
    rw [toNat_ofLimbs, Bignum.toNat_mod, toNat_limbs, toNat_limbs]
  cases x with
  | small a =>
    cases y with
    | small b => simp [mod, toNat, UInt64.toNat_mod]
    | large b hb =>
      have := small_lt_large a b hb
      simp only [mod]
      rw [Nat.mod_eq_of_lt this]
  | large a ha => exact hgen _ _

/-! ## Comparison -/

/-- Whether `x < y`. -/
public def blt : BigNat → BigNat → Bool
  | small a, small b => a < b
  | small _, large _ _ => true
  | large _ _, small _ => false
  | large a _, large b _ => lt a b

public theorem blt_iff (x y : BigNat) : blt x y = true ↔ x.toNat < y.toNat := by
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
      omega
    | large b hb => simp only [blt, lt_iff]; rfl

/-- Decides equality on the representation, which is unique. -/
public def decEq : (x y : BigNat) → Decidable (x = y)
  | small a, small b =>
    if h : a = b then isTrue (h ▸ rfl) else isFalse fun h' => h (by cases h'; rfl)
  | small a, large b hb => isFalse fun h' => by cases h'
  | large a ha, small b => isFalse fun h' => by cases h'
  | large a ha, large b hb =>
    if h : a = b then isTrue (by subst h; rfl) else isFalse fun h' => h (by cases h'; rfl)

/-! ## Instances -/

public instance : DecidableEq BigNat := decEq
public instance : Add BigNat := ⟨add⟩
public instance : Sub BigNat := ⟨sub⟩
public instance : Mul BigNat := ⟨mul⟩
public instance : Div BigNat := ⟨div⟩
public instance : Mod BigNat := ⟨mod⟩
public instance : LT BigNat := ⟨fun x y => x.toNat < y.toNat⟩
public instance : LE BigNat := ⟨fun x y => x.toNat ≤ y.toNat⟩
public instance (x y : BigNat) : Decidable (x < y) :=
  decidable_of_iff (blt x y = true) (blt_iff x y)
public instance (x y : BigNat) : Decidable (x ≤ y) :=
  decidable_of_iff (blt y x = false) (by
    show blt y x = false ↔ x.toNat ≤ y.toNat
    rw [← Bool.not_eq_true, blt_iff]
    omega)
public instance : Ord BigNat := ⟨fun x y => compareOfLessAndEq x y⟩
public instance (n : Nat) : OfNat BigNat n := ⟨ofNat n⟩
public instance : Inhabited BigNat := ⟨small 0⟩
public instance : Hashable BigNat where
  hash
    | small n => hash n
    | large a _ => hash a
public instance : ToString BigNat := ⟨fun x => toString x.toNat⟩
public instance : Repr BigNat := ⟨fun x _ => repr x.toNat⟩

@[simp] public theorem toNat_hAdd (x y : BigNat) : (x + y).toNat = x.toNat + y.toNat :=
  toNat_add x y
@[simp] public theorem toNat_hSub (x y : BigNat) : (x - y).toNat = x.toNat - y.toNat :=
  toNat_sub x y
@[simp] public theorem toNat_hMul (x y : BigNat) : (x * y).toNat = x.toNat * y.toNat :=
  toNat_mul x y
@[simp] public theorem toNat_hDiv (x y : BigNat) : (x / y).toNat = x.toNat / y.toNat :=
  toNat_div x y
@[simp] public theorem toNat_hMod (x y : BigNat) : (x % y).toNat = x.toNat % y.toNat :=
  toNat_mod x y
@[simp] public theorem toNat_ofNat' (n : Nat) : (OfNat.ofNat n : BigNat).toNat = n :=
  toNat_ofNat n
public theorem lt_iff_toNat_lt {x y : BigNat} : x < y ↔ x.toNat < y.toNat := Iff.rfl
public theorem le_iff_toNat_le {x y : BigNat} : x ≤ y ↔ x.toNat ≤ y.toNat := Iff.rfl

end BigNat

end Bignum
