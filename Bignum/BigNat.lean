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
public import Bignum.Bits
public import Bignum.Decimal
public import Bignum.MulSubMul
import Std.Data.String.ToNat
import all Init.Data.Repr

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

/-! ## Results of two words

A sum or product of two words can overflow 64 bits. `mulWide` computes the whole product of two
words from the four products of their halves, and `wideOf` makes the `BigNat` of a two-word
number directly, as one array of three or four limbs, where the general arithmetic would make an
array for each word first.
-/

/-- The three or four limbs of `lo + 2⁶⁴ hi`, for `hi ≠ 0`. -/
def limbs4 (lo hi : UInt64) : UInt32Array :=
  let r := (((UInt32Array.emptyWithCapacity 4).push lo.toUInt32).push (lo >>> 32).toUInt32).push
    hi.toUInt32
  if hi < 4294967296 then r else r.push (hi >>> 32).toUInt32

private theorem toList_limbs4 (lo hi : UInt64) :
    (limbs4 lo hi).toList = [lo.toUInt32, (lo >>> 32).toUInt32, hi.toUInt32] ++
      (if hi < 4294967296 then [] else [(hi >>> 32).toUInt32]) := by
  unfold limbs4
  split <;> simp

private theorem limbs4_spec (lo hi : UInt64) (h : hi ≠ 0) :
    isTrimmed (limbs4 lo hi) = true ∧
      Bignum.toNat (limbs4 lo hi) = lo.toNat + 2 ^ 64 * hi.toNat := by
  have hl := lo.toNat_lt
  have hh := hi.toNat_lt
  have h0 : hi.toNat ≠ 0 := fun e => h (UInt64.toNat_inj.1 (by simpa using e))
  rw [toNat_toSlice, toList_limbs4]
  by_cases hs : hi < 4294967296
  · have hs' := hs
    rw [UInt64.lt_iff_toNat_lt] at hs'
    simp only [UInt64.reduceToNat] at hs'
    refine ⟨isTrimmed_of_getLast (x := hi.toUInt32) (by rw [toList_limbs4]; simp [hs]) ?_, ?_⟩
    · intro e
      have := congrArg UInt32.toNat e
      simp only [UInt64.toNat_toUInt32, UInt32.toNat_zero] at this
      omega
    · simp only [hs, ite_true, List.append_nil, ofLimbs_cons, ofLimbs_nil, UInt64.toNat_toUInt32,
        UInt64.toNat_shiftRight, UInt64.reduceToNat, Nat.reduceMod, Nat.shiftRight_eq_div_pow]
      omega
  · have hs' := hs
    rw [UInt64.lt_iff_toNat_lt] at hs'
    simp only [UInt64.reduceToNat] at hs'
    refine ⟨isTrimmed_of_getLast (x := (hi >>> 32).toUInt32) (by rw [toList_limbs4]; simp [hs])
      ?_, ?_⟩
    · intro e
      have := congrArg UInt32.toNat e
      simp only [UInt64.toNat_toUInt32, UInt64.toNat_shiftRight, UInt64.reduceToNat,
        Nat.reduceMod, Nat.shiftRight_eq_div_pow, UInt32.toNat_zero] at this
      omega
    · simp only [hs, ite_false, List.cons_append, List.nil_append, ofLimbs_cons, ofLimbs_nil,
        UInt64.toNat_toUInt32, UInt64.toNat_shiftRight, UInt64.reduceToNat, Nat.reduceMod,
        Nat.shiftRight_eq_div_pow]
      omega

/-- The `BigNat` `lo + 2⁶⁴ hi`. -/
def wideOf (lo hi : UInt64) : BigNat :=
  if h : hi = 0 then small lo
  else large (limbs4 lo hi) ⟨(limbs4_spec lo hi h).1, by
    rw [(limbs4_spec lo hi h).2]
    have : hi.toNat ≠ 0 := fun e => h (UInt64.toNat_inj.1 (by simpa using e))
    have := Nat.mul_le_mul_left (2 ^ 64) (Nat.one_le_iff_ne_zero.2 this)
    omega⟩

private theorem toNat_wideOf (lo hi : UInt64) :
    (wideOf lo hi).toNat = lo.toNat + 2 ^ 64 * hi.toNat := by
  unfold wideOf
  split
  · rename_i h
    subst h
    simp [toNat]
  · rename_i h
    exact (limbs4_spec lo hi h).2

/-- The product of two words as its low word and its high word, from the products of halves. -/
def mulWide (a b : UInt64) : UInt64 × UInt64 :=
  let a₀ := a &&& 0xFFFFFFFF
  let a₁ := a >>> 32
  let b₀ := b &&& 0xFFFFFFFF
  let b₁ := b >>> 32
  let p₀₀ := a₀ * b₀
  let p₀₁ := a₀ * b₁
  let p₁₀ := a₁ * b₀
  let mid := (p₀₀ >>> 32) + (p₀₁ &&& 0xFFFFFFFF) + (p₁₀ &&& 0xFFFFFFFF)
  ((mid <<< 32) + (p₀₀ &&& 0xFFFFFFFF), a₁ * b₁ + (p₀₁ >>> 32) + (p₁₀ >>> 32) + (mid >>> 32))

private theorem mulWide_spec (a b : UInt64) :
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
  have hA₁ : a.toNat / 2 ^ 32 < 2 ^ 32 := by omega
  have hB₁ : b.toNat / 2 ^ 32 < 2 ^ 32 := by omega
  generalize a.toNat % 2 ^ 32 = A₀ at *
  generalize b.toNat % 2 ^ 32 = B₀ at *
  generalize a.toNat / 2 ^ 32 = A₁ at *
  generalize b.toNat / 2 ^ 32 = B₁ at *
  have hprod : a.toNat * b.toNat =
      2 ^ 64 * (A₁ * B₁) + 2 ^ 32 * (A₀ * B₁) + 2 ^ 32 * (A₁ * B₀) + A₀ * B₀ := by
    rw [e₁, e₂]
    simp only [Nat.mul_add, Nat.add_mul]
    grind
  have b₀₀ : A₀ * B₀ ≤ 4294967295 * 4294967295 := Nat.mul_le_mul (by omega) (by omega)
  have b₀₁ : A₀ * B₁ ≤ 4294967295 * 4294967295 := Nat.mul_le_mul (by omega) (by omega)
  have b₁₀ : A₁ * B₀ ≤ 4294967295 * 4294967295 := Nat.mul_le_mul (by omega) (by omega)
  have b₁₁ : A₁ * B₁ ≤ 4294967295 * 4294967295 := Nat.mul_le_mul (by omega) (by omega)
  rw [hprod]
  generalize A₀ * B₀ = P₀₀ at *
  generalize A₀ * B₁ = P₀₁ at *
  generalize A₁ * B₀ = P₁₀ at *
  generalize A₁ * B₁ = P₁₁ at *
  rw [Nat.mod_eq_of_lt (show P₀₀ < 2 ^ 64 by omega), Nat.mod_eq_of_lt (show P₀₁ < 2 ^ 64 by omega),
    Nat.mod_eq_of_lt (show P₁₀ < 2 ^ 64 by omega), Nat.mod_eq_of_lt (show P₁₁ < 2 ^ 64 by omega)]
  omega

/-! ## Arithmetic -/

/-- Addition: on words unless the sum overflows. -/
public def add : BigNat → BigNat → BigNat
  | small a, small b =>
    let s := a + b
    if s < a then wideOf s 1 else small s
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
    else wideOf (mulWide a b).1 (mulWide a b).2
  | x, y => ofLimbs (Bignum.mul x.limbs y.limbs) (isTrimmed_mul _ _)

/--
`a` divided by a nonzero word `b`, as untrimmed quotient limbs and the remainder, a word: `divRem1`
below `2³²` and `divRem2` above, without an array for `b`.
-/
def divRemWord (a : UInt32Array) (b : UInt64) : UInt32Array × UInt64 :=
  if b < 4294967296 then
    let p := divRem1 a b.toUInt32
    (p.1, p.2.toUInt64)
  else
    divRem2 a (b >>> 32).toUInt32 b.toUInt32

private theorem divRemWord_spec (a : UInt32Array) (b : UInt64) (hb : b ≠ 0) :
    Bignum.toNat (divRemWord a b).1 = Bignum.toNat a / b.toNat ∧
      (divRemWord a b).2.toNat = Bignum.toNat a % b.toNat := by
  have hb' : 0 < b.toNat := by
    rcases Nat.eq_zero_or_pos b.toNat with h | h
    · exact absurd (UInt64.toNat_inj.1 (by simpa using h)) hb
    · exact h
  have hB := b.toNat_lt
  -- `q b + r = a` with `r < b` determines both.
  have key : ∀ q r : Nat, q * b.toNat + r = Bignum.toNat a → r < b.toNat →
      q = Bignum.toNat a / b.toNat ∧ r = Bignum.toNat a % b.toNat := fun q r h₁ h₂ => by
    have := (Nat.div_mod_unique (a := Bignum.toNat a) (b := b.toNat) (d := q) (c := r) hb').2
      ⟨by rw [Nat.mul_comm b.toNat q]; omega, h₂⟩
    exact ⟨this.1.symm, this.2.symm⟩
  unfold divRemWord
  by_cases hs : b < 4294967296
  · rw [ite_eq_left hs]
    rw [UInt64.lt_iff_toNat_lt] at hs
    simp only [UInt64.reduceToNat] at hs
    have hd : b.toUInt32.toNat = b.toNat := by simp; omega
    have hd0 : b.toUInt32 ≠ 0 := fun e => by
      have := congrArg UInt32.toNat e
      rw [hd, UInt32.toNat_zero] at this
      omega
    obtain ⟨h₁, h₂⟩ := divRem1_spec a b.toUInt32 hd0
    rw [hd] at h₁ h₂
    simp only [UInt32.toNat_toUInt64]
    exact key _ _ h₁ h₂
  · rw [ite_eq_right hs]
    rw [UInt64.lt_iff_toNat_lt] at hs
    simp only [UInt64.reduceToNat] at hs
    have hd : ((b >>> 32).toUInt32).toNat * 2 ^ 32 + b.toUInt32.toNat = b.toNat := by
      simp only [UInt64.toNat_toUInt32, UInt64.toNat_shiftRight, UInt64.reduceToNat,
        Nat.reduceMod, Nat.shiftRight_eq_div_pow]
      omega
    have hd0 : (b >>> 32).toUInt32 ≠ 0 := fun e => by
      have := congrArg UInt32.toNat e
      simp only [UInt64.toNat_toUInt32, UInt64.toNat_shiftRight, UInt64.reduceToNat,
        Nat.reduceMod, Nat.shiftRight_eq_div_pow, UInt32.toNat_zero] at this
      omega
    obtain ⟨h₁, h₂⟩ := divRem2_spec a (b >>> 32).toUInt32 b.toUInt32 hd0
    rw [hd] at h₁ h₂
    exact key _ _ h₁ h₂

/--
`a / b` and `a % b` in words for `a < 2¹²⁸` (at most four limbs, read with `getD`) and
`2³² ≤ b`, without arrays: `a` is shifted left by `s` with four `shlStep`s, which normalizes `b`
as in `divRem2`, and divided by three `div2Step`s: the quotient is below `2⁹⁶`, so the top two
limbs of the shifted `a` are already below the divisor and start the remainder. The quotient comes
as its low word and its high word.
-/
def divRem128 (a : UInt32Array) (b : UInt64) : UInt64 × UInt64 × UInt64 :=
  let sN := 31 - (b >>> 32).toUInt32.toNat.log2
  let s := sN.toUInt64
  let V := b <<< s
  let vt := (V >>> 32).toUInt32
  let vs := V.toUInt32
  let p₀ := shlStep s (a.getD 0 0) 0
  let p₁ := shlStep s (a.getD 1 0) p₀.2
  let p₂ := shlStep s (a.getD 2 0) p₁.2
  let p₃ := shlStep s (a.getD 3 0) p₂.2
  let t₂ := div2Step vt vs ((p₃.2.toUInt64 <<< 32) + p₃.1.toUInt64) p₂.1
  let t₁ := div2Step vt vs t₂.2 p₁.1
  let t₀ := div2Step vt vs t₁.2 p₀.1
  (t₀.1.toUInt64 + (t₁.1.toUInt64 <<< 32), t₂.1.toUInt64, t₀.2 >>> s)

/--
Unscaling a division: `X S = Q (b S) + r` with `r < b S` gives `X / b = Q` and `X % b = r / S`.
-/
private theorem div_of_scaled {X Q b S r : Nat} (hS : 0 < S) (h : X * S = Q * (b * S) + r)
    (hr : r < b * S) : X / b = Q ∧ X % b = r / S := by
  have hQ : Q * b ≤ X := by
    refine Nat.le_of_not_lt fun hlt => ?_
    have := Nat.mul_le_mul_right S (show X + 1 ≤ Q * b by omega)
    rw [Nat.add_mul, Nat.one_mul, Nat.mul_assoc] at this
    omega
  have hr' : r = (X - Q * b) * S := by
    rw [Nat.sub_mul, Nat.mul_assoc Q b S]
    omega
  have hrS : r / S = X - Q * b := by rw [hr', Nat.mul_div_cancel _ hS]
  have hlt : X - Q * b < b := by
    rw [hr'] at hr
    exact Nat.lt_of_mul_lt_mul_right hr
  have hb : 0 < b := by omega
  have := (Nat.div_mod_unique (a := X) (b := b) (d := Q) (c := X - Q * b) hb).2
    ⟨by rw [Nat.mul_comm b Q]; omega, hlt⟩
  exact ⟨this.1, by rw [hrS]; exact this.2⟩

/-- The value of at most four limbs. -/
private theorem toNat_four (a : UInt32Array) (ha : a.size ≤ 4) :
    Bignum.toNat a = (a.getD 0 0).toNat + 2 ^ 32 * (a.getD 1 0).toNat +
      2 ^ 64 * (a.getD 2 0).toNat + 2 ^ 96 * (a.getD 3 0).toNat := by
  rw [toNat_toSlice]
  have hl : a.toList = (a.toList.take 4) := (List.take_of_length_le (by simp; omega)).symm
  rw [hl, ofLimbs_take_add_one_getD, ofLimbs_take_add_one_getD, ofLimbs_take_add_one_getD,
    ofLimbs_take_add_one_getD]
  simp only [List.take_zero, ofLimbs_nil, UInt32Array.getD_eq_getD_getElem?,
    List.getD_eq_getElem?_getD, UInt32Array.getElem?_toList]
  simp only [Nat.mul_zero, Nat.pow_zero, Nat.one_mul, Nat.zero_add, Nat.mul_one,
    Nat.reduceMul]

private theorem divRem128_spec (a : UInt32Array) (b : UInt64) (ha : a.size ≤ 4)
    (hb : 4294967296 ≤ b) :
    (divRem128 a b).1.toNat + 2 ^ 64 * (divRem128 a b).2.1.toNat = Bignum.toNat a / b.toNat ∧
      (divRem128 a b).2.2.toNat = Bignum.toNat a % b.toNat := by
  rw [UInt64.le_iff_toNat_le] at hb
  simp only [UInt64.reduceToNat] at hb
  have hbβ := b.toNat_lt
  -- The normalization: `V = b 2ˢ < 2⁶⁴` with `s = 31 - log₂ d₁` for the top limb `d₁` of `b`.
  have hd₁ : (b >>> 32).toUInt32.toNat = b.toNat / 2 ^ 32 := by
    simp only [UInt64.toNat_toUInt32, UInt64.toNat_shiftRight, UInt64.reduceToNat, Nat.reduceMod,
      Nat.shiftRight_eq_div_pow]
    omega
  have hd₁0 : b.toNat / 2 ^ 32 ≠ 0 := by omega
  have hl : (b.toNat / 2 ^ 32).log2 < 32 := (Nat.log2_lt hd₁0).2 (by omega)
  have hlt := Nat.lt_log2_self (n := b.toNat / 2 ^ 32)
  have hge := Nat.log2_self_le hd₁0
  simp only [divRem128, hd₁]
  generalize (b.toNat / 2 ^ 32).log2 = l at hl hlt hge
  have hS : 0 < 2 ^ (31 - l) := Nat.two_pow_pos _
  have hsU : (31 - l).toUInt64.toNat = 31 - l := by
    simp only [Nat.toUInt64, UInt64.toNat_ofNat']
    exact Nat.mod_eq_of_lt (by omega)
  have hV64 : b.toNat * 2 ^ (31 - l) < 2 ^ 64 := by
    have h₁ : b.toNat < 2 ^ (l + 1) * 2 ^ 32 := by
      have := Nat.mul_le_mul_right (2 ^ 32) (show b.toNat / 2 ^ 32 + 1 ≤ 2 ^ (l + 1) by omega)
      rw [Nat.succ_mul] at this
      omega
    have h₂ : 2 ^ (l + 1) * 2 ^ 32 * 2 ^ (31 - l) = 2 ^ 64 := by
      rw [← Nat.pow_add, ← Nat.pow_add]; congr 1; omega
    rw [← h₂]
    exact Nat.mul_lt_mul_of_pos_right h₁ hS
  have hV : (b <<< (31 - l).toUInt64).toNat = b.toNat * 2 ^ (31 - l) := by
    rw [UInt64.toNat_shiftLeft, hsU, Nat.mod_eq_of_lt (show 31 - l < 64 by omega),
      Nat.shiftLeft_eq, Nat.mod_eq_of_lt hV64]
  have hvtvs : ((b <<< (31 - l).toUInt64) >>> 32).toUInt32.toNat * 2 ^ 32 +
      (b <<< (31 - l).toUInt64).toUInt32.toNat = b.toNat * 2 ^ (31 - l) := by
    simp only [UInt64.toNat_toUInt32, UInt64.toNat_shiftRight, UInt64.reduceToNat, Nat.reduceMod,
      Nat.shiftRight_eq_div_pow, hV]
    omega
  have hVge : 2 ^ 32 * 2 ^ (31 - l) ≤ b.toNat * 2 ^ (31 - l) := Nat.mul_le_mul_right _ hb
  have hvt : 0 < ((b <<< (31 - l).toUInt64) >>> 32).toUInt32.toNat := by
    simp only [UInt64.toNat_toUInt32, UInt64.toNat_shiftRight, UInt64.reduceToNat, Nat.reduceMod,
      Nat.shiftRight_eq_div_pow, hV]
    have : 2 ^ 32 ≤ b.toNat * 2 ^ (31 - l) := Nat.le_trans (Nat.le_mul_of_pos_right _ hS) hVge
    omega
  generalize ((b <<< (31 - l).toUInt64) >>> 32).toUInt32 = vt at hvtvs hvt ⊢
  generalize (b <<< (31 - l).toUInt64).toUInt32 = vs at hvtvs ⊢
  -- The shift: four `shlStep`s make `X 2ˢ` in five words.
  obtain ⟨e₀, c₀⟩ := shlStep_spec (31 - l) (by omega) (a.getD 0 0) 0 (by simpa using hS)
  simp only [UInt32.toNat_zero, Nat.add_zero] at e₀
  obtain ⟨e₁, c₁⟩ := shlStep_spec (31 - l) (by omega) (a.getD 1 0) _ c₀
  obtain ⟨e₂, c₂⟩ := shlStep_spec (31 - l) (by omega) (a.getD 2 0) _ c₁
  obtain ⟨e₃, c₃⟩ := shlStep_spec (31 - l) (by omega) (a.getD 3 0) _ c₂
  generalize shlStep (31 - l).toUInt64 (a.getD 0 0) 0 = p₀ at *
  generalize shlStep (31 - l).toUInt64 (a.getD 1 0) p₀.2 = p₁ at *
  generalize shlStep (31 - l).toUInt64 (a.getD 2 0) p₁.2 = p₂ at *
  generalize shlStep (31 - l).toUInt64 (a.getD 3 0) p₂.2 = p₃ at *
  have hX := toNat_four a ha
  have hXlt : Bignum.toNat a < 2 ^ 128 := by
    have := (a.getD 0 0).toNat_lt; have := (a.getD 1 0).toNat_lt
    have := (a.getD 2 0).toNat_lt; have := (a.getD 3 0).toNat_lt
    omega
  -- The top two words start the remainder, below `V`.
  have hR0 : ((p₃.2.toUInt64 <<< 32) + p₃.1.toUInt64).toNat =
      p₃.2.toNat * 2 ^ 32 + p₃.1.toNat := by
    have := p₃.1.toNat_lt
    have : p₃.2.toNat < 2 ^ 31 :=
      Nat.lt_of_lt_of_le c₃ (Nat.pow_le_pow_right (by decide) (by omega))
    simp only [UInt64.toNat_add, UInt64.toNat_shiftLeft, UInt32.toNat_toUInt64, UInt64.reduceToNat,
      Nat.reduceMod, Nat.shiftLeft_eq]
    omega
  generalize hSdef : 2 ^ (31 - l) = S at *
  generalize Bignum.toNat a = X at *
  generalize b.toNat = B at *
  -- `X S = W`, the five words.
  have hW : X * S = p₀.1.toNat + 2 ^ 32 * p₁.1.toNat + 2 ^ 64 * p₂.1.toNat +
      2 ^ 96 * (p₃.2.toNat * 2 ^ 32 + p₃.1.toNat) := by
    rw [hX]
    simp only [Nat.add_mul, Nat.mul_assoc]
    omega
  have hXS : X * S < 2 ^ 128 * S := Nat.mul_lt_mul_of_pos_right hXlt hS
  have hR0lt : ((p₃.2.toUInt64 <<< 32) + p₃.1.toUInt64).toNat < vt.toNat * 2 ^ 32 + vs.toNat := by
    rw [hR0, hvtvs]
    omega
  -- The three steps.
  obtain ⟨q₂, r₂⟩ := div2Step_spec vt vs _ p₂.1 hvt hR0lt
  have hr₂ := Nat.mod_lt ((((p₃.2.toUInt64 <<< 32) + p₃.1.toUInt64).toNat * 2 ^ 32 +
    p₂.1.toNat)) (show 0 < vt.toNat * 2 ^ 32 + vs.toNat by omega)
  rw [← r₂] at hr₂
  generalize div2Step vt vs ((p₃.2.toUInt64 <<< 32) + p₃.1.toUInt64) p₂.1 = t₂ at *
  obtain ⟨q₁, r₁⟩ := div2Step_spec vt vs t₂.2 p₁.1 hvt hr₂
  have hr₁ := Nat.mod_lt (t₂.2.toNat * 2 ^ 32 + p₁.1.toNat)
    (show 0 < vt.toNat * 2 ^ 32 + vs.toNat by omega)
  rw [← r₁] at hr₁
  generalize div2Step vt vs t₂.2 p₁.1 = t₁ at *
  obtain ⟨q₀, r₀⟩ := div2Step_spec vt vs t₁.2 p₀.1 hvt hr₁
  have hr₀ := Nat.mod_lt (t₁.2.toNat * 2 ^ 32 + p₀.1.toNat)
    (show 0 < vt.toNat * 2 ^ 32 + vs.toNat by omega)
  rw [← r₀] at hr₀
  generalize div2Step vt vs t₁.2 p₀.1 = t₀ at *
  rw [hR0] at q₂ r₂
  rw [hvtvs] at q₂ r₂ q₁ r₁ q₀ r₀ hr₀
  -- `W = Q V + r` with `Q = q₀ + β q₁ + β² q₂`.
  have d₂ := Nat.div_add_mod ((p₃.2.toNat * 2 ^ 32 + p₃.1.toNat) * 2 ^ 32 + p₂.1.toNat) (B * S)
  have d₁ := Nat.div_add_mod (t₂.2.toNat * 2 ^ 32 + p₁.1.toNat) (B * S)
  have d₀ := Nat.div_add_mod (t₁.2.toNat * 2 ^ 32 + p₀.1.toNat) (B * S)
  rw [← q₂, ← r₂] at d₂
  rw [← q₁, ← r₁] at d₁
  rw [← q₀, ← r₀] at d₀
  have hQ : X * S = (t₀.1.toNat + 2 ^ 32 * t₁.1.toNat + 2 ^ 64 * t₂.1.toNat) * (B * S) +
      t₀.2.toNat := by
    rw [hW]
    generalize B * S = V at *
    rw [Nat.add_mul, Nat.add_mul, Nat.mul_assoc, Nat.mul_assoc, Nat.mul_comm t₀.1.toNat V,
      Nat.mul_comm t₁.1.toNat V, Nat.mul_comm t₂.1.toNat V]
    omega
  obtain ⟨hq, hr⟩ := div_of_scaled hS hQ hr₀
  refine ⟨?_, ?_⟩
  · have := t₀.1.toNat_lt
    have := t₁.1.toNat_lt
    simp only [UInt64.toNat_add, UInt64.toNat_shiftLeft, UInt32.toNat_toUInt64,
      UInt64.reduceToNat, Nat.reduceMod, Nat.shiftLeft_eq]
    rw [hq]
    omega
  · rw [hr, UInt64.toNat_shiftRight, hsU, Nat.mod_eq_of_lt (show 31 - l < 64 by omega),
      Nat.shiftRight_eq_div_pow, hSdef]

/-- `divRemWord` without the remainder, which `div2` saves allocating. -/
def divWord (a : UInt32Array) (b : UInt64) : UInt32Array :=
  if b < 4294967296 then (divRem1 a b.toUInt32).1 else div2 a (b >>> 32).toUInt32 b.toUInt32

private theorem divWord_eq (a : UInt32Array) (b : UInt64) : divWord a b = (divRemWord a b).1 := by
  unfold divWord divRemWord
  split <;> simp [div2_eq]

/-- Division, like `Nat`'s: `x / 0 = 0`. -/
public def div : BigNat → BigNat → BigNat
  | small a, small b => small (a / b)
  | small _, large _ _ => small 0
  | large a _, small b =>
    if b = 0 then small 0
    else if a.size ≤ 4 ∧ 4294967296 ≤ b then wideOf (divRem128 a b).1 (divRem128 a b).2.1
    else ofLimbs (trim (divWord a b)) (isTrimmed_trim _)
  | x, y => ofLimbs (Bignum.div x.limbs y.limbs) (isTrimmed_div _ _)

/-- The remainder, like `Nat`'s: `x % 0 = x`. -/
public def mod : BigNat → BigNat → BigNat
  | small a, small b => small (a % b)
  | small a, large _ _ => small a
  | large a ha, small b =>
    if b = 0 then large a ha
    else if a.size ≤ 4 ∧ 4294967296 ≤ b then small (divRem128 a b).2.2
    else small (divRemWord a b).2
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
        rw [UInt64.lt_iff_toNat_lt, UInt64.toNat_add] at h
        rw [toNat_wideOf, UInt64.toNat_add]
        simp only [toNat, UInt64.toNat_one]
        omega
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
      · rw [toNat_wideOf, mulWide_spec]
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
  | large a ha =>
    cases y with
    | small b =>
      simp only [div]
      split
      · rename_i h
        subst h
        simp [toNat]
      · rename_i h
        split
        · rename_i h'
          rw [toNat_wideOf, (divRem128_spec a b h'.1 h'.2).1]
          rfl
        · rw [toNat_ofLimbs, toNat_trim, divWord_eq, (divRemWord_spec a b h).1]
          rfl
    | large b hb => exact hgen _ _

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
  | large a ha =>
    cases y with
    | small b =>
      simp only [mod]
      split
      · rename_i h
        subst h
        simp [toNat]
      · rename_i h
        split
        · rename_i h'
          rw [toNat_small, (divRem128_spec a b h'.1 h'.2).2]
          rfl
        · rw [toNat_small, (divRemWord_spec a b h).2]
          rfl
    | large b hb => exact hgen _ _

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

/-! ## Shifts, bits and `log2` -/

/-- `x <<< n = x * 2ⁿ`: on words when it fits. -/
public def shiftLeft (x : BigNat) (n : Nat) : BigNat :=
  match x with
  | small a =>
    if n = 0 then small a
    else if n < 64 ∧ a >>> (64 - n).toUInt64 = 0 then small (a <<< n.toUInt64)
    else ofLimbs (Bignum.shiftLeft (limbsOfWord a) n) (isTrimmed_shiftLeft _ _)
  | large a _ => ofLimbs (Bignum.shiftLeft a n) (isTrimmed_shiftLeft _ _)

/-- `x >>> n = x / 2ⁿ`. -/
public def shiftRight (x : BigNat) (n : Nat) : BigNat :=
  match x with
  | small a => if n < 64 then small (a >>> n.toUInt64) else small 0
  | large a _ => ofLimbs (Bignum.shiftRight a n) (isTrimmed_shiftRight _ _)

@[simp] public theorem toNat_shiftLeft (x : BigNat) (n : Nat) :
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
          rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
        have hn' : n.toUInt64.toNat % 64 = n := by
          simp only [Nat.toUInt64, UInt64.toNat_ofNat']
          rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
        rw [hn] at h₂
        have hlt : a.toNat < 2 ^ (64 - n) := by
          rcases Nat.eq_zero_or_pos (a.toNat / 2 ^ (64 - n)) with h | h
          · exact (Nat.div_eq_zero_iff_lt (Nat.two_pow_pos _)).1 h
          · omega
        have : a.toNat * 2 ^ n < 2 ^ 64 := by
          have := Nat.mul_lt_mul_of_pos_right hlt (Nat.two_pow_pos n)
          rwa [← Nat.pow_add, show 64 - n + n = 64 by omega] at this
        simp only [toNat, UInt64.toNat_shiftLeft, hn', Nat.shiftLeft_eq]
        exact Nat.mod_eq_of_lt this
      · rw [toNat_ofLimbs, Bignum.toNat_shiftLeft, (limbsOfWord_spec a).1]
        rfl
  | large a ha =>
    simp only [shiftLeft]
    rw [toNat_ofLimbs, Bignum.toNat_shiftLeft]
    rfl

@[simp] public theorem toNat_shiftRight (x : BigNat) (n : Nat) :
    (shiftRight x n).toNat = x.toNat / 2 ^ n := by
  cases x with
  | small a =>
    have ha := a.toNat_lt
    simp only [shiftRight]
    split
    · rename_i h
      have hn' : n.toUInt64.toNat % 64 = n := by
        simp only [Nat.toUInt64, UInt64.toNat_ofNat']
        rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
      simp only [toNat, UInt64.toNat_shiftRight, hn', Nat.shiftRight_eq_div_pow]
    · rename_i h
      have : 2 ^ 64 ≤ 2 ^ n := Nat.pow_le_pow_right (by decide) (by omega)
      simp only [toNat, UInt64.toNat_zero]
      exact (Nat.div_eq_of_lt (by omega)).symm
  | large a ha =>
    simp only [shiftRight]
    rw [toNat_ofLimbs, Bignum.toNat_shiftRight]
    rfl

/-- `x &&& y`: on words when both are small. -/
public def land : BigNat → BigNat → BigNat
  | small a, small b => small (a &&& b)
  | x, y => ofLimbs (Bignum.land x.limbs y.limbs) (isTrimmed_land _ _)

/-- `x ||| y`: on words when both are small. -/
public def lor : BigNat → BigNat → BigNat
  | small a, small b => small (a ||| b)
  | x, y => ofLimbs (Bignum.lor x.limbs y.limbs) (isTrimmed_lor _ _)

/-- `x ^^^ y`: on words when both are small. -/
public def xor : BigNat → BigNat → BigNat
  | small a, small b => small (a ^^^ b)
  | x, y => ofLimbs (Bignum.xor x.limbs y.limbs) (isTrimmed_xor _ _)

@[simp] public theorem toNat_land (x y : BigNat) : (land x y).toNat = x.toNat &&& y.toNat := by
  have hgen : ∀ x y : BigNat, (ofLimbs (Bignum.land x.limbs y.limbs) (isTrimmed_land _ _)).toNat =
      x.toNat &&& y.toNat := fun x y => by
    rw [toNat_ofLimbs, Bignum.toNat_land, toNat_limbs, toNat_limbs]
  cases x with
  | small a => cases y with
    | small b => simp [land, toNat, UInt64.toNat_and]
    | large b hb => exact hgen _ _
  | large a ha => exact hgen _ _

@[simp] public theorem toNat_lor (x y : BigNat) : (lor x y).toNat = x.toNat ||| y.toNat := by
  have hgen : ∀ x y : BigNat, (ofLimbs (Bignum.lor x.limbs y.limbs) (isTrimmed_lor _ _)).toNat =
      x.toNat ||| y.toNat := fun x y => by
    rw [toNat_ofLimbs, Bignum.toNat_lor, toNat_limbs, toNat_limbs]
  cases x with
  | small a => cases y with
    | small b => simp [lor, toNat, UInt64.toNat_or]
    | large b hb => exact hgen _ _
  | large a ha => exact hgen _ _

@[simp] public theorem toNat_xor (x y : BigNat) : (xor x y).toNat = x.toNat ^^^ y.toNat := by
  have hgen : ∀ x y : BigNat, (ofLimbs (Bignum.xor x.limbs y.limbs) (isTrimmed_xor _ _)).toNat =
      x.toNat ^^^ y.toNat := fun x y => by
    rw [toNat_ofLimbs, Bignum.toNat_xor, toNat_limbs, toNat_limbs]
  cases x with
  | small a => cases y with
    | small b => simp [xor, toNat, UInt64.toNat_xor]
    | large b hb => exact hgen _ _
  | large a ha => exact hgen _ _

/-- `⌊log₂ x⌋`, and `0` for `0`, like `Nat.log2`: from the top limb. -/
public def log2 : BigNat → Nat
  | small a => a.toNat.log2
  | large a _ => 32 * (a.size - 1) + (a.getD (a.size - 1) 0).toNat.log2

@[simp] public theorem log2_eq (x : BigNat) : x.log2 = x.toNat.log2 := by
  cases x with
  | small a => rfl
  | large a ha =>
    simp only [log2, toNat]
    have hpos : 0 < a.size := by
      rcases Nat.eq_zero_or_pos a.size with h | h
      · have := ha.2
        rw [toNat_of_size_eq_zero (by simpa using h)] at this
        omega
      · exact h
    -- `a = L + β^(n - 1) t` with `L < β^(n - 1)` and `t ≠ 0` the top limb.
    have hsplit := toNat_slice_add_toNat_slice a (a.size - 1) (by simp)
    have hL := toNat_lt (a.toSlice.slice 0 (a.size - 1))
    have htop : Bignum.toNat (a.toSlice.slice (a.size - 1) a.toSlice.size) =
        (a.getD (a.size - 1) 0).toNat := by
      rw [toNat_of_size_eq_one (by simp; omega)]
      simp [UInt32Array.getD_eq_getD_getElem?, show a.size - 1 < a.size by omega]
    have ht : (a.getD (a.size - 1) 0).toNat ≠ 0 := by
      have := ha.1
      rw [isTrimmed_iff, IsTrimmed, List.getLast?_eq_getElem?] at this
      simp only [UInt32Array.length_toList] at this
      rw [List.getElem?_eq_getElem (by simp; omega)] at this
      intro h0
      apply this
      simp only [UInt32Array.getElem_toList]
      congr 1
      apply UInt32.toNat_inj.1
      rw [UInt32.toNat_zero, ← h0]
      simp [UInt32Array.getD_eq_getD_getElem?, show a.size - 1 < a.size by omega]
    simp only [UInt32Array.Slice.size_slice, UInt32Array.size_toSlice] at hL
    rw [show min (a.size - 1) (min a.size a.size - 0) - 0 = a.size - 1 by omega] at hL
    rw [htop] at hsplit
    have hlo := Nat.log2_self_le ht
    have hhi := @Nat.lt_log2_self (a.getD (a.size - 1) 0).toNat
    generalize (a.getD (a.size - 1) 0).toNat = t at *
    symm
    rw [Nat.log2_eq_iff (by omega)]
    have hP : 2 ^ (32 * (a.size - 1) + t.log2) = 2 ^ (32 * (a.size - 1)) * 2 ^ t.log2 :=
      Nat.pow_add _ _ _
    have hP1 : 2 ^ (32 * (a.size - 1) + t.log2 + 1) =
        2 ^ (32 * (a.size - 1)) * 2 ^ (t.log2 + 1) := by
      rw [Nat.add_assoc, Nat.pow_add]
    constructor
    · rw [hP, ← hsplit]
      have := Nat.mul_le_mul_left (2 ^ (32 * (a.size - 1))) hlo
      omega
    · rw [hP1, ← hsplit]
      have := Nat.mul_le_mul_left (2 ^ (32 * (a.size - 1))) (Nat.succ_le_of_lt hhi)
      rw [Nat.mul_succ] at this
      omega

/-! ## Powers and square roots -/

/-- `x * x`: on words below `2³²`, with the squaring of this library above. -/
public def sqr : BigNat → BigNat
  | small a =>
    if a < 4294967296 then small (a * a)
    else ofLimbs (Bignum.sqr (limbsOfWord a)) (isTrimmed_sqr _)
  | large a _ => ofLimbs (Bignum.sqr a) (isTrimmed_sqr _)

@[simp] public theorem toNat_sqr (x : BigNat) : (sqr x).toNat = x.toNat * x.toNat := by
  cases x with
  | small a =>
    simp only [sqr]
    split
    · rename_i h
      rw [UInt64.lt_iff_toNat_lt] at h
      simp only [UInt64.reduceToNat] at h
      have : a.toNat * a.toNat < 2 ^ 64 := Nat.lt_of_lt_of_le (Nat.mul_lt_mul'' h h) (by decide)
      simp only [toNat, UInt64.toNat_mul, Nat.mod_eq_of_lt this]
    · rw [toNat_ofLimbs, Bignum.toNat_sqr, (limbsOfWord_spec a).1]
      rfl
  | large a ha =>
    simp only [sqr]
    rw [toNat_ofLimbs, Bignum.toNat_sqr]
    rfl

/-- `xⁿ`, by repeated squaring. -/
public def pow (x : BigNat) (n : Nat) : BigNat :=
  if n = 0 then small 1
  else if n % 2 = 0 then pow (sqr x) (n / 2)
  else mul x (pow (sqr x) (n / 2))
termination_by n
decreasing_by all_goals omega

@[simp] public theorem toNat_pow (x : BigNat) (n : Nat) : (pow x n).toNat = x.toNat ^ n := by
  induction n using Nat.strongRecOn generalizing x with
  | ind n ih =>
    rw [pow]
    split
    · rename_i h; subst h; rfl
    · rename_i h0
      have hn := Nat.div_add_mod n 2
      split
      · rename_i h
        rw [ih _ (by omega), toNat_sqr, ← Nat.pow_two, ← Nat.pow_mul]
        congr 1
        omega
      · rename_i h
        rw [toNat_mul, ih _ (by omega), toNat_sqr, ← Nat.pow_two, ← Nat.pow_mul, ← Nat.pow_succ']
        congr 1
        omega

/--
Steps down from `x ≥ ⌊√n⌋` to `⌊√n⌋`, while `x² > n`, with `sq = x²`: `(x - 1)² = x² - 2 x + 1`
needs no product. The guard also checks what the termination needs, which always holds.
-/
def sqrtFix (n x sq : BigNat) : BigNat :=
  if _h : blt n sq = true ∧ blt (small 0) x = true then
    sqrtFix n (sub x (small 1)) (sub (add sq (small 1)) (shiftLeft x 1))
  else x
termination_by x.toNat
decreasing_by
  rw [blt_iff, blt_iff, toNat_small] at _h
  rw [toNat_sub, toNat_small]
  simp only [UInt64.toNat_zero, UInt64.toNat_one] at *
  omega

/-- `⌊√N⌋` is the `r` with `r² ≤ N < (r + 1)²`. -/
private theorem eq_sqrt {r N : Nat} (h₁ : r * r ≤ N) (h₂ : N < (r + 1) * (r + 1)) :
    r = Nat.sqrt N := by
  have s₁ := Nat.sqrt_le N
  have s₂ := Nat.lt_succ_sqrt N
  rcases Nat.lt_trichotomy r (Nat.sqrt N) with h | h | h
  · have := Nat.mul_self_le_mul_self (show r + 1 ≤ Nat.sqrt N by omega)
    omega
  · exact h
  · have := Nat.mul_self_le_mul_self (show Nat.sqrt N + 1 ≤ r by omega)
    simp only [Nat.succ_eq_add_one] at s₂
    omega

/-- One step of Newton's iteration stays at or above `s` when `s² ≤ N`, by AM-GM. -/
private theorem le_newton {x s N : Nat} (hx : 0 < x) (hs : s * s ≤ N) :
    s ≤ (x + N / x) / 2 := by
  refine Nat.le_of_not_lt fun hlt => ?_
  have hN : N < x * (N / x + 1) := Nat.lt_mul_div_succ N hx
  generalize N / x = q at *
  have h2 : x + q + 1 ≤ 2 * s := by omega
  have h3 := Nat.mul_self_le_mul_self h2
  -- `4 x (q + 1) ≤ (x + q + 1)²`, since their difference is a square.
  have h4 : 4 * (x * (q + 1)) ≤ (x + q + 1) * (x + q + 1) := by
    have e : ((x : Int) + q + 1) * ((x : Int) + q + 1) - 4 * ((x : Int) * (q + 1)) =
        ((x : Int) - (q + 1)) * ((x : Int) - (q + 1)) := by grind
    have hsq : 0 ≤ ((x : Int) - (q + 1)) * ((x : Int) - (q + 1)) := by
      rcases Int.le_total 0 ((x : Int) - (q + 1)) with h | h
      · exact Int.mul_nonneg h h
      · exact Int.mul_nonneg_of_nonpos_of_nonpos h h
    have h : ((4 * (x * (q + 1)) : Nat) : Int) ≤ (((x + q + 1) * (x + q + 1) : Nat) : Int) := by
      push_cast; omega
    exact_mod_cast h
  have : 2 * s * (2 * s) = 4 * (s * s) := by rw [Nat.mul_mul_mul_comm]
  omega

private theorem toNat_sqrtFix (n x sq : BigNat) (hsq : sq.toNat = x.toNat * x.toNat)
    (hx : n.toNat < (x.toNat + 1) * (x.toNat + 1)) :
    (sqrtFix n x sq).toNat = Nat.sqrt n.toNat := by
  induction x, sq using sqrtFix.induct n with
  | case1 x sq h ih =>
    rw [sqrtFix, dite_eq_left h]
    rw [blt_iff, blt_iff, toNat_small, UInt64.toNat_zero] at h
    obtain ⟨h₁, h₂⟩ := h
    apply ih
    · rw [toNat_sub, toNat_add, toNat_sub, toNat_shiftLeft, toNat_small, UInt64.toNat_one, hsq,
        Nat.pow_one]
      -- `(x - 1)² = x² + 1 - 2 x` for `x ≥ 1`.
      generalize x.toNat = X at h₂ ⊢
      obtain ⟨y, rfl⟩ : ∃ y, X = y + 1 := ⟨X - 1, by omega⟩
      simp only [Nat.add_sub_cancel, Nat.add_mul, Nat.mul_add, Nat.mul_one, Nat.one_mul]
      omega
    · rw [toNat_sub, toNat_small, UInt64.toNat_one, Nat.sub_add_cancel (by omega)]
      rw [hsq] at h₁
      exact h₁
  | case2 x sq h =>
    rw [sqrtFix, dite_eq_right h]
    rw [blt_iff, blt_iff, toNat_small, UInt64.toNat_zero] at h
    -- The loop stopped: `x² ≤ n`, or `x = 0` and then `n < 1`.
    refine eq_sqrt ?_ hx
    rw [hsq] at h
    rcases Nat.eq_zero_or_pos x.toNat with h0 | h0
    · rw [h0]; omega
    · omega

/--
`⌊√n⌋`: from `Nat.sqrt` on words, and above by Newton's iteration at growing precision: the root
`s` of the top half `n / 4ᵏ`, for `k` about a quarter of the bits of `n`, gives the start
`(s + 1) 2ᵏ` above `√n` and within `2ᵏ` of it. One Newton step from there is at least `⌊√n⌋`, by
AM-GM, and at most two above it; `sqrtFix` steps down to `⌊√n⌋` with one square, where checking
the step with a second division would cost more.
-/
public def sqrt (n : BigNat) : BigNat :=
  match hn : n with
  | small a => small (Nat.sqrt a.toNat).toUInt64
  | large _ ha =>
    let k := log2 n / 4 + 1
    let x₀ := shiftLeft (add (sqrt (shiftRight n (2 * k))) (small 1)) k
    let x₁ := shiftRight (add x₀ (div n x₀)) 1
    sqrtFix n x₁ (sqr x₁)
termination_by n.toNat
decreasing_by
  rw [toNat_shiftRight]
  have hpos : 0 < n.toNat := by rw [hn]; simp only [toNat]; omega
  rw [← hn]
  apply Nat.div_lt_self hpos
  apply Nat.one_lt_two_pow
  omega

@[simp] public theorem toNat_sqrt (n : BigNat) : (sqrt n).toNat = Nat.sqrt n.toNat := by
  induction n using sqrt.induct with
  | case1 a =>
    rw [sqrt]
    have ha := a.toNat_lt
    have hs : Nat.sqrt a.toNat < 2 ^ 64 := by
      have := Nat.sqrt_le a.toNat
      have := Nat.le_mul_self (Nat.sqrt a.toNat)
      omega
    simp only [toNat, Nat.toUInt64, UInt64.toNat_ofNat', Nat.mod_eq_of_lt hs]
  | case2 a ha k ih =>
    rw [sqrt]
    have hx₀ :
        0 < (shiftLeft (add (sqrt (shiftRight (large a ha) (2 * k))) (small 1)) k).toNat := by
      rw [toNat_shiftLeft, toNat_add, toNat_small, UInt64.toNat_one]
      exact Nat.mul_pos (by omega) (Nat.two_pow_pos _)
    -- One Newton step stays at or above the root.
    have hge := le_newton hx₀ (Nat.sqrt_le (large a ha).toNat)
    apply toNat_sqrtFix _ _ _ (toNat_sqr _)
    rw [toNat_shiftRight, toNat_add, toNat_div, Nat.pow_one]
    exact Nat.lt_of_lt_of_le (Nat.lt_succ_sqrt _) (Nat.mul_self_le_mul_self (Nat.succ_le_succ hge))

/-! ## Instances -/

/-! ## Decimal strings -/

/--
The decimal digits, like `Nat.repr`. A word that fits in a `USize` goes to the runtime's
`USize.repr` directly, without a `Nat` above `2⁶³`, which would be a GMP number.
-/
public def repr : BigNat → String
  | small n => if n.toUSize.toUInt64 = n then n.toUSize.repr else Nat.repr n.toNat
  | large a h => toDecimal a h.1

private theorem usize_repr (n : USize) : n.repr = Nat.repr n.toNat := by
  unfold USize.repr
  rfl

public theorem repr_eq (x : BigNat) : x.repr = Nat.repr x.toNat := by
  cases x with
  | small n =>
    show (if n.toUSize.toUInt64 = n then n.toUSize.repr else Nat.repr n.toNat) = Nat.repr n.toNat
    by_cases h : n.toUSize.toUInt64 = n
    · have := congrArg UInt64.toNat h
      rw [USize.toNat_toUInt64] at this
      rw [ite_eq_left h, usize_repr, this]
    · rw [ite_eq_right h]
  | large a h => exact toDecimal_eq a h.1

/-- The number that a string of decimal digits denotes, like `String.toNat?`. -/
public def ofString? (s : String) : Option BigNat :=
  if s.isNat then
    some (ofLimbs (trim (s.foldl DecimalState.step .init).finish) (isTrimmed_trim _))
  else
    none

public theorem ofString?_eq (s : String) : ofString? s = s.toNat?.map ofNat := by
  by_cases h : s.isNat = true
  · rw [ofString?, ite_eq_left h, String.toNat?_eq_some_ofDigitChars h, Option.map_some,
      Option.some.injEq, ← toNat_inj, toNat_ofLimbs, toNat_ofNat, toNat_trim,
      String.foldl_eq_foldl_toList]
    exact toNat_finish_foldl _ (String.isNat_iff.1 h).2.1
  · rw [ofString?, ite_eq_right h, String.toNat?_eq_none (by simpa using h), Option.map_none]

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
public instance : HShiftLeft BigNat Nat BigNat := ⟨shiftLeft⟩
public instance : HShiftRight BigNat Nat BigNat := ⟨shiftRight⟩
public instance : AndOp BigNat := ⟨land⟩
public instance : OrOp BigNat := ⟨lor⟩
public instance : XorOp BigNat := ⟨xor⟩
public instance : Pow BigNat Nat := ⟨pow⟩
public instance (n : Nat) : OfNat BigNat n := ⟨ofNat n⟩
public instance : Inhabited BigNat := ⟨small 0⟩
public instance : Hashable BigNat where
  hash
    | small n => hash n
    | large a _ => hash a
public instance : ToString BigNat := ⟨BigNat.repr⟩
public instance : Repr BigNat := ⟨fun x _ => x.repr⟩

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

/-! ## Greatest common divisor -/

/-- Euclid's algorithm on words. -/
def wordGcd (a b : UInt64) : UInt64 :=
  if _h : b = 0 then a else wordGcd b (a % b)
termination_by b.toNat
decreasing_by
  have : b.toNat ≠ 0 := fun h' => _h (UInt64.toNat_inj.1 (by simpa using h'))
  rw [UInt64.toNat_mod]
  exact Nat.mod_lt _ (by omega)

private theorem toNat_wordGcd (a b : UInt64) : (wordGcd a b).toNat = Nat.gcd a.toNat b.toNat := by
  induction a, b using wordGcd.induct with
  | case1 a => rw [wordGcd]; simp
  | case2 a b h ih =>
    rw [wordGcd, dite_eq_right h, ih, UInt64.toNat_mod, Nat.gcd_comm a.toNat b.toNat,
      Nat.gcd_rec b.toNat a.toNat, Nat.gcd_comm]

/-- A matrix of determinant `±1` keeps the greatest common divisor. -/
private theorem gcd_unimodular (a b : Nat) (A B C D : Int)
    (h : A * D - B * C = 1 ∨ A * D - B * C = -1) :
    Nat.gcd (A * a + B * b).natAbs (C * a + D * b).natAbs = Nat.gcd a b := by
  apply Nat.dvd_antisymm
  · -- The gcd of the combinations divides `a` and `b`, which the inverse matrix recovers.
    have hx : (Nat.gcd (A * a + B * b).natAbs (C * a + D * b).natAbs : Int) ∣ A * a + B * b :=
      Int.ofNat_dvd_left.2 (Nat.gcd_dvd_left _ _)
    have hy : (Nat.gcd (A * a + B * b).natAbs (C * a + D * b).natAbs : Int) ∣ C * a + D * b :=
      Int.ofNat_dvd_left.2 (Nat.gcd_dvd_right _ _)
    have ha : D * (A * a + B * b) - B * (C * a + D * b) = (A * D - B * C) * a := by grind
    have hb : A * (C * a + D * b) - C * (A * a + B * b) = (A * D - B * C) * b := by grind
    have hda := Int.dvd_sub (Int.dvd_trans hx (Int.dvd_mul_left D _))
      (Int.dvd_trans hy (Int.dvd_mul_left B _))
    have hdb := Int.dvd_sub (Int.dvd_trans hy (Int.dvd_mul_left A _))
      (Int.dvd_trans hx (Int.dvd_mul_left C _))
    rw [ha] at hda
    rw [hb] at hdb
    refine Nat.dvd_gcd ?_ ?_
    · rcases h with h | h <;> rw [h] at hda <;> simp at hda <;> exact Int.natCast_dvd_natCast.1 hda
    · rcases h with h | h <;> rw [h] at hdb <;> simp at hdb <;> exact Int.natCast_dvd_natCast.1 hdb
  · have ga : (Nat.gcd a b : Int) ∣ (a : Int) := Int.natCast_dvd_natCast.2 (Nat.gcd_dvd_left a b)
    have gb : (Nat.gcd a b : Int) ∣ (b : Int) := Int.natCast_dvd_natCast.2 (Nat.gcd_dvd_right a b)
    refine Nat.dvd_gcd ?_ ?_
    · exact Int.ofNat_dvd_left.1 (Int.dvd_add (Int.dvd_trans ga (Int.dvd_mul_left A _))
        (Int.dvd_trans gb (Int.dvd_mul_left B _)))
    · exact Int.ofNat_dvd_left.1 (Int.dvd_add (Int.dvd_trans ga (Int.dvd_mul_left C _))
        (Int.dvd_trans gb (Int.dvd_mul_left D _)))

/-- The cofactors of a run of Lehmer's steps, as one object with unboxed fields. -/
structure Cofactors where
  A : Int64
  B : Int64
  C : Int64
  D : Int64

/--
Euclid's algorithm on the leading words `x ≥ y` of two numbers, with the cofactors `A`, `B`, `C`,
`D` of the steps so far, like GMP's `hgcd2` on one word: it stops when the remainder falls below
`2³¹`, half the bits of the words, which keeps the cofactors below `2³¹`, as `mulSubMul` needs, or
when Jebelean's condition fails, which makes the quotients those of the full numbers. A quotient of
`1`, the most common, costs a comparison rather than a division. It computes in `Int64`, since `Int`
boxes values from `2³¹`; nothing is proved about it, since `lehmerStep` checks the cofactors it
returns and `gcd` takes a step of Euclid's algorithm when they do not apply.
-/
def lehmerSteps (x y A B C D : Int64) : Nat → Cofactors
  | 0 => ⟨A, B, C, D⟩
  | f + 1 =>
    if y < 0x80000000 then ⟨A, B, C, D⟩
    else
      let q : Int64 := if x < y + y then 1 else x / y
      let r := x - q * y
      let C' := A - q * C
      let D' := B - q * D
      -- Jebelean's condition: the quotient is that of the full numbers when the remainder and
      -- the difference of the remainders exceed the cofactors and their differences.
      if r < C'.abs ∨ r < D'.abs ∨ y - r < (C' - C).abs ∨ y - r < (D' - D).abs ∨
          0x80000000 ≤ C'.abs ∨ 0x80000000 ≤ D'.abs then
        ⟨A, B, C, D⟩
      else lehmerSteps y r C D C' D' f

/--
The numbers `|A x + B y|` and `|C x + D y|` of a step of Lehmer's algorithm with the cofactors
`A`, `B`, `C`, `D`, when the step is valid: the cofactors are below `2³¹`, their determinant is
`±1`, their signs alternate as in Euclid's algorithm, and both numbers are nonnegative. Each
number is a difference of two multiples, from `mulSubMul` in one pass, and the determinant is
checked on `Nat`, where its products fit in a word.
-/
def lehmerStep (x y : BigNat) (A B C D : Int) : Option (BigNat × BigNat) :=
  let a := A.natAbs
  let b := B.natAbs
  let c := C.natAbs
  let d := D.natAbs
  if a < 2 ^ 31 ∧ b < 2 ^ 31 ∧ c < 2 ^ 31 ∧ d < 2 ^ 31 ∧ (a * d = b * c + 1 ∨ b * c = a * d + 1)
  then
    if 0 ≤ A ∧ B ≤ 0 ∧ C ≤ 0 ∧ 0 ≤ D then
      let u := mulSubMul x.limbs y.limbs a.toUInt32 b.toUInt32
      let v := mulSubMul y.limbs x.limbs d.toUInt32 c.toUInt32
      if u.2 = false ∧ v.2 = false then
        some (ofLimbs (trim u.1) (isTrimmed_trim _), ofLimbs (trim v.1) (isTrimmed_trim _))
      else none
    else if A ≤ 0 ∧ 0 ≤ B ∧ 0 ≤ C ∧ D ≤ 0 then
      let u := mulSubMul y.limbs x.limbs b.toUInt32 a.toUInt32
      let v := mulSubMul x.limbs y.limbs c.toUInt32 d.toUInt32
      if u.2 = false ∧ v.2 = false then
        some (ofLimbs (trim u.1) (isTrimmed_trim _), ofLimbs (trim v.1) (isTrimmed_trim _))
      else none
    else none
  else none

/-- `p X - q Y` from `mulSubMul`, when it is not negative, as `|P X + Q Y|`. -/
private theorem toNat_mulSubMul_natAbs (X Y : UInt32Array) (p q : Nat) (P Q : Int)
    (hp : p < 2 ^ 31) (hq : q < 2 ^ 31) (hP : P = p) (hQ : Q = -(q : Int))
    (hn : (mulSubMul X Y p.toUInt32 q.toUInt32).2 = false) :
    Bignum.toNat (trim (mulSubMul X Y p.toUInt32 q.toUInt32).1) =
      (P * Bignum.toNat X + Q * Bignum.toNat Y).natAbs := by
  have hpu : p.toUInt32.toNat = p := by simp [Nat.toUInt32_eq, UInt32.toNat_ofNat']; omega
  have hqu : q.toUInt32.toNat = q := by simp [Nat.toUInt32_eq, UInt32.toNat_ofNat']; omega
  have h := (mulSubMul_spec X Y p.toUInt32 q.toUInt32 (by omega) (by omega)).1 hn
  rw [hpu, hqu] at h
  rw [toNat_trim, hP, hQ]
  generalize Bignum.toNat (mulSubMul X Y p.toUInt32 q.toUInt32).1 = R at *
  generalize Bignum.toNat X = Xv at *
  generalize Bignum.toNat Y = Yv at *
  have : (p : Int) * Xv + -(q : Int) * Yv = (R : Int) := by
    have h' : ((R + Yv * q : Nat) : Int) = ((Xv * p : Nat) : Int) := by rw [h]
    push_cast at h'
    rw [Int.neg_mul]
    rw [Int.mul_comm (p : Int), Int.mul_comm (q : Int)]
    omega
  rw [this, Int.natAbs_natCast]

/-- A valid step of Lehmer's algorithm keeps the greatest common divisor. -/
private theorem lehmerStep_gcd (x y : BigNat) (A B C D : Int) (p : BigNat × BigNat)
    (h : lehmerStep x y A B C D = some p) :
    Nat.gcd p.1.toNat p.2.toNat = Nat.gcd x.toNat y.toNat := by
  unfold lehmerStep at h
  simp only at h
  split at h
  · rename_i hc
    obtain ⟨ha, hb, hc', hd, hdet⟩ := hc
    -- The determinant `A D - B C = |A||D| - |B||C|` in either sign pattern.
    have hdet' (hAD : A * D = (A.natAbs * D.natAbs : Nat))
        (hBC : B * C = (B.natAbs * C.natAbs : Nat)) : A * D - B * C = 1 ∨ A * D - B * C = -1 := by
      rw [hAD, hBC]
      rcases hdet with e | e
      · left; rw [e]; push_cast; omega
      · right; rw [e]; push_cast; omega
    split at h
    · rename_i hs
      obtain ⟨hA, hB, hC, hD⟩ := hs
      split at h
      · rename_i hn
        obtain ⟨hu, hv⟩ := hn
        rw [Option.some.injEq] at h
        subst h
        simp only [toNat_ofLimbs]
        have hA' : A = (A.natAbs : Int) := (Int.natAbs_of_nonneg hA).symm
        have hD' : D = (D.natAbs : Int) := (Int.natAbs_of_nonneg hD).symm
        have hB' : B = -(B.natAbs : Int) := by rw [Int.ofNat_natAbs_of_nonpos hB, Int.neg_neg]
        have hC' : C = -(C.natAbs : Int) := by rw [Int.ofNat_natAbs_of_nonpos hC, Int.neg_neg]
        rw [toNat_mulSubMul_natAbs _ _ _ _ A B ha hb hA' hB' hu,
          toNat_mulSubMul_natAbs _ _ _ _ D C hd hc' hD' hC' hv, toNat_limbs, toNat_limbs,
          Int.add_comm (D * _)]
        exact gcd_unimodular _ _ A B C D (hdet' (by rw [hA', hD']; simp)
          (by rw [hB', hC']; simp [Int.neg_mul_neg]))
      · exact absurd h (by simp)
    · split at h
      · rename_i _ hs
        obtain ⟨hA, hB, hC, hD⟩ := hs
        split at h
        · rename_i hn
          obtain ⟨hu, hv⟩ := hn
          rw [Option.some.injEq] at h
          subst h
          simp only [toNat_ofLimbs]
          have hB' : B = (B.natAbs : Int) := (Int.natAbs_of_nonneg hB).symm
          have hC' : C = (C.natAbs : Int) := (Int.natAbs_of_nonneg hC).symm
          have hA' : A = -(A.natAbs : Int) := by rw [Int.ofNat_natAbs_of_nonpos hA, Int.neg_neg]
          have hD' : D = -(D.natAbs : Int) := by rw [Int.ofNat_natAbs_of_nonpos hD, Int.neg_neg]
          rw [toNat_mulSubMul_natAbs _ _ _ _ B A hb ha hB' hA' hu,
            toNat_mulSubMul_natAbs _ _ _ _ C D hc' hd hC' hD' hv, toNat_limbs, toNat_limbs,
            Int.add_comm (B * _)]
          exact gcd_unimodular _ _ A B C D
            (hdet' (by rw [hA', hD']; simp [Int.neg_mul_neg]) (by rw [hB', hC']; simp))
        · exact absurd h (by simp)
      · exact absurd h (by simp)
  · exact absurd h (by simp)

/-- Two words, as one object with unboxed fields. -/
structure LeadWords where
  x : Int64
  y : Int64

/--
The leading 62 bits of `a`, normalized so that its top bit is set, and the bits of `b` at the same
positions, as the words of Lehmer's algorithm. Their values only affect its speed: every step on
the full numbers is checked.
-/
def leadWords (a b : UInt32Array) : LeadWords :=
  let n := a.size
  let c := (31 - (a.getD (n - 1) 0).log2).toUInt64
  let lead (t₂ t₁ t₀ : UInt32) : Int64 :=
    let w := (((t₂.toUInt64 <<< 32) ||| t₁.toUInt64) <<< c) ||| (t₀.toUInt64 >>> (32 - c))
    (w >>> 2).toInt64
  ⟨lead (a.getD (n - 1) 0) (a.getD (n - 2) 0) (a.getD (n - 3) 0),
    lead (b.getD (n - 1) 0) (b.getD (n - 2) 0) (b.getD (n - 3) 0)⟩

/--
The greatest common divisor, by Lehmer's algorithm: the cofactors of Euclid's steps on the leading
words, from `lehmerSteps`, are applied to the full numbers at once with `lehmerStep`, which keeps
the greatest common divisor since their matrix has determinant `±1`; when the step is not valid
or does not make the second number smaller, one step of Euclid's algorithm is taken instead. On
words when both are small.
-/
public def gcd (x y : BigNat) : BigNat :=
  match x, y with
  | small a, small b => small (wordGcd a b)
  | x, y =>
    if _h : y = small 0 then x
    else if blt x y then gcd y (mod x y)
    else
      let w := leadWords x.limbs y.limbs
      let m := lehmerSteps w.x w.y 1 0 0 1 100
      match lehmerStep x y m.A.toInt m.B.toInt m.C.toInt m.D.toInt with
      | some p => if _hy : blt p.2 y then gcd p.1 p.2 else gcd y (mod x y)
      | none => gcd y (mod x y)
termination_by y.toNat
decreasing_by
  all_goals first
    | (rw [blt_iff] at _hy; exact _hy)
    | (have : y.toNat ≠ 0 := fun h' => _h (toNat_inj.1 (by rw [h']; rfl))
       rw [toNat_mod]
       exact Nat.mod_lt _ (by omega))

/-- One step of Euclid's algorithm keeps the greatest common divisor. -/
private theorem gcd_mod_step (x y : BigNat) :
    Nat.gcd y.toNat (mod x y).toNat = Nat.gcd x.toNat y.toNat := by
  rw [toNat_mod, Nat.gcd_comm x.toNat y.toNat, Nat.gcd_rec y.toNat x.toNat, Nat.gcd_comm]

@[simp] public theorem toNat_gcd (x y : BigNat) : (gcd x y).toNat = Nat.gcd x.toNat y.toNat := by
  induction x, y using gcd.induct with
  | case1 a b => rw [gcd]; exact toNat_wordGcd a b
  | case2 x hxy =>
    rw [gcd]
    · simp only [↓reduceDIte, toNat_small, UInt64.toNat_zero, Nat.gcd_zero_right]
    · exact hxy
  | case3 x y hxy h hlt ih =>
    rw [gcd]
    · rw [dite_eq_right h, ite_eq_left hlt, ih, gcd_mod_step]
    · exact hxy
  | case4 x y hxy h hlt w m p hp hy ih =>
    rw [gcd]
    · rw [dite_eq_right h, ite_eq_right hlt]
      simp only [w, m] at hp
      simp only [hp, dite_eq_left hy, ih, lehmerStep_gcd _ _ _ _ _ _ _ hp]
    · exact hxy
  | case5 x y hxy h hlt w m p hp hy ih =>
    rw [gcd]
    · rw [dite_eq_right h, ite_eq_right hlt]
      simp only [w, m] at hp
      simp only [hp, dite_eq_right hy, ih, gcd_mod_step]
    · exact hxy
  | case6 x y hxy h hlt w m hp ih =>
    rw [gcd]
    · rw [dite_eq_right h, ite_eq_right hlt]
      simp only [w, m] at hp
      simp only [hp, ih, gcd_mod_step]
    · exact hxy

/-- The least common multiple, `x / gcd x y * y`, and `0` when either is `0`. -/
public def lcm (x y : BigNat) : BigNat :=
  if gcd x y = small 0 then small 0 else div x (gcd x y) * y

@[simp] public theorem toNat_lcm (x y : BigNat) : (lcm x y).toNat = Nat.lcm x.toNat y.toNat := by
  unfold lcm
  split
  · rename_i h
    have h' := congrArg toNat h
    rw [toNat_gcd, toNat_small, UInt64.toNat_zero, Nat.gcd_eq_zero_iff] at h'
    rw [toNat_small, UInt64.toNat_zero, h'.1, Nat.lcm_zero_left]
  · show (mul (div x (gcd x y)) y).toNat = _
    rw [toNat_mul, toNat_div, toNat_gcd, Nat.lcm, Nat.div_mul_right_comm (Nat.gcd_dvd_left _ _)]

end BigNat

end Bignum
