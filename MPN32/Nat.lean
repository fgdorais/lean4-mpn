/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import MPN32.Add
public import MPN32.Sub
public import MPN32.Cmp
public import MPN32.Mul
public import MPN32.Sqr
public import MPN32.Div
public import MPN32.Bits
public import MPN32.Decimal
public import MPN32.Arch.LinComb
public import MPN.WordGcd
public import MPN.NatGcd
public import MPN.LehmerStep
public import MPN.Generic.HGCD
public import MPN.Generic.Radix
public import MPN.Generic.Sqrt
public import MPN.Natural
public import MPN.Bridge
public import MPN.WordSqrt
import Std.Data.String.ToNat
import all Init.Data.Repr

/-!
# Natural numbers

`MPN.Nat` is `main`'s `GNat` on arrays of 32-bit limbs: a natural number as a machine word below
`2⁶⁴` and as trimmed limbs above, with every operation proved correct against `Nat`. The instance
`natLimbs32` of `NatLimbs` gives it this library's operations on trimmed limbs, with a fast path
for the division of up to four limbs by a word (`divRem128`). The square root by Zimmermann's
recursion is defined here on `MPN.Nat`. The greatest common divisor is `main`'s `GNat.gcd` on the
instance `gcdLimbs32` of `GcdLimbs`, with Lehmer's step and half-gcd's base case on 32-bit limbs
from here.
-/


open ScalarArray

namespace MPN.W32

/-! ## Limbs and words -/

/-- A trimmed array of limbs is at least `β ^ (n - 1)` for `n` limbs. -/
public theorem pow_le_toNat_of_isTrimmed {a : UInt32Array} (h : isTrimmed a = true)
    (hpos : 0 < a.size) : 2 ^ (32 * (a.size - 1)) ≤ toNat a := by
  refine Nat.le_of_not_lt fun hlt => ?_
  rw [toNat_array_eq_valAt] at hlt
  exact getElem_top_ne_zero h hpos (UInt32Array.getElem_eq_zero_of_valAt_lt a (by lia) hlt)

/-- The limbs of a word: none for `0`, one below `2³²`, two otherwise. -/
public def limbsOfWord (n : UInt64) : UInt32Array :=
  if n = 0 then
    .empty
  else if n < 4294967296 then
    (UInt32Array.emptyWithCapacity 1).push n.toUInt32
  else
    ((UInt32Array.emptyWithCapacity 2).push n.toUInt32).push (n >>> 32).toUInt32

public theorem limbsOfWord_spec (n : UInt64) :
    toNat (limbsOfWord n) = n.toNat ∧ isTrimmed (limbsOfWord n) = true := by
  have hn := n.toNat_lt
  by_cases h : n = 0
  · have heq : limbsOfWord n = .empty := by rw [limbsOfWord, ite_eq_left h]
    rw [heq, h]
    exact ⟨toNat_empty, isTrimmed_empty⟩
  · have h0 : n.toNat ≠ 0 := fun h'' => h (UInt64.toNat_inj.1 (by simpa using h''))
    by_cases h' : n < 4294967296
    · have heq : limbsOfWord n = (UInt32Array.emptyWithCapacity 1).push n.toUInt32 := by
        rw [limbsOfWord, ite_eq_right h, ite_eq_left h']
      have h' : n.toNat < 2 ^ 32 := by simpa [UInt64.lt_iff_toNat_lt] using h'
      have hx : n.toUInt32 ≠ 0 := fun h'' => by
        have := congrArg UInt32.toNat h''
        simp only [UInt64.toNat_toUInt32, UInt32.toNat_zero] at this
        lia
      rw [heq]
      refine ⟨?_, isTrimmed_push _ hx⟩
      rw [toNat_push, UInt32Array.emptyWithCapacity_eq_empty, toNat_empty]
      simp only [UInt32Array.size_empty, Nat.mul_zero, Nat.pow_zero, Nat.one_mul, Nat.zero_add,
        UInt64.toNat_toUInt32]
      lia
    · have heq : limbsOfWord n =
          ((UInt32Array.emptyWithCapacity 2).push n.toUInt32).push (n >>> 32).toUInt32 := by
        rw [limbsOfWord, ite_eq_right h, ite_eq_right h']
      have h' : 2 ^ 32 ≤ n.toNat := by simpa [UInt64.lt_iff_toNat_lt] using h'
      have hhi : (n >>> 32).toNat = n.toNat / 2 ^ 32 := by
        simp [UInt64.toNat_shiftRight, Nat.shiftRight_eq_div_pow]
      have hx : (n >>> 32).toUInt32 ≠ 0 := fun h'' => by
        have := congrArg UInt32.toNat h''
        simp only [UInt64.toNat_toUInt32, UInt32.toNat_zero, hhi] at this
        lia
      rw [heq]
      refine ⟨?_, isTrimmed_push _ hx⟩
      rw [toNat_push, toNat_push, UInt32Array.emptyWithCapacity_eq_empty, toNat_empty]
      simp only [UInt32Array.size_empty, UInt32Array.size_push, Nat.mul_zero, Nat.pow_zero,
        Nat.one_mul, Nat.zero_add, UInt64.toNat_toUInt32, hhi]
      have : n.toNat / 2 ^ 32 < 2 ^ 32 := by lia
      rw [Nat.mod_eq_of_lt this]
      lia

/-- The word of an array of at most two limbs. -/
public def wordOfLimbs (a : UInt32Array) : UInt64 :=
  (a.getD 0 0).toUInt64 + ((a.getD 1 0).toUInt64 <<< 32)

public theorem toNat_wordOfLimbs (a : UInt32Array) (h : a.size ≤ 2) :
    (wordOfLimbs a).toNat = toNat a := by
  have h₀ := (a.getD 0 0).toNat_lt
  have h₁ := (a.getD 1 0).toNat_lt
  have hw : (wordOfLimbs a).toNat = (a.getD 0 0).toNat + (a.getD 1 0).toNat * 2 ^ 32 := by
    simp only [wordOfLimbs, UInt64.toNat_add, UInt64.toNat_shiftLeft, UInt32.toNat_toUInt64,
      UInt64.reduceToNat, Nat.reduceMod, Nat.shiftLeft_eq]
    rw [Nat.mod_eq_of_lt (by lia), Nat.mod_eq_of_lt (by lia)]
  rw [hw, toNat_array_eq_valAt,
    ← UInt32Array.valAt_extend a (lo := 0) (m := a.size) 2 (by lia) h]
  simp only [UInt32Array.valAt_succ, UInt32Array.valAt_zero, UInt32Array.getD_zero_eq_getElem!]
  lia

namespace Nat

/-! ## Results of two words -/

/-- The three or four limbs of `lo + 2⁶⁴ hi`, for `hi ≠ 0`. -/
public def limbs4 (lo hi : UInt64) : UInt32Array :=
  let r := (((UInt32Array.emptyWithCapacity 4).push lo.toUInt32).push (lo >>> 32).toUInt32).push
    hi.toUInt32
  if hi < 4294967296 then r else r.push (hi >>> 32).toUInt32

public theorem limbs4_spec (lo hi : UInt64) (h : hi ≠ 0) :
    isTrimmed (limbs4 lo hi) = true ∧
      MPN.W32.toNat (limbs4 lo hi) = lo.toNat + 2 ^ 64 * hi.toNat := by
  have hl := lo.toNat_lt
  have hh := hi.toNat_lt
  have h0 : hi.toNat ≠ 0 := fun e => h (UInt64.toNat_inj.1 (by simpa using e))
  have hsz : 2 ^ (32 * (((UInt32Array.emptyWithCapacity 4).push lo.toUInt32).push
      (lo >>> 32).toUInt32).size) = 2 ^ 64 := by simp
  by_cases hs : hi < 4294967296
  · have e : limbs4 lo hi = (((UInt32Array.emptyWithCapacity 4).push lo.toUInt32).push
        (lo >>> 32).toUInt32).push hi.toUInt32 := by
      simp only [limbs4, hs, ite_true]
    rw [e]
    have hs' := hs
    rw [UInt64.lt_iff_toNat_lt] at hs'
    simp only [UInt64.reduceToNat] at hs'
    refine ⟨isTrimmed_push _ ?_, ?_⟩
    · intro e
      have := congrArg UInt32.toNat e
      simp only [UInt64.toNat_toUInt32, UInt32.toNat_zero] at this
      lia
    · rw [toNat_push, hsz, toNat_push, toNat_push, UInt32Array.emptyWithCapacity_eq_empty,
        toNat_empty]
      simp only [
        UInt32Array.size_empty, UInt32Array.size_push, UInt64.toNat_toUInt32,
        UInt64.toNat_shiftRight, UInt64.reduceToNat, Nat.reduceMod, Nat.shiftRight_eq_div_pow]
      lia
  · have e : limbs4 lo hi = ((((UInt32Array.emptyWithCapacity 4).push lo.toUInt32).push
        (lo >>> 32).toUInt32).push hi.toUInt32).push (hi >>> 32).toUInt32 := by
      simp only [limbs4, hs, ite_false]
    rw [e]
    have hs' := hs
    rw [UInt64.lt_iff_toNat_lt] at hs'
    simp only [UInt64.reduceToNat] at hs'
    refine ⟨isTrimmed_push _ ?_, ?_⟩
    · intro e
      have := congrArg UInt32.toNat e
      simp only [UInt64.toNat_toUInt32, UInt64.toNat_shiftRight, UInt64.reduceToNat,
        Nat.reduceMod, Nat.shiftRight_eq_div_pow, UInt32.toNat_zero] at this
      lia
    · rw [toNat_push, toNat_push, hsz, toNat_push, toNat_push,
        UInt32Array.emptyWithCapacity_eq_empty, toNat_empty]
      simp only [
        UInt32Array.size_empty, UInt32Array.size_push, UInt64.toNat_toUInt32,
        UInt64.toNat_shiftRight, UInt64.reduceToNat, Nat.reduceMod, Nat.shiftRight_eq_div_pow]
      lia

/--
`a` divided by a nonzero word `b`, as untrimmed quotient limbs and the remainder, a word: `divRem1`
below `2³²` and `divRem2` above, without an array for `b`.
-/
public def divRemWord (a : UInt32Array) (b : UInt64) : UInt32Array × UInt64 :=
  if b < 4294967296 then
    let p := divRem1 a b.toUInt32
    (p.1, p.2.toUInt64)
  else
    divRem2 a (b >>> 32).toUInt32 b.toUInt32

public theorem divRemWord_spec (a : UInt32Array) (b : UInt64) (hb : b ≠ 0) :
    MPN.W32.toNat (divRemWord a b).1 = MPN.W32.toNat a / b.toNat ∧
      (divRemWord a b).2.toNat = MPN.W32.toNat a % b.toNat := by
  have hb' : 0 < b.toNat := by
    rcases Nat.eq_zero_or_pos b.toNat with h | h
    · exact absurd (UInt64.toNat_inj.1 (by simpa using h)) hb
    · exact h
  have hB := b.toNat_lt
  -- `q b + r = a` with `r < b` determines both.
  have key : ∀ q r : Nat, q * b.toNat + r = MPN.W32.toNat a → r < b.toNat →
      q = MPN.W32.toNat a / b.toNat ∧ r = MPN.W32.toNat a % b.toNat := fun q r h₁ h₂ => by
    have := (Nat.div_mod_unique (a := MPN.W32.toNat a) (b := b.toNat) (d := q) (c := r) hb').2
      ⟨by rw [Nat.mul_comm b.toNat q]; lia, h₂⟩
    exact ⟨this.1.symm, this.2.symm⟩
  unfold divRemWord
  by_cases hs : b < 4294967296
  · rw [ite_eq_left hs]
    rw [UInt64.lt_iff_toNat_lt] at hs
    simp only [UInt64.reduceToNat] at hs
    have hd : b.toUInt32.toNat = b.toNat := by simp; lia
    have hd0 : b.toUInt32 ≠ 0 := fun e => by
      have := congrArg UInt32.toNat e
      rw [hd, UInt32.toNat_zero] at this
      lia
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
      lia
    have hd0 : (b >>> 32).toUInt32 ≠ 0 := fun e => by
      have := congrArg UInt32.toNat e
      simp only [UInt64.toNat_toUInt32, UInt64.toNat_shiftRight, UInt64.reduceToNat,
        Nat.reduceMod, Nat.shiftRight_eq_div_pow, UInt32.toNat_zero] at this
      lia
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
@[inline] public def divRem128L (x₀ x₁ x₂ x₃ : UInt32) (b : UInt64) : UInt64 × UInt64 × UInt64 :=
  let sN := 31 - (b >>> 32).toUInt32.toNat.log2
  let s := sN.toUInt64
  let V := b <<< s
  let vt := (V >>> 32).toUInt32
  let vs := V.toUInt32
  let p₀ := shlStep s (x₀) 0
  let p₁ := shlStep s (x₁) p₀.2
  let p₂ := shlStep s (x₂) p₁.2
  let p₃ := shlStep s (x₃) p₂.2
  let t₂ := div2Step vt vs ((p₃.2.toUInt64 <<< 32) + p₃.1.toUInt64) p₂.1
  let t₁ := div2Step vt vs t₂.2 p₁.1
  let t₀ := div2Step vt vs t₁.2 p₀.1
  (t₀.1.toUInt64 + (t₁.1.toUInt64 <<< 32), t₂.1.toUInt64, t₀.2 >>> s)

/-- `divRem128L` on the four limbs of `a`. -/
public def divRem128 (a : UInt32Array) (b : UInt64) : UInt64 × UInt64 × UInt64 :=
  divRem128L (a.getD 0 0) (a.getD 1 0) (a.getD 2 0) (a.getD 3 0) b

/--
Unscaling a division: `X S = Q (b S) + r` with `r < b S` gives `X / b = Q` and `X % b = r / S`.
-/
public theorem div_of_scaled {X Q b S r : Nat} (hS : 0 < S) (h : X * S = Q * (b * S) + r)
    (hr : r < b * S) : X / b = Q ∧ X % b = r / S := by
  have hQ : Q * b ≤ X := by
    refine Nat.le_of_not_lt fun hlt => ?_
    have := Nat.mul_le_mul_right S (show X + 1 ≤ Q * b by lia)
    rw [Nat.add_mul, Nat.one_mul, Nat.mul_assoc] at this
    lia
  have hr' : r = (X - Q * b) * S := by
    rw [Nat.sub_mul, Nat.mul_assoc Q b S]
    lia
  have hrS : r / S = X - Q * b := by rw [hr', Nat.mul_div_cancel _ hS]
  have hlt : X - Q * b < b := by
    rw [hr'] at hr
    exact Nat.lt_of_mul_lt_mul_right hr
  have hb : 0 < b := by lia
  have := (Nat.div_mod_unique (a := X) (b := b) (d := Q) (c := X - Q * b) hb).2
    ⟨by rw [Nat.mul_comm b Q]; lia, hlt⟩
  exact ⟨this.1, by rw [hrS]; exact this.2⟩

/-- The value of at most four limbs. -/
public theorem toNat_four (a : UInt32Array) (ha : a.size ≤ 4) :
    MPN.W32.toNat a = (a.getD 0 0).toNat + 2 ^ 32 * (a.getD 1 0).toNat +
      2 ^ 64 * (a.getD 2 0).toNat + 2 ^ 96 * (a.getD 3 0).toNat := by
  rw [toNat_array_eq_valAt,
    ← UInt32Array.valAt_extend a (lo := 0) (m := a.size) 4 (by lia) ha]
  simp only [UInt32Array.valAt_succ, UInt32Array.valAt_zero, UInt32Array.getD_zero_eq_getElem!]
  lia

public theorem divRem128L_spec (x₀ x₁ x₂ x₃ : UInt32) (b : UInt64)
    (hb : 4294967296 ≤ b) :
    (divRem128L x₀ x₁ x₂ x₃ b).1.toNat + 2 ^ 64 * (divRem128L x₀ x₁ x₂ x₃ b).2.1.toNat =
        (x₀.toNat + 2 ^ 32 * x₁.toNat + 2 ^ 64 * x₂.toNat + 2 ^ 96 * x₃.toNat) / b.toNat ∧
      (divRem128L x₀ x₁ x₂ x₃ b).2.2.toNat =
        (x₀.toNat + 2 ^ 32 * x₁.toNat + 2 ^ 64 * x₂.toNat + 2 ^ 96 * x₃.toNat) % b.toNat := by
  rw [UInt64.le_iff_toNat_le] at hb
  simp only [UInt64.reduceToNat] at hb
  have hbβ := b.toNat_lt
  -- The normalization: `V = b 2ˢ < 2⁶⁴` with `s = 31 - log₂ d₁` for the top limb `d₁` of `b`.
  have hd₁ : (b >>> 32).toUInt32.toNat = b.toNat / 2 ^ 32 := by
    simp only [UInt64.toNat_toUInt32, UInt64.toNat_shiftRight, UInt64.reduceToNat, Nat.reduceMod,
      Nat.shiftRight_eq_div_pow]
    lia
  have hd₁0 : b.toNat / 2 ^ 32 ≠ 0 := by lia
  have hl : (b.toNat / 2 ^ 32).log2 < 32 := (Nat.log2_lt hd₁0).2 (by lia)
  have hlt := Nat.lt_log2_self (n := b.toNat / 2 ^ 32)
  have hge := Nat.log2_self_le hd₁0
  simp only [divRem128L, hd₁]
  generalize (b.toNat / 2 ^ 32).log2 = l at hl hlt hge
  have hS : 0 < 2 ^ (31 - l) := Nat.two_pow_pos _
  have hsU : (31 - l).toUInt64.toNat = 31 - l := by
    simp only [Nat.toUInt64, UInt64.toNat_ofNat']
    exact Nat.mod_eq_of_lt (by lia)
  have hV64 : b.toNat * 2 ^ (31 - l) < 2 ^ 64 := by
    have h₁ : b.toNat < 2 ^ (l + 1) * 2 ^ 32 := by
      have := Nat.mul_le_mul_right (2 ^ 32) (show b.toNat / 2 ^ 32 + 1 ≤ 2 ^ (l + 1) by lia)
      rw [Nat.succ_mul] at this
      lia
    have h₂ : 2 ^ (l + 1) * 2 ^ 32 * 2 ^ (31 - l) = 2 ^ 64 := by
      rw [← Nat.pow_add, ← Nat.pow_add]; congr 1; lia
    rw [← h₂]
    exact Nat.mul_lt_mul_of_pos_right h₁ hS
  have hV : (b <<< (31 - l).toUInt64).toNat = b.toNat * 2 ^ (31 - l) := by
    rw [UInt64.toNat_shiftLeft, hsU, Nat.mod_eq_of_lt (show 31 - l < 64 by lia),
      Nat.shiftLeft_eq, Nat.mod_eq_of_lt hV64]
  have hvtvs : ((b <<< (31 - l).toUInt64) >>> 32).toUInt32.toNat * 2 ^ 32 +
      (b <<< (31 - l).toUInt64).toUInt32.toNat = b.toNat * 2 ^ (31 - l) := by
    simp only [UInt64.toNat_toUInt32, UInt64.toNat_shiftRight, UInt64.reduceToNat, Nat.reduceMod,
      Nat.shiftRight_eq_div_pow, hV]
    lia
  have hVge : 2 ^ 32 * 2 ^ (31 - l) ≤ b.toNat * 2 ^ (31 - l) := Nat.mul_le_mul_right _ hb
  have hvt : 0 < ((b <<< (31 - l).toUInt64) >>> 32).toUInt32.toNat := by
    simp only [UInt64.toNat_toUInt32, UInt64.toNat_shiftRight, UInt64.reduceToNat, Nat.reduceMod,
      Nat.shiftRight_eq_div_pow, hV]
    have : 2 ^ 32 ≤ b.toNat * 2 ^ (31 - l) := Nat.le_trans (Nat.le_mul_of_pos_right _ hS) hVge
    lia
  generalize ((b <<< (31 - l).toUInt64) >>> 32).toUInt32 = vt at hvtvs hvt ⊢
  generalize (b <<< (31 - l).toUInt64).toUInt32 = vs at hvtvs ⊢
  -- The shift: four `shlStep`s make `X 2ˢ` in five words.
  obtain ⟨e₀, c₀⟩ := shlStep_spec (31 - l) (by lia) (x₀) 0 (by simpa using hS)
  simp only [UInt32.toNat_zero, Nat.add_zero] at e₀
  obtain ⟨e₁, c₁⟩ := shlStep_spec (31 - l) (by lia) (x₁) _ c₀
  obtain ⟨e₂, c₂⟩ := shlStep_spec (31 - l) (by lia) (x₂) _ c₁
  obtain ⟨e₃, c₃⟩ := shlStep_spec (31 - l) (by lia) (x₃) _ c₂
  generalize shlStep (31 - l).toUInt64 (x₀) 0 = p₀ at *
  generalize shlStep (31 - l).toUInt64 (x₁) p₀.2 = p₁ at *
  generalize shlStep (31 - l).toUInt64 (x₂) p₁.2 = p₂ at *
  generalize shlStep (31 - l).toUInt64 (x₃) p₂.2 = p₃ at *
  have hXlt :
      (x₀.toNat + 2 ^ 32 * x₁.toNat + 2 ^ 64 * x₂.toNat + 2 ^ 96 * x₃.toNat) < 2 ^ 128 := by
    have := (x₀).toNat_lt; have := (x₁).toNat_lt
    have := (x₂).toNat_lt; have := (x₃).toNat_lt
    lia
  -- The top two words start the remainder, below `V`.
  have hR0 : ((p₃.2.toUInt64 <<< 32) + p₃.1.toUInt64).toNat =
      p₃.2.toNat * 2 ^ 32 + p₃.1.toNat := by
    have := p₃.1.toNat_lt
    have : p₃.2.toNat < 2 ^ 31 :=
      Nat.lt_of_lt_of_le c₃ (Nat.pow_le_pow_right (by decide) (by lia))
    simp only [UInt64.toNat_add, UInt64.toNat_shiftLeft, UInt32.toNat_toUInt64, UInt64.reduceToNat,
      Nat.reduceMod, Nat.shiftLeft_eq]
    lia
  generalize hSdef : 2 ^ (31 - l) = S at *
  generalize hX :
    (x₀.toNat + 2 ^ 32 * x₁.toNat + 2 ^ 64 * x₂.toNat + 2 ^ 96 * x₃.toNat) = X at *
  generalize b.toNat = B at *
  -- `X S = W`, the five words.
  have hW : X * S = p₀.1.toNat + 2 ^ 32 * p₁.1.toNat + 2 ^ 64 * p₂.1.toNat +
      2 ^ 96 * (p₃.2.toNat * 2 ^ 32 + p₃.1.toNat) := by
    rw [← hX]
    simp only [Nat.add_mul, Nat.mul_assoc]
    lia
  have hXS : X * S < 2 ^ 128 * S := Nat.mul_lt_mul_of_pos_right hXlt hS
  have hR0lt : ((p₃.2.toUInt64 <<< 32) + p₃.1.toUInt64).toNat < vt.toNat * 2 ^ 32 + vs.toNat := by
    rw [hR0, hvtvs]
    lia
  -- The three steps.
  obtain ⟨q₂, r₂⟩ := div2Step_spec vt vs _ p₂.1 hvt hR0lt
  have hr₂ := Nat.mod_lt ((((p₃.2.toUInt64 <<< 32) + p₃.1.toUInt64).toNat * 2 ^ 32 +
    p₂.1.toNat)) (show 0 < vt.toNat * 2 ^ 32 + vs.toNat by lia)
  rw [← r₂] at hr₂
  generalize div2Step vt vs ((p₃.2.toUInt64 <<< 32) + p₃.1.toUInt64) p₂.1 = t₂ at *
  obtain ⟨q₁, r₁⟩ := div2Step_spec vt vs t₂.2 p₁.1 hvt hr₂
  have hr₁ := Nat.mod_lt (t₂.2.toNat * 2 ^ 32 + p₁.1.toNat)
    (show 0 < vt.toNat * 2 ^ 32 + vs.toNat by lia)
  rw [← r₁] at hr₁
  generalize div2Step vt vs t₂.2 p₁.1 = t₁ at *
  obtain ⟨q₀, r₀⟩ := div2Step_spec vt vs t₁.2 p₀.1 hvt hr₁
  have hr₀ := Nat.mod_lt (t₁.2.toNat * 2 ^ 32 + p₀.1.toNat)
    (show 0 < vt.toNat * 2 ^ 32 + vs.toNat by lia)
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
    lia
  obtain ⟨hq, hr⟩ := div_of_scaled hS hQ hr₀
  refine ⟨?_, ?_⟩
  · have := t₀.1.toNat_lt
    have := t₁.1.toNat_lt
    simp only [UInt64.toNat_add, UInt64.toNat_shiftLeft, UInt32.toNat_toUInt64,
      UInt64.reduceToNat, Nat.reduceMod, Nat.shiftLeft_eq]
    rw [hq]
    lia
  · rw [hr, UInt64.toNat_shiftRight, hsU, Nat.mod_eq_of_lt (show 31 - l < 64 by lia),
      Nat.shiftRight_eq_div_pow, hSdef]

public theorem divRem128_spec (a : UInt32Array) (b : UInt64) (ha : a.size ≤ 4)
    (hb : 4294967296 ≤ b) :
    (divRem128 a b).1.toNat + 2 ^ 64 * (divRem128 a b).2.1.toNat = MPN.W32.toNat a / b.toNat ∧
      (divRem128 a b).2.2.toNat = MPN.W32.toNat a % b.toNat := by
  rw [divRem128, toNat_four a ha]
  exact divRem128L_spec _ _ _ _ b hb

/-- `divRemWord` without the remainder, which `div2` saves allocating. -/
public def divWord (a : UInt32Array) (b : UInt64) : UInt32Array :=
  if b < 4294967296 then (divRem1 a b.toUInt32).1 else div2 a (b >>> 32).toUInt32 b.toUInt32

public theorem divWord_eq (a : UInt32Array) (b : UInt64) : divWord a b = (divRemWord a b).1 := by
  unfold divWord divRemWord
  split <;> simp [div2_eq]

/-! ## Decimal strings

`main`'s `DecChunks.toDecimalWith` and `DecChunks.ofDecimalWith` on `ops32`, which converts this
library's slices to arrays by copying them.
-/

/-- The size below which divide and conquer writes digits by chunks. -/
public def decBaseSize : Nat := 32

/-- The size, in digits, below which divide and conquer reads digits by chunks. -/
public def parseBaseSize : Nat := 300

private theorem hto (x : UInt32Array.Slice) : DecChunks.vA x.copy = ops32.val x := by
  rw [decVA_eq, ops32_val, toNat_copy]

private theorem hof (a : UInt32Array) : ops32.val a.toSlice = DecChunks.vA a := by
  rw [ops32_val, decVA_eq]

/--
The decimal digits of limbs: by chunks of nine digits below `strDC` limbs, and by divide and
conquer from `strDC` limbs (`NatOps.toDec`), down to `decBaseSize` limbs.
-/
public def toDecimalWith (strDC : Nat) (a : UInt32Array) (_h : isTrimmed a = true) : String :=
  DecChunks.toDecimalWith ops32 (·.copy) (·.toSlice) strDC decBaseSize a

public theorem toDecimalWith_eq (strDC : Nat) (a : UInt32Array) (h : isTrimmed a = true) :
    toDecimalWith strDC a h = _root_.Nat.repr (MPN.W32.toNat a) := by
  rw [toDecimalWith, DecChunks.toDecimalWith_eq _ _ _ hto hof, decVA_eq]

/--
The limbs of a string of decimal digits that `String.isNat` accepts, trimmed: from `9 parseDC`
digits by divide and conquer (`NatOps.fromDec`), and below by chunks of nine digits.
-/
public def ofDecimalWith (parseDC : Nat) (s : String) : UInt32Array :=
  trim (DecChunks.ofDecimalWith ops32 (·.copy) (·.toSlice) parseDC parseBaseSize s)

public theorem ofDecimalWith_spec (parseDC : Nat) (s : String) (h : s.isNat = true) :
    isTrimmed (ofDecimalWith parseDC s) = true ∧
      s.toNat? = some (MPN.W32.toNat (ofDecimalWith parseDC s)) := by
  refine ⟨isTrimmed_trim _, ?_⟩
  rw [DecChunks.ofDecimalWith_spec _ _ _ hto hof _ _ s h, ofDecimalWith, toNat_trim, decVA_eq]

/-- `a / b` for a nonzero word, trimmed: by `divRem128` for up to four limbs and `2³² ≤ b`. -/
public def divW (a : UInt32Array) (b : UInt64) : UInt32Array :=
  if a.size ≤ 4 ∧ 4294967296 ≤ b then
    let q := divRem128 a b
    if q.2.1 = 0 then limbsOfWord q.1 else limbs4 q.1 q.2.1
  else trim (divWord a b)

/-- `a % b` for a nonzero word: by `divRem128` for up to four limbs and `2³² ≤ b`. -/
public def modW (a : UInt32Array) (b : UInt64) : UInt64 :=
  if a.size ≤ 4 ∧ 4294967296 ≤ b then (divRem128 a b).2.2 else (divRemWord a b).2

/-- `⌊log₂ a⌋`, from the top limb. -/
public def log2A (a : UInt32Array) : Nat :=
  if h : a.size < 4294967295 then
    WordArray.log2W a 0 a.size.toUSize (by
      have e := toNat_toUSize (lt_usizeSize h)
      exact ⟨by simp [e]; exact Nat.le_refl _, by simp [e]; exact lt_usizeSize h⟩)
  else (MPN.W32.toNat a).log2

public theorem log2A_eq (a : UInt32Array) (_ha : isTrimmed a = true) (_hb : 2 ^ 64 ≤ MPN.W32.toNat a) :
    log2A a = (MPN.W32.toNat a).log2 := by
  by_cases h : a.size < 4294967295
  · simp only [log2A, h, ↓reduceDIte]
    rw [WordArray.log2W_eq, toNat_array_eq_valAt, toNat_toUSize (lt_usizeSize h)]
    rfl
  · simp only [log2A, h, ↓reduceDIte]

end Nat

/-- `main`'s whole-number operations on trimmed arrays of 32-bit limbs: this library's. -/
public instance natLimbs32 : NatLimbs UInt32Array where
  val a := MPN.W32.toNat a
  trimmed := isTrimmed
  eq_of_val a b ha hb h := by rw [← ofNat_toNat ha, ← ofNat_toNat hb]; exact congrArg _ h
  decEq := inferInstance
  -- In constant time, like `Nat`'s, which is the low word: the size and the bottom and top limbs.
  hash a := mixHash (hash a.size) (mixHash (hash a[0]!) (hash a[a.size - 1]!))
  ofNat := MPN.W32.ofNat
  trimmed_ofNat := isTrimmed_ofNat
  val_ofNat := MPN.W32.toNat_ofNat
  ofWord := limbsOfWord
  trimmed_ofWord w := (limbsOfWord_spec w).2
  val_ofWord w := (limbsOfWord_spec w).1
  wide := Nat.limbs4
  wide_spec lo hi h := Nat.limbs4_spec lo hi h
  fits a := decide (a.size ≤ 2)
  fits_iff a h := by
    rw [decide_eq_true_iff]
    constructor
    · intro hs
      have := toNat_lt a.toSlice
      have : 2 ^ (32 * a.size) ≤ 2 ^ 64 := Nat.pow_le_pow_right (by decide) (by lia)
      simp only [UInt32Array.size_toSlice] at *
      change MPN.W32.toNat a < 2 ^ 64
      lia
    · intro hv
      change MPN.W32.toNat a < 2 ^ 64 at hv
      refine Nat.le_of_not_lt fun hs => ?_
      have := pow_le_toNat_of_isTrimmed h (by lia)
      have : 2 ^ 64 ≤ 2 ^ (32 * (a.size - 1)) := Nat.pow_le_pow_right (by decide) (by lia)
      lia
  toWord := wordOfLimbs
  val_toWord a h hv := by
    change MPN.W32.toNat a < 2 ^ 64 at hv
    refine toNat_wordOfLimbs a (Nat.le_of_not_lt fun hs => ?_)
    have := pow_le_toNat_of_isTrimmed h (by lia)
    have : 2 ^ 64 ≤ 2 ^ (32 * (a.size - 1)) := Nat.pow_le_pow_right (by decide) (by lia)
    lia
  add a b := MPN.W32.add a b
  trimmed_add a b := isTrimmed_add a b
  val_add a b := MPN.W32.toNat_add a b
  sub a b := trim (subVal a b)
  trimmed_sub _ _ := isTrimmed_trim _
  val_sub a b h := by
    show MPN.W32.toNat (trim (subVal a b)) = _
    rw [toNat_trim, toNat_subVal _ _ h]
  lt a b := MPN.W32.ltA a b
  lt_iff a b := MPN.W32.ltA_iff a b
  mul a b := MPN.W32.mul a b
  trimmed_mul a b := isTrimmed_mul a b
  val_mul a b := MPN.W32.toNat_mul a b
  sqr a := MPN.W32.sqr a
  trimmed_sqr a := isTrimmed_sqr a
  val_sqr a := MPN.W32.toNat_sqr a
  div a b := MPN.W32.div a b
  trimmed_div a b := isTrimmed_div a b
  val_div a b := MPN.W32.toNat_div a b
  mod a b := MPN.W32.mod a b
  trimmed_mod a b := isTrimmed_mod a b
  val_mod a b := MPN.W32.toNat_mod a b
  divW := Nat.divW
  trimmed_divW a b := by
    show isTrimmed (Nat.divW a b) = true
    by_cases h : a.size ≤ 4 ∧ 4294967296 ≤ b
    · by_cases h0 : (Nat.divRem128 a b).2.1 = 0
      · have e : Nat.divW a b = limbsOfWord (Nat.divRem128 a b).1 := by simp [Nat.divW, h, h0]
        rw [e]; exact (limbsOfWord_spec _).2
      · have e : Nat.divW a b = Nat.limbs4 (Nat.divRem128 a b).1 (Nat.divRem128 a b).2.1 := by
          simp [Nat.divW, h, h0]
        rw [e]; exact (Nat.limbs4_spec _ _ h0).1
    · have e : Nat.divW a b = trim (Nat.divWord a b) := by simp [Nat.divW, h]
      rw [e]; exact isTrimmed_trim _
  val_divW a b hb := by
    show MPN.W32.toNat (Nat.divW a b) = _
    by_cases h : a.size ≤ 4 ∧ 4294967296 ≤ b
    · have hq := (Nat.divRem128_spec a b h.1 h.2).1
      by_cases h0 : (Nat.divRem128 a b).2.1 = 0
      · have e : Nat.divW a b = limbsOfWord (Nat.divRem128 a b).1 := by simp [Nat.divW, h, h0]
        rw [e, (limbsOfWord_spec _).1]
        rw [h0, UInt64.toNat_zero, Nat.mul_zero, Nat.add_zero] at hq
        exact hq
      · have e : Nat.divW a b = Nat.limbs4 (Nat.divRem128 a b).1 (Nat.divRem128 a b).2.1 := by
          simp [Nat.divW, h, h0]
        rw [e, (Nat.limbs4_spec _ _ h0).2]
        exact hq
    · have e : Nat.divW a b = trim (Nat.divWord a b) := by simp [Nat.divW, h]
      rw [e, toNat_trim, Nat.divWord_eq, (Nat.divRemWord_spec a b hb).1]
  modW := Nat.modW
  val_modW a b hb := by
    unfold Nat.modW
    split
    · rename_i h; exact (Nat.divRem128_spec a b h.1 h.2).2
    · exact (Nat.divRemWord_spec a b hb).2
  shl a n := MPN.W32.shiftLeft a n
  trimmed_shl a n := isTrimmed_shiftLeft a n
  val_shl a n := MPN.W32.toNat_shiftLeft a n
  shr a n := MPN.W32.shiftRight a n
  trimmed_shr a n := isTrimmed_shiftRight a n
  val_shr a n := MPN.W32.toNat_shiftRight a n
  land a b := MPN.W32.land a b
  trimmed_land a b := isTrimmed_land a b
  val_land a b := MPN.W32.toNat_land a b
  lor a b := MPN.W32.lor a b
  trimmed_lor a b := isTrimmed_lor a b
  val_lor a b := MPN.W32.toNat_lor a b
  xor a b := MPN.W32.xor a b
  trimmed_xor a b := isTrimmed_xor a b
  val_xor a b := MPN.W32.toNat_xor a b
  log2 := Nat.log2A
  log2_eq a h hb := Nat.log2A_eq a h hb
  toDecimal a := if h : isTrimmed a = true then Nat.toDecimalWith config.strDC a h
    else _root_.Nat.repr (MPN.W32.toNat a)
  toDecimal_eq a h := by
    show (if h : isTrimmed a = true then Nat.toDecimalWith config.strDC a h
      else _root_.Nat.repr (MPN.W32.toNat a)) = _
    rw [dite_eq_left_of_eq_true (eq_true h), Nat.toDecimalWith_eq]
  ofDecimal := Nat.ofDecimalWith config.parseDC
  ofDecimal_spec s h := Nat.ofDecimalWith_spec _ s h

/-- A natural number: `main`'s `GNat` on arrays of 32-bit limbs. -/
public protected abbrev Nat := GNat UInt32Array

namespace Nat

export GNat (small large ofLimbs wideOf toNat_wideOf add sub mul div mod blt decEq shiftLeft
  shiftRight land lor xor sqr pow sqrtNewton toNat_ofNat toNat_small toNat_inj ofNat_toNat trimmed_limbs
  toNat_add toNat_sub toNat_mul toNat_div toNat_mod blt_iff toNat_shiftLeft toNat_shiftRight
  toNat_land toNat_lor toNat_xor log2_eq toNat_sqr toNat_pow toNat_sqrtNewton repr_eq ofString?_eq
  toNat_hAdd toNat_hSub toNat_hMul toNat_hDiv toNat_hMod toNat_ofNat' lt_iff_toNat_lt
  le_iff_toNat_le)

/-- The `MPN.Nat` of a natural number. -/
public abbrev ofNat (n : _root_.Nat) : MPN.W32.Nat := GNat.ofNat n

/-- The number that a string of decimal digits denotes, like `String.toNat?`. -/
public abbrev ofString? (s : String) : Option MPN.W32.Nat := GNat.ofString? s

/-- The value of the limbs of an `MPN.Nat`. -/
public theorem toNat_limbs (x : MPN.W32.Nat) : MPN.W32.toNat x.limbs = x.toNat := GNat.val_limbs x

@[simp] public theorem toNat_ofLimbs (a : UInt32Array) (h : isTrimmed a = true) :
    (ofLimbs a h : MPN.W32.Nat).toNat = MPN.W32.toNat a := GNat.toNat_ofLimbs a h

/--
The number that a string of decimal digits denotes, like `String.toNat?`, with the threshold of
divide and conquer `parseDC` (`ofDecimalWith`).
-/
public def ofStringWith (parseDC : _root_.Nat) (s : String) : Option MPN.W32.Nat :=
  if h : s.isNat then some (ofLimbs (ofDecimalWith parseDC s) (ofDecimalWith_spec parseDC s h).1)
  else none

public theorem ofStringWith_eq (parseDC : _root_.Nat) (s : String) :
    ofStringWith parseDC s = s.toNat?.map ofNat := by
  unfold ofStringWith
  split
  · rename_i h
    rw [(ofDecimalWith_spec parseDC s h).2, Option.map_some, Option.some.injEq, ← toNat_inj,
      toNat_ofLimbs, toNat_ofNat]
  · rename_i h
    rw [String.toNat?_eq_none (by simpa using h), Option.map_none]

/-! ## The bridge to `ops32` and square roots by Zimmermann's recursion -/

/--
The bridge from `MPN.W32.Nat` to `ops32`: the slice of the limbs, and back from a copy, trimmed.
-/
@[expose] public def bridge32 : Bridge UInt32Array UInt32Array.Slice where
  o := ops32
  w := 32
  B_eq := rfl
  one_le_w := by decide
  toO a := a.toSlice
  val_toO _ := rfl
  ofO S := ofLimbs (trim S.copy) (isTrimmed_trim _)
  toNat_ofO S := by rw [toNat_ofLimbs, toNat_trim, toNat_copy, ops32_val]

@[simp] public theorem bridge32_o : bridge32.o = ops32 := rfl

/-- `(⌊√N⌋, N - ⌊√N⌋²)` for `N` of at most two limbs, on words by `WordArray.sqrt2W`. -/
public def sqrtTwo (N : UInt32Array.Slice) : UInt32Array.Slice × UInt32Array.Slice :=
  let c := N.copy
  let s := WordArray.sqrt2W UInt32Array (c.getD 1 0) (c.getD 0 0)
  let n : UInt64 := (c.getD 1 0).toUInt64 * 4294967296 + (c.getD 0 0).toUInt64
  ((limbsOfWord s.toUInt64).toSlice, (limbsOfWord (n - s.toUInt64 * s.toUInt64)).toSlice)

/-- The value of a slice of at most two limbs. -/
private theorem toNat_le_two (N : UInt32Array.Slice) (h : N.size ≤ 2) :
    MPN.W32.toNat N = (N.copy.getD 1 0).toNat * 2 ^ 32 + (N.copy.getD 0 0).toNat := by
  have hc : N.copy.size ≤ 4 := by simp; lia
  have hv := toNat_four N.copy hc
  have h2 : N.copy.getD 2 0 = 0 := by
    rw [UInt32Array.getD_eq_getD_getElem?, getElem?_neg _ _ (by simp; lia)]; rfl
  have h3 : N.copy.getD 3 0 = 0 := by
    rw [UInt32Array.getD_eq_getD_getElem?, getElem?_neg _ _ (by simp; lia)]; rfl
  rw [toNat_copy, h2, h3] at hv
  simp only [UInt32.toNat_zero, Nat.mul_zero, Nat.add_zero] at hv
  lia

private theorem sqrtTwo_spec (N : UInt32Array.Slice) (h2 : N.size ≤ 2) :
    MPN.W32.toNat (sqrtTwo N).1 = _root_.Nat.sqrt (MPN.W32.toNat N) ∧
      MPN.W32.toNat (sqrtTwo N).2 = MPN.W32.toNat N -
        _root_.Nat.sqrt (MPN.W32.toNat N) * _root_.Nat.sqrt (MPN.W32.toNat N) := by
  unfold sqrtTwo
  rw [toNat_le_two N h2]
  dsimp only
  generalize N.copy.getD 1 0 = hi
  generalize N.copy.getD 0 0 = lo
  have hs : (WordArray.sqrt2W UInt32Array hi lo).toNat =
      _root_.Nat.sqrt (hi.toNat * 2 ^ 32 + lo.toNat) :=
    WordArray.val_sqrt2W (A := UInt32Array) hi lo
  generalize WordArray.sqrt2W UInt32Array hi lo = r at hs
  have hhi := hi.toNat_lt; have hlo := lo.toNat_lt; have hr := r.toNat_lt
  have hn : ((hi.toUInt64 * 4294967296 + lo.toUInt64 : UInt64)).toNat =
      hi.toNat * 2 ^ 32 + lo.toNat := by
    simp only [UInt64.toNat_add, UInt64.toNat_mul, UInt32.toNat_toUInt64, UInt64.reduceToNat]
    lia
  have hsq : (r.toUInt64 * r.toUInt64).toNat = r.toNat * r.toNat := by
    rw [UInt64.toNat_mul, UInt32.toNat_toUInt64]
    exact Nat.mod_eq_of_lt (by have := Nat.mul_lt_mul'' hr hr; simpa using this)
  have hle := Nat.sqrt_le (hi.toNat * 2 ^ 32 + lo.toNat)
  rw [← hs] at hle
  rw [(limbsOfWord_spec _).1, (limbsOfWord_spec _).1, UInt32.toNat_toUInt64,
    UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.2 (by rw [hn, hsq]; exact hle)), hn, hsq,
    hs]
  exact ⟨rfl, rfl⟩

/--
`(⌊√N⌋, N - ⌊√N⌋²)`, the base of Zimmermann's step: by `sqrtTwo` for two limbs, and by Newton's
iteration (`Bridge.newtonBase`) above.
-/
public def sqrtBase (N : UInt32Array.Slice) : UInt32Array.Slice × UInt32Array.Slice :=
  bridge32.newtonBase sqrtTwo (fun N => N.size ≤ 2) N

private theorem sqrtBase_spec (N : UInt32Array.Slice) :
    MPN.W32.toNat (sqrtBase N).1 = _root_.Nat.sqrt (MPN.W32.toNat N) ∧
      MPN.W32.toNat (sqrtBase N).2 =
        MPN.W32.toNat N - _root_.Nat.sqrt (MPN.W32.toNat N) * _root_.Nat.sqrt (MPN.W32.toNat N) := by
  have h := bridge32.newtonBase_spec sqrtTwo (fun N => N.size ≤ 2) (fun N h => by
    simp only [bridge32_o, ops32_val]; exact sqrtTwo_spec N (by simpa using h)) N
  simp only [bridge32_o, ops32_val] at h
  exact h

/--
`⌊√x⌋` by Zimmermann's recursion over `bridge32` (`Bridge.sqrtZ`), with Newton's iteration for
roots of up to `T` limbs.
-/
public def sqrtZimmermann (T : Nat) (x : MPN.W32.Nat) : MPN.W32.Nat := bridge32.sqrtZ sqrtBase T x

private theorem toNat_sqrtZimmermann (T : Nat) (x : MPN.W32.Nat) (hx : x.toNat ≠ 0) :
    (sqrtZimmermann T x).toNat = _root_.Nat.sqrt x.toNat :=
  bridge32.toNat_sqrtZ sqrtBase T (fun N _ _ _ _ _ => by
    simp only [bridge32_o, ops32_val]; exact sqrtBase_spec N) x hx

/--
`⌊√n⌋`: by Newton's iteration (`sqrtNewton`) for roots below `Z` limbs, and from there by
Zimmermann's recursion (`sqrtZimmermann`), with Newton's iteration for roots of up to `T` limbs.
-/
public def sqrtWith (Z T : Nat) (n : MPN.W32.Nat) : MPN.W32.Nat :=
  Dispatch.sqrtBy (fun a => 2 * Z ≤ a.size) (fun a h => sqrtZimmermann T (large a h)) n

@[simp] public theorem toNat_sqrtWith (Z T : Nat) (n : MPN.W32.Nat) :
    (sqrtWith Z T n).toNat = _root_.Nat.sqrt n.toNat :=
  Dispatch.toNat_sqrtBy _ _ (fun a h _ => toNat_sqrtZimmermann _ _ (by
    simp only [GNat.toNat]; have := h.2; lia)) n

/-- `sqrtWith` from roots of `config.sqrtZimmermann` limbs, down to `config.sqrtBase`. -/
public def sqrt (n : MPN.W32.Nat) : MPN.W32.Nat := sqrtWith config.sqrtZimmermann config.sqrtBase n

@[simp] public theorem toNat_sqrt (n : MPN.W32.Nat) : (sqrt n).toNat = _root_.Nat.sqrt n.toNat :=
  toNat_sqrtWith ..

/-! ## Greatest common divisor -/

/--
The leading 62 bits of `a`, normalized so that its top bit is set, and the bits of `b` at the same
positions, as the words of Lehmer's algorithm. Their values only affect its speed: every step on
the full numbers is checked.
-/
public def leadWords (a b : UInt32Array) : LeadWords :=
  let n := a.size
  let c := (31 - (a.getD (n - 1) 0).log2).toUInt64
  let lead (t₂ t₁ t₀ : UInt32) : Int64 :=
    let w := (((t₂.toUInt64 <<< 32) ||| t₁.toUInt64) <<< c) ||| (t₀.toUInt64 >>> (32 - c))
    (w >>> 2).toInt64
  ⟨lead (a.getD (n - 1) 0) (a.getD (n - 2) 0) (a.getD (n - 3) 0),
    lead (b.getD (n - 1) 0) (b.getD (n - 2) 0) (b.getD (n - 3) 0)⟩

/-! ## Two words

The words of `main`'s `gcd2`, Euclid's algorithm on numbers below `2¹²⁸` as pairs of words, like
GMP's `mpn_gcd_22`: the high word of a product, the remainder of two words by one (`rem2`), and the
two words of a number below `2⁹⁶`, where `gcd2` beats Lehmer's algorithm.
-/

/-- The high word of `a b`. -/
public theorem toNat_mulWide_snd (a b : UInt64) :
    (mulWide a b).2.toNat = a.toNat * b.toNat / 2 ^ 64 := by
  have h := mulWide_spec a b
  have := (mulWide a b).1.toNat_lt
  rw [← h, Nat.add_mul_div_left _ _ (by decide), Nat.div_eq_of_lt this, Nat.zero_add]

/-- Reducing the high part of `A m + c` modulo `b` first. -/
private theorem mod_step (A m c b : Nat) : (A * m + c) % b = (A % b * m + c) % b := by
  have h : A * m + c = A % b * m + c + b * (A / b * m) := by
    rw [show A * m = (A % b + b * (A / b)) * m by rw [Nat.mod_add_div], Nat.add_mul,
      Nat.mul_assoc]
    lia
  rw [h, Nat.add_mul_mod_self_left]

/-- The two halves of a word. -/
private theorem toNat_halves (x : UInt64) :
    x.toUInt32.toNat + 2 ^ 32 * (x >>> 32).toUInt32.toNat = x.toNat := by
  have := x.toNat_lt
  simp only [UInt64.toNat_toUInt32, UInt64.toNat_shiftRight, UInt64.reduceToNat, Nat.reduceMod,
    Nat.shiftRight_eq_div_pow]
  rw [Nat.mod_eq_of_lt (a := x.toNat / 2 ^ 32) (by lia)]
  have := Nat.div_add_mod x.toNat (2 ^ 32)
  lia

/--
`(ah β + al) % bl` in words: by `divRem128L` for `bl ≥ 2³²`, and below by three remainders of words,
each of a remainder followed by 32 more bits, which fits in a word.
-/
public def rem2 (ah al bl : UInt64) : UInt64 :=
  if 4294967296 ≤ bl then
    (divRem128L al.toUInt32 (al >>> 32).toUInt32 ah.toUInt32 (ah >>> 32).toUInt32 bl).2.2
  else
    let r₁ := ah % bl
    let r₂ := ((r₁ <<< 32) + (al >>> 32)) % bl
    ((r₂ <<< 32) + (al &&& 0xFFFFFFFF)) % bl

public theorem toNat_rem2 (ah al bl : UInt64) (hb : 0 < bl.toNat) :
    (rem2 ah al bl).toNat = (ah.toNat * 2 ^ 64 + al.toNat) % bl.toNat := by
  unfold rem2
  split
  · rename_i h
    rw [(divRem128L_spec _ _ _ _ bl h).2]
    congr 1
    have e₁ := toNat_halves al; have e₂ := toNat_halves ah
    lia
  · rename_i h
    rw [UInt64.le_iff_toNat_le] at h
    simp only [UInt64.reduceToNat] at h
    have hal := al.toNat_lt
    -- A remainder below `bl < 2³²`, followed by 32 bits.
    have shift (r : UInt64) (x : UInt64) (hr : r.toNat < bl.toNat) (hx : x.toNat < 2 ^ 32) :
        ((r <<< 32) + x).toNat = r.toNat * 2 ^ 32 + x.toNat := by
      simp only [UInt64.toNat_add, UInt64.toNat_shiftLeft, UInt64.reduceToNat, Nat.reduceMod,
        Nat.shiftLeft_eq]
      rw [Nat.mod_eq_of_lt (a := r.toNat * 2 ^ 32) (by lia), Nat.mod_eq_of_lt (by lia)]
    have hhi : (al >>> 32).toNat = al.toNat / 2 ^ 32 := by
      simp [UInt64.toNat_shiftRight, Nat.shiftRight_eq_div_pow]
    have hlo : (al &&& 0xFFFFFFFF).toNat = al.toNat % 2 ^ 32 := by
      rw [UInt64.toNat_and]; exact Nat.and_two_pow_sub_one_eq_mod _ 32
    have r₁ : (ah % bl).toNat = ah.toNat % bl.toNat := UInt64.toNat_mod ..
    have hr₁ : (ah % bl).toNat < bl.toNat := by rw [r₁]; exact Nat.mod_lt _ hb
    have e₂ := shift (ah % bl) (al >>> 32) hr₁ (by rw [hhi]; lia)
    have r₂ : (((ah % bl) <<< 32 + (al >>> 32)) % bl).toNat =
        (ah.toNat * 2 ^ 32 + al.toNat / 2 ^ 32) % bl.toNat := by
      rw [UInt64.toNat_mod, e₂, r₁, hhi, ← mod_step]
    have hr₂ : (((ah % bl) <<< 32 + (al >>> 32)) % bl).toNat < bl.toNat := by
      rw [UInt64.toNat_mod]; exact Nat.mod_lt _ hb
    have e₃ := shift _ (al &&& 0xFFFFFFFF) hr₂ (by rw [hlo]; exact Nat.mod_lt _ (by decide))
    dsimp only
    rw [UInt64.toNat_mod, e₃, r₂, hlo, ← mod_step (ah.toNat * 2 ^ 32 + al.toNat / 2 ^ 32) (2 ^ 32)
      (al.toNat % 2 ^ 32) bl.toNat]
    have hv : (ah.toNat * 2 ^ 32 + al.toNat / 2 ^ 32) * 2 ^ 32 + al.toNat % 2 ^ 32 =
        ah.toNat * 2 ^ 64 + al.toNat := by
      have := Nat.div_add_mod al.toNat (2 ^ 32)
      lia
    rw [hv]

/-- Whether a number is below `2⁹⁶`, from its size. -/
public def fits2 : MPN.W32.Nat → Bool
  | small _ => true
  | large a _ => a.size ≤ 3

/-- The word `x + 2³² y` of two limbs. -/
@[inline] public def word2 (x y : UInt32) : UInt64 := x.toUInt64 + (y.toUInt64 <<< 32)

private theorem toNat_word2 (x y : UInt32) : (word2 x y).toNat = x.toNat + 2 ^ 32 * y.toNat := by
  have := x.toNat_lt; have := y.toNat_lt
  simp only [word2, UInt64.toNat_add, UInt64.toNat_shiftLeft, UInt32.toNat_toUInt64,
    UInt64.reduceToNat, Nat.reduceMod, Nat.shiftLeft_eq]
  rw [Nat.mod_eq_of_lt (a := y.toNat * 2 ^ 32) (by lia), Nat.mod_eq_of_lt (by lia)]
  lia

/-- The high and low words of a number below `2¹²⁸`, read from its limbs. -/
public def hiWord : MPN.W32.Nat → UInt64
  | small _ => 0
  | large a _ => word2 (a.getD 2 0) (a.getD 3 0)

public def loWord : MPN.W32.Nat → UInt64
  | small w => w
  | large a _ => word2 (a.getD 0 0) (a.getD 1 0)

public theorem v2_words (x : MPN.W32.Nat) (h : fits2 x = true) :
    (hiWord x).toNat * 2 ^ 64 + (loWord x).toNat = x.toNat := by
  cases x with
  | small w => simp [hiWord, loWord, GNat.toNat]
  | large a ha =>
    simp only [fits2, decide_eq_true_eq] at h
    show (word2 (a.getD 2 0) (a.getD 3 0)).toNat * 2 ^ 64 +
        (word2 (a.getD 0 0) (a.getD 1 0)).toNat =
      MPN.W32.toNat a
    simp only [toNat_word2, toNat_four a (by lia)]
    lia

/-! ## Lehmer's step and half-gcd's base case

The cofactors of a run of `lehmerSteps` on the leading words, checked on words (`wmat32`), for
`main`'s `LehmerStep` (`lehmer32`), which applies them by `mulSubMul` and multiplies the matrices of
half-gcd's base case by `mulAddMul`, converting this library's slices for it (`steps32`).
-/

/-- A `2 × 2` matrix of words below `2³¹`, and the sign of its determinant, with unboxed fields. -/
public structure WMat where
  s11 : UInt32
  s12 : UInt32
  s21 : UInt32
  s22 : UInt32
  neg : Bool

/-- `|x|` as a word, for the cofactors of `lehmerSteps`. -/
@[inline] public def absW (x : Int64) : UInt32 := (if x < 0 then 0 - x else x).toUInt64.toUInt32

/--
The matrix `[[|D|, |B|], [|C|, |A|]]` of the cofactors `m`, when its entries are below `2³¹` and its
determinant is `±1`, checked on `Nat`, where its products fit in a word.
-/
@[inline] public def wmat32 (m : Cofactors) : Option WMat :=
  let A := absW m.A
  let B := absW m.B
  let C := absW m.C
  let D := absW m.D
  if A < 0x80000000 ∧ B < 0x80000000 ∧ C < 0x80000000 ∧ D < 0x80000000 then
    if D.toNat * A.toNat = B.toNat * C.toNat + 1 then some ⟨D, B, C, A, false⟩
    else if B.toNat * C.toNat = D.toNat * A.toNat + 1 then some ⟨D, B, C, A, true⟩
    else none
  else none

public theorem ok_wmat32 (m : Cofactors) (S : WMat) (h : wmat32 m = some S) :
    LehmerStep.OK UInt32Array S.s11 S.s12 S.s21 S.s22 S.neg := by
  unfold wmat32 at h
  dsimp only at h
  split at h
  · rename_i hb
    obtain ⟨hA, hB, hC, hD⟩ := hb
    simp only [UInt32.lt_iff_toNat_lt, UInt32.reduceToNat] at hA hB hC hD
    split at h
    · rename_i he
      rw [Option.some.injEq] at h
      subst h
      exact ⟨hD, hB, hC, hA, fun _ => he, fun h => absurd h (by simp)⟩
    · split at h
      · rename_i _ he
        rw [Option.some.injEq] at h
        subst h
        exact ⟨hD, hB, hC, hA, fun h => absurd h (by simp), fun _ => he⟩
      · exact absurd h (by simp)
  · exact absurd h (by simp)

/-- The value of an array, as `LehmerStep` reads it. -/
public theorem vA_eq (a : UInt32Array) : LehmerStep.vA a = MPN.W32.toNat a :=
  (toNat_array_eq_valAt a).symm

/-- Lehmer's step on 32-bit limbs for `main`'s `LehmerStep`: one run of `lehmerSteps`. -/
public instance lehmer32 : LehmerOps UInt32Array UInt32 where
  trim := trim
  vA_trim a := by rw [vA_eq, vA_eq, toNat_trim]
  trimmed := isTrimmed
  trimmed_trim := isTrimmed_trim
  W := WMat
  s11 := WMat.s11
  s12 := WMat.s12
  s21 := WMat.s21
  s22 := WMat.s22
  neg := WMat.neg
  wmat := wmat32
  ok_wmat := ok_wmat32
  cof₁ a b := let w := leadWords a b; lehmerSteps w.x w.y 1 0 0 1 100
  cof₂ a b := let w := leadWords a b; lehmerSteps w.x w.y 1 0 0 1 100
  two := false

/--
Half-gcd's base case of word matrices, for `NatOps.smallBase`: `main`'s `LehmerStep.smallSteps` on
copies of the slices.
-/
public def steps32 : ops32.SmallSteps :=
  LehmerStep.smallSteps ops32 (fun s => s.copy) (fun a => a.toSlice)
    (fun s => by rw [vA_eq, ops32_val, toNat_copy]) (fun a => by rw [ops32_val, vA_eq])
    (fun b s => decide (s < topSize b))

/-- The size below which half-gcd computes its matrices by Lehmer's steps alone. -/
public def hgcdBase : Nat := 128

/-- One reduction of `x ≥ y` by half-gcd over `bridge32` (`Bridge.hgcd`). -/
public def hgcdNat (x y : MPN.W32.Nat) : MPN.W32.Nat × MPN.W32.Nat :=
  bridge32.hgcd (ops32.smallBase steps32) hgcdBase x y

public theorem gcd_hgcdNat (x y : MPN.W32.Nat) :
    _root_.Nat.gcd (hgcdNat x y).1.toNat (hgcdNat x y).2.toNat =
      _root_.Nat.gcd x.toNat y.toNat :=
  bridge32.gcd_hgcd _ (ops32.smallBase_ok steps32) hgcdBase x y

/-- Lehmer's step on the limbs of `x ≥ y` (`Bridge.lehmer`). -/
public def lehmer (x y : MPN.W32.Nat) : Option (MPN.W32.Nat × MPN.W32.Nat) :=
  Bridge.lehmer (fun a h => ofLimbs a h) x y

public theorem gcd_lehmer (x y : MPN.W32.Nat) (p : MPN.W32.Nat × MPN.W32.Nat)
    (h : lehmer x y = some p) :
    _root_.Nat.gcd p.1.toNat p.2.toNat = _root_.Nat.gcd x.toNat y.toNat :=
  Bridge.gcd_lehmer _ (fun a _ => by rw [toNat_ofLimbs, vA_eq]) vA_eq x y p h

/-- The size of a number, in limbs. -/
public def sizeL : MPN.W32.Nat → _root_.Nat
  | small _ => 2
  | large a _ => a.size

/-- The parts of `main`'s greatest common divisor that depend on 32-bit limbs. -/
public instance gcdLimbs32 : GcdLimbs UInt32Array where
  mulh a b := (mulWide a b).2
  toNat_mulh := toNat_mulWide_snd
  rem2 := rem2
  toNat_rem2 := toNat_rem2
  fits2 := fits2
  hi := hiWord
  lo := loWord
  val_two := v2_words
  lehmer := lehmer
  gcd_lehmer := gcd_lehmer
  hgcd := hgcdNat
  gcd_hgcd := gcd_hgcdNat
  size := sizeL
  half := config.gcdHalf

export GNat (gcd lcm gcdWith toNat_gcd toNat_lcm toNat_gcdWith)

end Nat

end MPN.W32
