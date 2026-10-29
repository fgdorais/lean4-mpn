/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import MPN.Add
public import MPN.Sub
public import MPN.Cmp
public import MPN.Mul
public import MPN.Sqr
public import MPN.Div
public import MPN.Bits
public import MPN.Decimal
public import MPN.MulSubMul
public import MPN.WordGcd
public import MPN.Generic.HGCD
public import MPN.Generic.Radix
public import MPN.Generic.Sqrt
public import MPN.Natural
import Std.Data.String.ToNat
import all Init.Data.Repr

/-!
# Natural numbers

`MPN.Nat` is `main`'s `GNat` on arrays of 32-bit limbs: a natural number as a machine word below
`2⁶⁴` and as trimmed limbs above, with every operation proved correct against `Nat`. The instance
`natLimbs32` of `NatLimbs` gives it this library's operations on trimmed limbs, with a fast path
for the division of up to four limbs by a word (`divRem128`). The square root by Zimmermann's
recursion and the greatest common divisor by Lehmer's algorithm and half-gcd are defined here on
`MPN.Nat`.
-/


open ScalarArray

namespace MPN

/-! ## Limbs and words -/

/-- A trimmed array of limbs is at least `β ^ (n - 1)` for `n` limbs. -/
public theorem pow_le_toNat_of_isTrimmed {a : UInt32Array} (h : isTrimmed a = true)
    (hpos : 0 < a.size) : 2 ^ (32 * (a.size - 1)) ≤ toNat a := by
  refine Nat.le_of_not_lt fun hlt => ?_
  rw [toNat_toSlice] at hlt
  have := getElem_eq_zero_of_ofLimbs_lt (l := a.toList) (k := a.size - 1) (by simp; lia) hlt
  rw [isTrimmed_iff, IsTrimmed, List.getLast?_eq_getElem?] at h
  simp only [UInt32Array.length_toList] at h
  rw [List.getElem?_eq_getElem (by simp; lia), this] at h
  exact h rfl

/-- The limbs of a word: none for `0`, one below `2³²`, two otherwise. -/
public def limbsOfWord (n : UInt64) : UInt32Array :=
  if n = 0 then
    .empty
  else if n < 4294967296 then
    (UInt32Array.emptyWithCapacity 1).push n.toUInt32
  else
    ((UInt32Array.emptyWithCapacity 2).push n.toUInt32).push (n >>> 32).toUInt32

public theorem isTrimmed_of_getLast {a : UInt32Array} {x : UInt32} (h : a.toList.getLast? = some x)
    (hx : x ≠ 0) : isTrimmed a = true := by
  rw [isTrimmed_iff, IsTrimmed, h]
  intro h'
  exact hx (Option.some.inj h')

public theorem limbsOfWord_spec (n : UInt64) :
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
        lia
      refine ⟨?_, isTrimmed_of_getLast (by rw [hl]; rfl) hx⟩
      rw [toNat_toSlice, hl]
      simp only [ofLimbs_cons, ofLimbs_nil, Nat.mul_zero, Nat.add_zero, UInt64.toNat_toUInt32]
      lia
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
        lia
      refine ⟨?_, isTrimmed_of_getLast (by rw [hl]; rfl) hx⟩
      rw [toNat_toSlice, hl]
      simp only [ofLimbs_cons, ofLimbs_nil, Nat.mul_zero, Nat.add_zero, UInt64.toNat_toUInt32, hhi]
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
  rw [hw, toNat_toSlice]
  have hl : a.toList = (a.toList.take 2) := (List.take_of_length_le (by simp; lia)).symm
  rw [hl, ofLimbs_take_add_one_getD, ofLimbs_take_add_one_getD]
  simp only [List.take_zero, ofLimbs_nil, Nat.mul_zero, Nat.pow_zero, Nat.one_mul, Nat.zero_add,
    UInt32Array.getD_eq_getD_getElem?, List.getD_eq_getElem?_getD, UInt32Array.getElem?_toList]
  lia

namespace Nat

/-! ## Results of two words -/

/-- The three or four limbs of `lo + 2⁶⁴ hi`, for `hi ≠ 0`. -/
public def limbs4 (lo hi : UInt64) : UInt32Array :=
  let r := (((UInt32Array.emptyWithCapacity 4).push lo.toUInt32).push (lo >>> 32).toUInt32).push
    hi.toUInt32
  if hi < 4294967296 then r else r.push (hi >>> 32).toUInt32

public theorem toList_limbs4 (lo hi : UInt64) :
    (limbs4 lo hi).toList = [lo.toUInt32, (lo >>> 32).toUInt32, hi.toUInt32] ++
      (if hi < 4294967296 then [] else [(hi >>> 32).toUInt32]) := by
  unfold limbs4
  split <;> simp

public theorem limbs4_spec (lo hi : UInt64) (h : hi ≠ 0) :
    isTrimmed (limbs4 lo hi) = true ∧
      MPN.toNat (limbs4 lo hi) = lo.toNat + 2 ^ 64 * hi.toNat := by
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
      lia
    · simp only [hs, ite_true, List.append_nil, ofLimbs_cons, ofLimbs_nil, UInt64.toNat_toUInt32,
        UInt64.toNat_shiftRight, UInt64.reduceToNat, Nat.reduceMod, Nat.shiftRight_eq_div_pow]
      lia
  · have hs' := hs
    rw [UInt64.lt_iff_toNat_lt] at hs'
    simp only [UInt64.reduceToNat] at hs'
    refine ⟨isTrimmed_of_getLast (x := (hi >>> 32).toUInt32) (by rw [toList_limbs4]; simp [hs])
      ?_, ?_⟩
    · intro e
      have := congrArg UInt32.toNat e
      simp only [UInt64.toNat_toUInt32, UInt64.toNat_shiftRight, UInt64.reduceToNat,
        Nat.reduceMod, Nat.shiftRight_eq_div_pow, UInt32.toNat_zero] at this
      lia
    · simp only [hs, ite_false, List.cons_append, List.nil_append, ofLimbs_cons, ofLimbs_nil,
        UInt64.toNat_toUInt32, UInt64.toNat_shiftRight, UInt64.reduceToNat, Nat.reduceMod,
        Nat.shiftRight_eq_div_pow]
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
    MPN.toNat (divRemWord a b).1 = MPN.toNat a / b.toNat ∧
      (divRemWord a b).2.toNat = MPN.toNat a % b.toNat := by
  have hb' : 0 < b.toNat := by
    rcases Nat.eq_zero_or_pos b.toNat with h | h
    · exact absurd (UInt64.toNat_inj.1 (by simpa using h)) hb
    · exact h
  have hB := b.toNat_lt
  -- `q b + r = a` with `r < b` determines both.
  have key : ∀ q r : Nat, q * b.toNat + r = MPN.toNat a → r < b.toNat →
      q = MPN.toNat a / b.toNat ∧ r = MPN.toNat a % b.toNat := fun q r h₁ h₂ => by
    have := (Nat.div_mod_unique (a := MPN.toNat a) (b := b.toNat) (d := q) (c := r) hb').2
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
    MPN.toNat a = (a.getD 0 0).toNat + 2 ^ 32 * (a.getD 1 0).toNat +
      2 ^ 64 * (a.getD 2 0).toNat + 2 ^ 96 * (a.getD 3 0).toNat := by
  rw [toNat_toSlice]
  have hl : a.toList = (a.toList.take 4) := (List.take_of_length_le (by simp; lia)).symm
  rw [hl, ofLimbs_take_add_one_getD, ofLimbs_take_add_one_getD, ofLimbs_take_add_one_getD,
    ofLimbs_take_add_one_getD]
  simp only [List.take_zero, ofLimbs_nil, UInt32Array.getD_eq_getD_getElem?,
    List.getD_eq_getElem?_getD, UInt32Array.getElem?_toList]
  simp only [Nat.mul_zero, Nat.pow_zero, Nat.one_mul, Nat.zero_add, Nat.mul_one,
    Nat.reduceMul]

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
    (divRem128 a b).1.toNat + 2 ^ 64 * (divRem128 a b).2.1.toNat = MPN.toNat a / b.toNat ∧
      (divRem128 a b).2.2.toNat = MPN.toNat a % b.toNat := by
  rw [divRem128, toNat_four a ha]
  exact divRem128L_spec _ _ _ _ b hb

/-- `divRemWord` without the remainder, which `div2` saves allocating. -/
public def divWord (a : UInt32Array) (b : UInt64) : UInt32Array :=
  if b < 4294967296 then (divRem1 a b.toUInt32).1 else div2 a (b >>> 32).toUInt32 b.toUInt32

public theorem divWord_eq (a : UInt32Array) (b : UInt64) : divWord a b = (divRemWord a b).1 := by
  unfold divWord divRemWord
  split <;> simp [div2_eq]

/-! ## Decimal strings -/

/-- The decimal digits of a slice by chunks of nine digits (`toDecimal`), `toDec`'s base case. -/
public def decBase (x : UInt32Array.Slice) : String := toDecimal (trim x.copy) (isTrimmed_trim _)

private theorem decBase_spec (x : UInt32Array.Slice) :
    (decBase x).toList = _root_.Nat.toDigits 10 (ops32.val x) := by
  rw [decBase, toDecimal_eq, _root_.Nat.toList_repr, toNat_trim, toNat_copy, ops32_val]

/-- The size below which divide and conquer writes digits by chunks (`decBase`). -/
public def decBaseSize : Nat := 32

/--
The decimal digits of limbs: by chunks of nine digits below `strDC` limbs (`toDecimal`), and by
divide and conquer from `strDC` limbs (`NatOps.toDec`), down to `decBaseSize` limbs.
-/
public def toDecimalWith (strDC : Nat) (a : UInt32Array) (h : isTrimmed a = true) : String :=
  if strDC ≤ a.size then ops32.toDec decBase decBaseSize a.toSlice else toDecimal a h

public theorem toDecimalWith_eq (strDC : Nat) (a : UInt32Array) (h : isTrimmed a = true) :
    toDecimalWith strDC a h = _root_.Nat.repr (MPN.toNat a) := by
  unfold toDecimalWith
  split
  · rw [← String.toList_inj, ops32.toDec_spec decBase decBaseSize decBase_spec,
      _root_.Nat.toList_repr,
      ops32_val]
  · exact toDecimal_eq a h

/-- The value of `len` digits of `arr` from `start` by chunks of nine digits, `fromDec`'s base. -/
public def parseBase (arr : Array Char) (start len : Nat) : UInt32Array.Slice :=
  (trim (arr.foldl DecimalState.step .init start (start + len)).finish).toSlice

private theorem foldl_chars (arr : Array Char) (start len : Nat) :
    arr.foldl DecimalState.step .init start (start + len) =
      (NatOps.chars arr start len).foldl DecimalState.step .init := by
  rw [Array.foldl_eq_foldl_extract, ← Array.foldl_toList, Array.toList_extract,
    List.extract_eq_take_drop, Nat.add_sub_cancel_left, NatOps.chars]

/-- The size, in digits, below which divide and conquer reads digits by chunks (`parseBase`). -/
public def parseBaseSize : Nat := 300

private theorem parseBase_spec (arr : Array Char) (hd : ∀ c ∈ arr.toList, c.isDigit = true)
    (start len : Nat) :
    ops32.val (parseBase arr start len) =
      _root_.Nat.ofDigitChars 10 (NatOps.chars arr start len) 0 := by
  have hc : ∀ c ∈ NatOps.chars arr start len, c.isDigit = true := fun c hc =>
    hd c (List.mem_of_mem_drop (List.mem_of_mem_take hc))
  rw [ops32_val, parseBase, toNat_toSlice, ← toNat_toSlice, toNat_trim, foldl_chars,
    toNat_finish_foldl _ (fun c h => Or.inl (hc c h))]
  congr 1
  apply List.filter_eq_self.2
  intro c h
  have := hc c h
  simp only [bne_iff_ne, ne_eq]
  rintro rfl
  exact absurd this (by decide)

/--
The limbs of a string of decimal digits that `String.isNat` accepts: from `9 parseDC` digits by
divide and conquer (`NatOps.fromDec`), and below by chunks of nine digits.
-/
public def ofDecimalWith (parseDC : Nat) (s : String) : UInt32Array :=
  if 9 * parseDC ≤ s.length then
    let ds := (s.toList.filter (· != '_')).toArray
    trim (ops32.fromDec parseBase parseBaseSize ds).copy
  else trim (s.foldl DecimalState.step .init).finish

public theorem ofDecimalWith_spec (parseDC : Nat) (s : String) (h : s.isNat = true) :
    isTrimmed (ofDecimalWith parseDC s) = true ∧
      s.toNat? = some (MPN.toNat (ofDecimalWith parseDC s)) := by
  rw [String.toNat?_eq_some_ofDigitChars h]
  by_cases hl : 9 * parseDC ≤ s.length
  · have e : ofDecimalWith parseDC s =
        trim (ops32.fromDec parseBase parseBaseSize (s.toList.filter (· != '_')).toArray).copy := by
      simp [ofDecimalWith, hl]
    rw [e]
    refine ⟨isTrimmed_trim _, ?_⟩
    rw [Option.some.injEq, toNat_trim, toNat_copy]
    have hd : ∀ c ∈ (s.toList.filter (· != '_')).toArray.toList, c.isDigit = true := by
      intro c hc
      simp only [List.mem_filter, bne_iff_ne, ne_eq] at hc
      rcases (String.isNat_iff.1 h).2.1 c hc.1 with h' | h'
      · exact h'
      · exact absurd h' hc.2
    have := ops32.fromDec_spec parseBase parseBaseSize _
      (fun st ln _ => parseBase_spec _ hd st ln)
    rw [ops32_val] at this
    rw [this, List.toList_toArray]
  · have e : ofDecimalWith parseDC s = trim (s.foldl DecimalState.step .init).finish := by
      simp [ofDecimalWith, hl]
    rw [e]
    refine ⟨isTrimmed_trim _, ?_⟩
    rw [Option.some.injEq, toNat_trim, String.foldl_eq_foldl_toList]
    exact (toNat_finish_foldl _ (String.isNat_iff.1 h).2.1).symm

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
public def log2A (a : UInt32Array) : Nat := 32 * (a.size - 1) + (a.getD (a.size - 1) 0).toNat.log2

public theorem log2A_eq (a : UInt32Array) (ha : isTrimmed a = true) (hb : 2 ^ 64 ≤ MPN.toNat a) :
    log2A a = (MPN.toNat a).log2 := by
  have hpos : 0 < a.size := by
    rcases Nat.eq_zero_or_pos a.size with h | h
    · rw [toNat_of_size_eq_zero (by simpa using h)] at hb
      lia
    · exact h
  simp only [log2A]
  -- `a = L + β^(n - 1) t` with `L < β^(n - 1)` and `t ≠ 0` the top limb.
  have hsplit := toNat_slice_add_toNat_slice a (a.size - 1) (by simp)
  have hL := toNat_lt (a.toSlice.slice 0 (a.size - 1))
  have htop : MPN.toNat (a.toSlice.slice (a.size - 1) a.toSlice.size) =
      (a.getD (a.size - 1) 0).toNat := by
    rw [toNat_of_size_eq_one (by simp; lia)]
    simp [UInt32Array.getD_eq_getD_getElem?, show a.size - 1 < a.size by lia]
  have ht : (a.getD (a.size - 1) 0).toNat ≠ 0 := by
    have := ha
    rw [isTrimmed_iff, IsTrimmed, List.getLast?_eq_getElem?] at this
    simp only [UInt32Array.length_toList] at this
    rw [List.getElem?_eq_getElem (by simp; lia)] at this
    intro h0
    apply this
    simp only [UInt32Array.getElem_toList]
    congr 1
    apply UInt32.toNat_inj.1
    rw [UInt32.toNat_zero, ← h0]
    simp [UInt32Array.getD_eq_getD_getElem?, show a.size - 1 < a.size by lia]
  simp only [UInt32Array.Slice.size_slice, UInt32Array.size_toSlice] at hL
  rw [show min (a.size - 1) (min a.size a.size - 0) - 0 = a.size - 1 by lia] at hL
  rw [htop] at hsplit
  have hlo := Nat.log2_self_le ht
  have hhi := @Nat.lt_log2_self (a.getD (a.size - 1) 0).toNat
  generalize (a.getD (a.size - 1) 0).toNat = t at *
  symm
  rw [Nat.log2_eq_iff (by lia)]
  have hP : 2 ^ (32 * (a.size - 1) + t.log2) = 2 ^ (32 * (a.size - 1)) * 2 ^ t.log2 :=
    Nat.pow_add _ _ _
  have hP1 : 2 ^ (32 * (a.size - 1) + t.log2 + 1) =
      2 ^ (32 * (a.size - 1)) * 2 ^ (t.log2 + 1) := by
    rw [Nat.add_assoc, Nat.pow_add]
  constructor
  · rw [hP, ← hsplit]
    have := Nat.mul_le_mul_left (2 ^ (32 * (a.size - 1))) hlo
    lia
  · rw [hP1, ← hsplit]
    have := Nat.mul_le_mul_left (2 ^ (32 * (a.size - 1))) (Nat.succ_le_of_lt hhi)
    rw [Nat.mul_succ] at this
    lia

end Nat

/-- `main`'s whole-number operations on trimmed arrays of 32-bit limbs: this library's. -/
public instance natLimbs32 : NatLimbs UInt32Array where
  val a := MPN.toNat a
  trimmed := isTrimmed
  eq_of_val a b ha hb h := by rw [← ofNat_toNat ha, ← ofNat_toNat hb]; exact congrArg _ h
  decEq := inferInstance
  hash a := hash a
  ofNat := MPN.ofNat
  trimmed_ofNat := isTrimmed_ofNat
  val_ofNat := MPN.toNat_ofNat
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
      change MPN.toNat a < 2 ^ 64
      lia
    · intro hv
      change MPN.toNat a < 2 ^ 64 at hv
      refine Nat.le_of_not_lt fun hs => ?_
      have := pow_le_toNat_of_isTrimmed h (by lia)
      have : 2 ^ 64 ≤ 2 ^ (32 * (a.size - 1)) := Nat.pow_le_pow_right (by decide) (by lia)
      lia
  toWord := wordOfLimbs
  val_toWord a h hv := by
    change MPN.toNat a < 2 ^ 64 at hv
    refine toNat_wordOfLimbs a (Nat.le_of_not_lt fun hs => ?_)
    have := pow_le_toNat_of_isTrimmed h (by lia)
    have : 2 ^ 64 ≤ 2 ^ (32 * (a.size - 1)) := Nat.pow_le_pow_right (by decide) (by lia)
    lia
  add a b := MPN.add a b
  trimmed_add a b := isTrimmed_add a b
  val_add a b := MPN.toNat_add a b
  sub a b := trim (subVal a b)
  trimmed_sub _ _ := isTrimmed_trim _
  val_sub a b h := by
    show MPN.toNat (trim (subVal a b)) = _
    rw [toNat_trim, toNat_subVal _ _ h]
  lt a b := MPN.lt a b
  lt_iff a b := MPN.lt_iff a b
  mul a b := MPN.mul a b
  trimmed_mul a b := isTrimmed_mul a b
  val_mul a b := MPN.toNat_mul a b
  sqr a := MPN.sqr a
  trimmed_sqr a := isTrimmed_sqr a
  val_sqr a := MPN.toNat_sqr a
  div a b := MPN.div a b
  trimmed_div a b := isTrimmed_div a b
  val_div a b := MPN.toNat_div a b
  mod a b := MPN.mod a b
  trimmed_mod a b := isTrimmed_mod a b
  val_mod a b := MPN.toNat_mod a b
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
    show MPN.toNat (Nat.divW a b) = _
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
  shl a n := MPN.shiftLeft a n
  trimmed_shl a n := isTrimmed_shiftLeft a n
  val_shl a n := MPN.toNat_shiftLeft a n
  shr a n := MPN.shiftRight a n
  trimmed_shr a n := isTrimmed_shiftRight a n
  val_shr a n := MPN.toNat_shiftRight a n
  land a b := MPN.land a b
  trimmed_land a b := isTrimmed_land a b
  val_land a b := MPN.toNat_land a b
  lor a b := MPN.lor a b
  trimmed_lor a b := isTrimmed_lor a b
  val_lor a b := MPN.toNat_lor a b
  xor a b := MPN.xor a b
  trimmed_xor a b := isTrimmed_xor a b
  val_xor a b := MPN.toNat_xor a b
  log2 := Nat.log2A
  log2_eq a h hb := Nat.log2A_eq a h hb
  toDecimal a := if h : isTrimmed a = true then Nat.toDecimalWith config.strDC a h
    else _root_.Nat.repr (MPN.toNat a)
  toDecimal_eq a h := by
    show (if h : isTrimmed a = true then Nat.toDecimalWith config.strDC a h
      else _root_.Nat.repr (MPN.toNat a)) = _
    rw [dite_eq_left_of_eq_true (eq_true h), Nat.toDecimalWith_eq]
  ofDecimal := Nat.ofDecimalWith config.parseDC
  ofDecimal_spec s h := Nat.ofDecimalWith_spec _ s h

/-- A natural number: `main`'s `GNat` on arrays of 32-bit limbs. -/
public protected abbrev Nat := GNat UInt32Array

namespace Nat

export GNat (small large ofLimbs wideOf toNat_wideOf add sub mul div mod blt decEq shiftLeft shiftRight land
  lor xor sqr pow sqrtNewton toNat_ofNat toNat_small toNat_inj ofNat_toNat trimmed_limbs
  toNat_add toNat_sub toNat_mul toNat_div toNat_mod blt_iff toNat_shiftLeft toNat_shiftRight
  toNat_land toNat_lor toNat_xor log2_eq toNat_sqr toNat_pow toNat_sqrtNewton repr_eq ofString?_eq
  toNat_hAdd toNat_hSub toNat_hMul toNat_hDiv toNat_hMod toNat_ofNat' lt_iff_toNat_lt
  le_iff_toNat_le)

/-- The `MPN.Nat` of a natural number. -/
public abbrev ofNat (n : _root_.Nat) : MPN.Nat := GNat.ofNat n

/-- The number that a string of decimal digits denotes, like `String.toNat?`. -/
public abbrev ofString? (s : String) : Option MPN.Nat := GNat.ofString? s

/-- The value of the limbs of an `MPN.Nat`. -/
public theorem toNat_limbs (x : MPN.Nat) : MPN.toNat x.limbs = x.toNat := GNat.val_limbs x

@[simp] public theorem toNat_ofLimbs (a : UInt32Array) (h : isTrimmed a = true) :
    (ofLimbs a h : MPN.Nat).toNat = MPN.toNat a := GNat.toNat_ofLimbs a h

/--
The number that a string of decimal digits denotes, like `String.toNat?`, with the threshold of
divide and conquer `parseDC` (`ofDecimalWith`).
-/
public def ofStringWith (parseDC : _root_.Nat) (s : String) : Option MPN.Nat :=
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

/-! ## Square roots by Zimmermann's recursion -/

/-- `toNat` of the slice of the limbs. -/
private theorem toNat_limbs_toSlice (x : MPN.Nat) : MPN.toNat x.limbs.toSlice = x.toNat :=
  toNat_limbs x

/-- `(⌊√N⌋, N - ⌊√N⌋²)` by Newton's iteration (`sqrtNewton`), the base of Zimmermann's step. -/
public def sqrtBase (N : UInt32Array.Slice) : UInt32Array.Slice × UInt32Array.Slice :=
  let S := (sqrtNewton (ofLimbs (trim N.copy) (isTrimmed_trim _))).limbs.toSlice
  (S, ops32.sub N (ops32.sqr S))

private theorem sqrtBase_spec (N : UInt32Array.Slice) :
    MPN.toNat (sqrtBase N).1 = _root_.Nat.sqrt (MPN.toNat N) ∧
      MPN.toNat (sqrtBase N).2 =
        MPN.toNat N - _root_.Nat.sqrt (MPN.toNat N) * _root_.Nat.sqrt (MPN.toNat N) := by
  have hS : MPN.toNat (sqrtNewton (ofLimbs (trim N.copy) (isTrimmed_trim _))).limbs.toSlice =
      _root_.Nat.sqrt (MPN.toNat N) := by
    rw [toNat_limbs_toSlice, toNat_sqrtNewton, toNat_ofLimbs, toNat_trim, toNat_copy]
  refine ⟨hS, ?_⟩
  simp only [sqrtBase]
  rw [← ops32_val, ops32.val_sub _ _ (by rw [ops32.val_sqr, ops32_val, hS]; exact Nat.sqrt_le _),
    ops32.val_sqr, ops32_val, ops32_val, hS]

/-- The size of the root at or below which Zimmermann's recursion takes Newton's iteration. -/
public def sqrtBaseSize : Nat := 16

/--
`⌊√x⌋` by Zimmermann's recursion (`NatOps.sqrtRemAux`) on `N = x 4ᶜ` of `2 n` limbs with
`β^(2n) ≤ 4 N`, then `⌊√N⌋ / 2ᶜ`.
-/
public def sqrtZimmermann (x : MPN.Nat) : MPN.Nat :=
  let L := GNat.log2 x
  let n := L / 64 + 1
  let c := (64 * n - 1 - L) / 2
  let S := (ops32.sqrtRemAux sqrtBase sqrtBaseSize (shiftLeft x (2 * c)).limbs.toSlice n).1
  shiftRight (ofLimbs (trim S.copy) (isTrimmed_trim _)) c

/-- `N = X 4ᶜ` has `2 n` limbs and `β^(2n) ≤ 4 N`, for the `n` and `c` of `sqrtZimmermann`. -/
private theorem sqrtZimmermann_bounds (X : Nat) (hx : X ≠ 0) :
    X * 2 ^ (2 * ((64 * (X.log2 / 64 + 1) - 1 - X.log2) / 2)) < 2 ^ (64 * (X.log2 / 64 + 1)) ∧
      2 ^ (64 * (X.log2 / 64 + 1)) ≤
        4 * (X * 2 ^ (2 * ((64 * (X.log2 / 64 + 1) - 1 - X.log2) / 2))) := by
  have hlo : 2 ^ X.log2 ≤ X := Nat.log2_self_le hx
  have hhi : X < 2 ^ (X.log2 + 1) := Nat.lt_log2_self
  generalize X.log2 = L at *
  generalize hn : L / 64 + 1 = n
  generalize hc : (64 * n - 1 - L) / 2 = c
  have hc₁ : 64 * n - 2 ≤ L + 2 * c := by lia
  have hc₂ : L + 2 * c + 1 ≤ 64 * n := by lia
  constructor
  · calc X * 2 ^ (2 * c) < 2 ^ (L + 1) * 2 ^ (2 * c) :=
          Nat.mul_lt_mul_of_pos_right hhi (Nat.two_pow_pos _)
      _ = 2 ^ (L + 2 * c + 1) := by rw [← Nat.pow_add]; congr 1; lia
      _ ≤ 2 ^ (64 * n) := Nat.pow_le_pow_right (by decide) hc₂
  · calc 2 ^ (64 * n) ≤ 2 ^ (L + 2 * c + 2) := Nat.pow_le_pow_right (by decide) (by lia)
      _ = 4 * (2 ^ L * 2 ^ (2 * c)) := by
          rw [show (4 : Nat) = 2 ^ 2 by rfl, ← Nat.pow_add, ← Nat.pow_add]; congr 1; lia
      _ ≤ 4 * (X * 2 ^ (2 * c)) := Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ hlo)

private theorem toNat_sqrtZimmermann_of (x : MPN.Nat) (n c : Nat)
    (hNlt : x.toNat * 2 ^ (2 * c) < 2 ^ (64 * n))
    (hNge : 2 ^ (64 * n) ≤ 4 * (x.toNat * 2 ^ (2 * c))) :
    (shiftRight (ofLimbs (trim (ops32.sqrtRemAux sqrtBase sqrtBaseSize
      (shiftLeft x (2 * c)).limbs.toSlice n).1.copy) (isTrimmed_trim _)) c).toNat =
      _root_.Nat.sqrt x.toNat := by
  have hn : 1 ≤ n := by
    refine Nat.pos_of_ne_zero fun h => ?_
    rw [h] at hNlt hNge
    have : x.toNat ≠ 0 := by intro h'; rw [h'] at hNge; simp at hNge
    have := Nat.le_mul_of_pos_right x.toNat (Nat.two_pow_pos (2 * c))
    simp at hNlt; lia
  have hNv : ops32.val (shiftLeft x (2 * c)).limbs.toSlice = x.toNat * 2 ^ (2 * c) := by
    rw [ops32_val, toNat_limbs_toSlice, toNat_shiftLeft]
  have hB : ops32.B ^ (2 * n) = 2 ^ (64 * n) := by
    rw [show ops32.B = 2 ^ 32 from rfl, ← Nat.pow_mul]; congr 1; lia
  obtain ⟨i₃, -⟩ := ops32.sqrtRemAux_spec sqrtBase sqrtBaseSize
    (fun N _ _ _ _ _ => by simp only [ops32_val]; exact sqrtBase_spec N)
    ⟨2 ^ 31, by decide⟩ n _ hn (by rw [hNv, hB]; exact hNlt) (by rw [hNv, hB]; exact hNge)
  rw [hNv, ops32_val] at i₃
  rw [toNat_shiftRight, toNat_ofLimbs, toNat_trim, toNat_copy, i₃, sqrt_mul_four_pow]

private theorem toNat_sqrtZimmermann (x : MPN.Nat) (hx : x.toNat ≠ 0) :
    (sqrtZimmermann x).toNat = _root_.Nat.sqrt x.toNat := by
  obtain ⟨h₁, h₂⟩ := sqrtZimmermann_bounds x.toNat hx
  rw [← log2_eq] at h₁ h₂
  exact toNat_sqrtZimmermann_of x _ _ h₁ h₂

/-- The size of the root from which `sqrt` takes Zimmermann's recursion. -/
public def sqrtZimmermannSize : Nat := 40

/--
`⌊√n⌋`: by Newton's iteration (`sqrtNewton`) below `2 sqrtZimmermannSize` limbs, and by
Zimmermann's recursion (`sqrtZimmermann`) from there.
-/
public def sqrt (n : MPN.Nat) : MPN.Nat :=
  match n with
  | small _ => sqrtNewton n
  | large a _ => if 2 * sqrtZimmermannSize ≤ a.size then sqrtZimmermann n else sqrtNewton n

@[simp] public theorem toNat_sqrt (n : MPN.Nat) : (sqrt n).toNat = _root_.Nat.sqrt n.toNat := by
  unfold sqrt
  split
  · exact toNat_sqrtNewton _
  · split
    · rename_i a ha _
      exact toNat_sqrtZimmermann _ (by simp only [GNat.toNat]; lia)
    · exact toNat_sqrtNewton _

/-! ## Greatest common divisor -/

/--
The numbers `|A x + B y|` and `|C x + D y|` of a step of Lehmer's algorithm with the cofactors
`A`, `B`, `C`, `D`, when the step is valid: the cofactors are below `2³¹`, their determinant is
`±1`, their signs alternate as in Euclid's algorithm, and both numbers are nonnegative. Each
number is a difference of two multiples, both from `mulSubMul₂` in one pass, and the
determinant is checked on `Nat`, where its products fit in a word.
-/
def lehmerStep (x y : MPN.Nat) (A B C D : Int) : Option (MPN.Nat × MPN.Nat) :=
  let a := A.natAbs
  let b := B.natAbs
  let c := C.natAbs
  let d := D.natAbs
  if a < 2 ^ 31 ∧ b < 2 ^ 31 ∧ c < 2 ^ 31 ∧ d < 2 ^ 31 ∧ (a * d = b * c + 1 ∨ b * c = a * d + 1)
  then
    if 0 ≤ A ∧ B ≤ 0 ∧ C ≤ 0 ∧ 0 ≤ D then
      let w := mulSubMul₂ x.limbs y.limbs a.toUInt32 b.toUInt32 c.toUInt32 d.toUInt32
      let u := w.1
      let v := w.2
      if u.2 = false ∧ v.2 = false then
        some (ofLimbs (trim u.1) (isTrimmed_trim _), ofLimbs (trim v.1) (isTrimmed_trim _))
      else none
    else if A ≤ 0 ∧ 0 ≤ B ∧ 0 ≤ C ∧ D ≤ 0 then
      let w := mulSubMul₂ y.limbs x.limbs b.toUInt32 a.toUInt32 d.toUInt32 c.toUInt32
      let u := w.1
      let v := w.2
      if u.2 = false ∧ v.2 = false then
        some (ofLimbs (trim u.1) (isTrimmed_trim _), ofLimbs (trim v.1) (isTrimmed_trim _))
      else none
    else none
  else none

/-- `p X - q Y` from `mulSubMul`, when it is not negative, as `|P X + Q Y|`. -/
private theorem toNat_mulSubMul_natAbs (X Y : UInt32Array) (p q : Nat) (P Q : Int)
    (hp : p < 2 ^ 31) (hq : q < 2 ^ 31) (hP : P = p) (hQ : Q = -(q : Int))
    (hn : (mulSubMul X Y p.toUInt32 q.toUInt32).2 = false) :
    MPN.toNat (trim (mulSubMul X Y p.toUInt32 q.toUInt32).1) =
      (P * MPN.toNat X + Q * MPN.toNat Y).natAbs := by
  have hpu : p.toUInt32.toNat = p := by simp [Nat.toUInt32_eq, UInt32.toNat_ofNat']; lia
  have hqu : q.toUInt32.toNat = q := by simp [Nat.toUInt32_eq, UInt32.toNat_ofNat']; lia
  have h := (mulSubMul_spec X Y p.toUInt32 q.toUInt32 (by lia) (by lia)).1 hn
  rw [hpu, hqu] at h
  rw [toNat_trim, hP, hQ]
  generalize MPN.toNat (mulSubMul X Y p.toUInt32 q.toUInt32).1 = R at *
  generalize MPN.toNat X = Xv at *
  generalize MPN.toNat Y = Yv at *
  have : (p : Int) * Xv + -(q : Int) * Yv = (R : Int) := by
    have h' : ((R + Yv * q : Nat) : Int) = ((Xv * p : Nat) : Int) := by rw [h]
    push_cast at h'
    rw [Int.neg_mul]
    rw [Int.mul_comm (p : Int), Int.mul_comm (q : Int)]
    lia
  rw [this, Int.natAbs_natCast]

/-- A valid step of Lehmer's algorithm keeps the greatest common divisor. -/
private theorem lehmerStep_gcd (x y : MPN.Nat) (A B C D : Int) (p : MPN.Nat × MPN.Nat)
    (h : lehmerStep x y A B C D = some p) :
    _root_.Nat.gcd p.1.toNat p.2.toNat = _root_.Nat.gcd x.toNat y.toNat := by
  unfold lehmerStep at h
  simp only [mulSubMul₂_eq] at h
  split at h
  · rename_i hc
    obtain ⟨ha, hb, hc', hd, hdet⟩ := hc
    -- The determinant `A D - B C = |A||D| - |B||C|` in either sign pattern.
    have hdet' (hAD : A * D = (A.natAbs * D.natAbs : Nat))
        (hBC : B * C = (B.natAbs * C.natAbs : Nat)) : A * D - B * C = 1 ∨ A * D - B * C = -1 := by
      rw [hAD, hBC]
      rcases hdet with e | e
      · left; rw [e]; push_cast; lia
      · right; rw [e]; push_cast; lia
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
        exact NatOps.gcd_unimodular _ _ A B C D (hdet' (by rw [hA', hD']; simp)
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
          exact NatOps.gcd_unimodular _ _ A B C D
            (hdet' (by rw [hA', hD']; simp [Int.neg_mul_neg]) (by rw [hB', hC']; simp))
        · exact absurd h (by simp)
      · exact absurd h (by simp)
  · exact absurd h (by simp)

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

/-! ## Two words

Euclid's algorithm on numbers below `2¹²⁸` as pairs of words, like GMP's `mpn_gcd_22` and
`main64`'s `gcd2`: Lehmer's algorithm and its divisions cost more than the steps there.
-/

/-- The high word of `a b`. -/
private theorem toNat_mulWide_snd (a b : UInt64) :
    (mulWide a b).2.toNat = a.toNat * b.toNat / 2 ^ 64 := by
  have h := mulWide_spec a b
  have := (mulWide a b).1.toNat_lt
  rw [← h, Nat.add_mul_div_left _ _ (by decide), Nat.div_eq_of_lt this, Nat.zero_add]

/-- The number `h β + l`. -/
def v2 (h l : UInt64) : Nat := h.toNat * 2 ^ 64 + l.toNat

/-- `(ah β + al) - (bh β + bl)` in two words. -/
@[inline] def sub2h (ah al bh bl : UInt64) : UInt64 := ah - bh - (if al < bl then 1 else 0)

private theorem toNat_sub_add (a b : UInt64) :
    (a - b).toNat + b.toNat = a.toNat + (if a.toNat < b.toNat then 2 ^ 64 else 0) := by
  rw [UInt64.toNat_sub]
  have := a.toNat_lt; have := b.toNat_lt
  split
  · rw [Nat.mod_eq_of_lt (by lia)]; lia
  · rw [show 2 ^ 64 - b.toNat + a.toNat = a.toNat - b.toNat + 2 ^ 64 by lia, Nat.add_mod_right,
      Nat.mod_eq_of_lt (by lia)]
    lia

private theorem v2_sub (ah al bh bl : UInt64) (h : v2 bh bl ≤ v2 ah al) :
    v2 (sub2h ah al bh bl) (al - bl) = v2 ah al - v2 bh bl := by
  unfold v2 sub2h at *
  have := al.toNat_lt; have := bl.toNat_lt; have := ah.toNat_lt; have := bh.toNat_lt
  have := (ah - bh).toNat_lt; have := (al - bl).toNat_lt
  have e₁ := toNat_sub_add al bl
  have e₂ := toNat_sub_add ah bh
  have e₃ := toNat_sub_add (ah - bh) (if al < bl then 1 else 0)
  have := (ah - bh - if al < bl then 1 else 0).toNat_lt
  generalize ah - bh - (if al < bl then 1 else 0) = t at *
  by_cases hl : al < bl
  · have hl' := UInt64.lt_iff_toNat_lt.1 hl
    simp only [hl, hl', ↓reduceIte, UInt64.toNat_one] at e₁ e₃
    split at e₃ <;> lia
  · have hl' := mt UInt64.lt_iff_toNat_lt.2 hl
    simp only [hl, hl', ↓reduceIte, UInt64.toNat_zero] at e₁ e₃
    split at e₃ <;> lia

/-- Whether `ah β + al < bh β + bl`. -/
@[inline] def lt2 (ah al bh bl : UInt64) : Bool := ah < bh || (ah == bh && al < bl)

private theorem lt2_iff (ah al bh bl : UInt64) : lt2 ah al bh bl = true ↔ v2 ah al < v2 bh bl := by
  unfold lt2 v2
  have := al.toNat_lt; have := bl.toNat_lt
  simp only [Bool.or_eq_true, decide_eq_true_eq, Bool.and_eq_true, beq_iff_eq,
    UInt64.lt_iff_toNat_lt, ← UInt64.toNat_inj]
  constructor
  · rintro (h | ⟨h₁, h₂⟩) <;> lia
  · intro h
    rcases Nat.lt_or_ge ah.toNat bh.toNat with h' | h'
    · exact .inl h'
    · exact .inr ⟨by lia, by lia⟩

/-- The quotient estimate of a step: `⌊ah / (bh + 1)⌋`, at least `1`. -/
@[inline] def q2 (ah bh : UInt64) : UInt64 := let q := ah / (bh + 1); if q = 0 then 1 else q

private theorem q2_mul_le (ah al bh bl : UInt64) (h : v2 bh bl ≤ v2 ah al) :
    (q2 ah bh).toNat * v2 bh bl ≤ v2 ah al ∧ 1 ≤ (q2 ah bh).toNat := by
  unfold q2
  dsimp only
  split
  · simp only [UInt64.toNat_one]; lia
  · rename_i hq
    have hq' : (ah / (bh + 1)).toNat ≠ 0 := fun e => hq (UInt64.toNat_inj.1 (by rw [e]; rfl))
    rw [UInt64.toNat_div] at hq' ⊢
    have hb1 : (bh + 1).toNat = bh.toNat + 1 := by
      rw [UInt64.toNat_add, UInt64.toNat_one]
      rcases Nat.lt_or_ge (bh.toNat + 1) (2 ^ 64) with e | e
      · exact Nat.mod_eq_of_lt e
      · exfalso; apply hq'
        rw [UInt64.toNat_add, UInt64.toNat_one,
          show bh.toNat + 1 = 2 ^ 64 by have := bh.toNat_lt; lia]
        simp
    rw [hb1] at hq' ⊢
    have hd := Nat.div_mul_le_self ah.toNat (bh.toNat + 1)
    have := bl.toNat_lt
    unfold v2
    constructor
    · have : ah.toNat / (bh.toNat + 1) * (bh.toNat * 2 ^ 64 + bl.toNat) ≤
          ah.toNat / (bh.toNat + 1) * ((bh.toNat + 1) * 2 ^ 64) :=
        Nat.mul_le_mul_left _ (by lia)
      have : ah.toNat / (bh.toNat + 1) * ((bh.toNat + 1) * 2 ^ 64) ≤ ah.toNat * 2 ^ 64 := by
        rw [← Nat.mul_assoc]; exact Nat.mul_le_mul_right _ hd
      lia
    · lia

/-- The high word of `q (bh β + bl)`. -/
@[inline] def mul2h (q bh bl : UInt64) : UInt64 := q * bh + (mulWide q bl).2

private theorem v2_mul (q bh bl : UInt64) (h : q.toNat * v2 bh bl < 2 ^ 128) :
    v2 (mul2h q bh bl) (q * bl) = q.toNat * v2 bh bl := by
  unfold v2 mul2h at *
  have hm := Nat.div_add_mod (q.toNat * bl.toNat) (2 ^ 64)
  rw [UInt64.toNat_add, UInt64.toNat_mul, toNat_mulWide_snd, UInt64.toNat_mul]
  have : q.toNat * bh.toNat * 2 ^ 64 + q.toNat * bl.toNat < 2 ^ 128 := by
    rw [Nat.mul_add, ← Nat.mul_assoc] at h; exact h
  have : q.toNat * bh.toNat < 2 ^ 64 := by
    rcases Nat.lt_or_ge (q.toNat * bh.toNat) (2 ^ 64) with e | e
    · exact e
    · exfalso
      have := Nat.mul_le_mul_right (2 ^ 64) e
      lia
  rw [Nat.mod_eq_of_lt (a := q.toNat * bh.toNat) this]
  have : q.toNat * bh.toNat + q.toNat * bl.toNat / 2 ^ 64 < 2 ^ 64 := by
    rcases Nat.lt_or_ge (q.toNat * bh.toNat + q.toNat * bl.toNat / 2 ^ 64) (2 ^ 64) with e | e
    · exact e
    · exfalso
      have := Nat.mul_le_mul_right (2 ^ 64) e
      lia
  rw [Nat.mod_eq_of_lt this]
  lia

/-- A step of `gcd2`: `a = (a - q b) + q b` with `q ≥ 1`. -/
private theorem v2_step (ah al bh bl : UInt64) (h : ¬lt2 ah al bh bl = true) :
    v2 (sub2h ah al (mul2h (q2 ah bh) bh bl) (q2 ah bh * bl)) (al - q2 ah bh * bl) +
      (q2 ah bh).toNat * v2 bh bl = v2 ah al ∧ 1 ≤ (q2 ah bh).toNat := by
  rw [lt2_iff] at h
  have hle : v2 bh bl ≤ v2 ah al := Nat.le_of_not_lt h
  obtain ⟨hq, h1⟩ := q2_mul_le ah al bh bl hle
  have h128 : v2 ah al < 2 ^ 128 := by
    unfold v2; have := ah.toNat_lt; have := al.toNat_lt; lia
  have hm := v2_mul (q2 ah bh) bh bl (Nat.lt_of_le_of_lt hq h128)
  have hq' : v2 (mul2h (q2 ah bh) bh bl) (q2 ah bh * bl) ≤ v2 ah al := by rw [hm]; exact hq
  rw [v2_sub _ _ _ _ hq', hm]
  exact ⟨Nat.sub_add_cancel hq, h1⟩


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
def rem2 (ah al bl : UInt64) : UInt64 :=
  if 4294967296 ≤ bl then
    (divRem128L al.toUInt32 (al >>> 32).toUInt32 ah.toUInt32 (ah >>> 32).toUInt32 bl).2.2
  else
    let r₁ := ah % bl
    let r₂ := ((r₁ <<< 32) + (al >>> 32)) % bl
    ((r₂ <<< 32) + (al &&& 0xFFFFFFFF)) % bl

private theorem toNat_rem2 (ah al bl : UInt64) (hb : 0 < bl.toNat) :
    (rem2 ah al bl).toNat = v2 ah al % bl.toNat := by
  unfold rem2
  split
  · rename_i h
    rw [(divRem128L_spec _ _ _ _ bl h).2]
    congr 1
    have e₁ := toNat_halves al; have e₂ := toNat_halves ah
    unfold v2; lia
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
    have hv : (ah.toNat * 2 ^ 32 + al.toNat / 2 ^ 32) * 2 ^ 32 + al.toNat % 2 ^ 32 = v2 ah al := by
      have := Nat.div_add_mod al.toNat (2 ^ 32)
      unfold v2; lia
    rw [hv]

/--
The greatest common divisor of `ah β + al` and `bh β + bl` by Euclid's algorithm on pairs of words,
like GMP's `mpn_gcd_22`: steps `a - q b` with the estimate `q2` of the quotient, which is never too
large, until `b` fits in a word, then one remainder by `rem2` and `wordGcd`.
-/
def gcd2 (ah al bh bl : UInt64) : MPN.Nat :=
  if bh = 0 then
    if bl = 0 then wideOf al ah
    else small (wordGcd bl (rem2 ah al bl))
  else if _h : lt2 ah al bh bl then gcd2 bh bl ah al
  else
    let q := q2 ah bh
    gcd2 bh bl (sub2h ah al (mul2h q bh bl) (q * bl)) (al - q * bl)
termination_by v2 ah al + v2 bh bl + (if v2 ah al < v2 bh bl then 1 else 0)
decreasing_by
  · rw [lt2_iff] at _h
    generalize v2 ah al = A at *
    generalize v2 bh bl = B at *
    split <;> (try split) <;> lia
  · rename_i hb
    obtain ⟨e, h1⟩ := v2_step ah al bh bl _h
    have hpos : 2 ^ 64 ≤ v2 bh bl := by
      have : bh.toNat ≠ 0 := fun e => hb (UInt64.toNat_inj.1 (by rw [e]; rfl))
      unfold v2; lia
    have hb1 : v2 bh bl ≤ (q2 ah bh).toNat * v2 bh bl := Nat.le_mul_of_pos_left _ h1
    rw [lt2_iff] at _h
    generalize v2 (sub2h ah al (mul2h (q2 ah bh) bh bl) (q2 ah bh * bl))
      (al - q2 ah bh * bl) = R at *
    generalize v2 ah al = A at *
    generalize v2 bh bl = B at *
    generalize (q2 ah bh).toNat * B = P at *
    split <;> lia

private theorem toNat_wideOf_v2 (lo hi : UInt64) : (wideOf lo hi : MPN.Nat).toNat = v2 hi lo := by
  rw [toNat_wideOf, v2]; lia

private theorem toNat_gcd2 (ah al bh bl : UInt64) :
    (gcd2 ah al bh bl).toNat = _root_.Nat.gcd (v2 ah al) (v2 bh bl) := by
  induction ah, al, bh, bl using gcd2.induct with
  | case1 ah al =>
    rw [gcd2, ite_eq_left rfl, ite_eq_left rfl, toNat_wideOf_v2]
    simp [v2]
  | case2 ah al bl hl =>
    rw [gcd2, ite_eq_left rfl, ite_eq_right hl]
    have hl' : 0 < bl.toNat := Nat.pos_of_ne_zero fun e => hl (UInt64.toNat_inj.1 (by rw [e]; rfl))
    rw [toNat_small, toNat_wordGcd, toNat_rem2 _ _ _ hl', show v2 0 bl = bl.toNat by simp [v2],
      Nat.gcd_comm, ← Nat.gcd_rec, Nat.gcd_comm]
  | case3 ah al bh bl hb h ih =>
    rw [gcd2, ite_eq_right hb, dite_eq_left h, ih, Nat.gcd_comm]
  | case4 ah al bh bl hb h q ih =>
    simp only [q] at ih
    rw [gcd2, ite_eq_right hb, dite_eq_right h, ih]
    obtain ⟨e, -⟩ := v2_step ah al bh bl h
    rw [← e, Nat.gcd_comm (_ + _), Nat.gcd_add_mul_right_right]

/-- Whether a number is below `2⁹⁶`, from its size. -/
def fits2 : MPN.Nat → Bool
  | small _ => true
  | large a _ => a.size ≤ 3

/-- The word `x + 2³² y` of two limbs. -/
@[inline] def word2 (x y : UInt32) : UInt64 := x.toUInt64 + (y.toUInt64 <<< 32)

private theorem toNat_word2 (x y : UInt32) : (word2 x y).toNat = x.toNat + 2 ^ 32 * y.toNat := by
  have := x.toNat_lt; have := y.toNat_lt
  simp only [word2, UInt64.toNat_add, UInt64.toNat_shiftLeft, UInt32.toNat_toUInt64,
    UInt64.reduceToNat, Nat.reduceMod, Nat.shiftLeft_eq]
  rw [Nat.mod_eq_of_lt (a := y.toNat * 2 ^ 32) (by lia), Nat.mod_eq_of_lt (by lia)]
  lia

/-- The high and low words of a number below `2¹²⁸`, read from its limbs. -/
def hiWord : MPN.Nat → UInt64
  | small _ => 0
  | large a _ => word2 (a.getD 2 0) (a.getD 3 0)

def loWord : MPN.Nat → UInt64
  | small w => w
  | large a _ => word2 (a.getD 0 0) (a.getD 1 0)

private theorem v2_words (x : MPN.Nat) (h : fits2 x = true) :
    v2 (hiWord x) (loWord x) = x.toNat := by
  cases x with
  | small w => simp [v2, hiWord, loWord, GNat.toNat]
  | large a ha =>
    simp only [fits2, decide_eq_true_eq] at h
    show v2 (word2 (a.getD 2 0) (a.getD 3 0)) (word2 (a.getD 0 0) (a.getD 1 0)) = MPN.toNat a
    simp only [v2, toNat_word2, toNat_four a (by lia)]
    lia

/--
The greatest common divisor, by Lehmer's algorithm: the cofactors of Euclid's steps on the leading
words, from `lehmerSteps`, are applied to the full numbers at once with `lehmerStep`, which keeps
the greatest common divisor since their matrix has determinant `±1`; when the step is not valid
or does not make the second number smaller, one step of Euclid's algorithm is taken instead. On
words when both are small.
-/
def gcdLehmer (x y : MPN.Nat) : MPN.Nat :=
  match x, y with
  | small a, small b => small (wordGcd a b)
  | x, y =>
    if _h : y = small 0 then x
    else if blt x y then gcdLehmer y (mod x y)
    else
      let w := leadWords x.limbs y.limbs
      let m := lehmerSteps w.x w.y 1 0 0 1 100
      match lehmerStep x y m.A.toInt m.B.toInt m.C.toInt m.D.toInt with
      | some p => if _hy : blt p.2 y then gcdLehmer p.1 p.2 else gcdLehmer y (mod x y)
      | none => gcdLehmer y (mod x y)
termination_by y.toNat
decreasing_by
  all_goals first
    | (rw [blt_iff] at _hy; exact _hy)
    | (have : y.toNat ≠ 0 := fun h' => _h (toNat_inj.1 (by rw [h']; rfl))
       rw [toNat_mod]
       exact Nat.mod_lt _ (by lia))

/-- One step of Euclid's algorithm keeps the greatest common divisor. -/
private theorem gcd_mod_step (x y : MPN.Nat) :
    _root_.Nat.gcd y.toNat (mod x y).toNat = _root_.Nat.gcd x.toNat y.toNat := by
  rw [toNat_mod, Nat.gcd_comm x.toNat y.toNat, Nat.gcd_rec y.toNat x.toNat, Nat.gcd_comm]

private theorem toNat_gcdLehmer (x y : MPN.Nat) :
    (gcdLehmer x y).toNat = _root_.Nat.gcd x.toNat y.toNat := by
  induction x, y using gcdLehmer.induct with
  | case1 a b => rw [gcdLehmer]; exact toNat_wordGcd a b
  | case2 x hxy =>
    rw [gcdLehmer]
    · simp only [↓reduceDIte, toNat_small, UInt64.toNat_zero, Nat.gcd_zero_right]
    · exact hxy
  | case3 x y hxy h hlt ih =>
    rw [gcdLehmer]
    · rw [dite_eq_right h, ite_eq_left hlt, ih, gcd_mod_step]
    · exact hxy
  | case4 x y hxy h hlt w m p hp hy ih =>
    rw [gcdLehmer]
    · rw [dite_eq_right h, ite_eq_right hlt]
      simp only [w, m] at hp
      simp only [hp, dite_eq_left hy, ih, lehmerStep_gcd _ _ _ _ _ _ _ hp]
    · exact hxy
  | case5 x y hxy h hlt w m p hp hy ih =>
    rw [gcdLehmer]
    · rw [dite_eq_right h, ite_eq_right hlt]
      simp only [w, m] at hp
      simp only [hp, dite_eq_right hy, ih, gcd_mod_step]
    · exact hxy
  | case6 x y hxy h hlt w m hp ih =>
    rw [gcdLehmer]
    · rw [dite_eq_right h, ite_eq_right hlt]
      simp only [w, m] at hp
      simp only [hp, ih, gcd_mod_step]
    · exact hxy


/--
The greatest common divisor of small numbers: on words when both are, on pairs of words (`gcd2`)
when both are below `2⁹⁶`, where it beats Lehmer's algorithm, and by `gcdLehmer` otherwise. The
numbers that Lehmer's algorithm leaves along the way are better finished by it.
-/
def gcdSmall (x y : MPN.Nat) : MPN.Nat :=
  match x, y with
  | small a, small b => small (wordGcd a b)
  | x, y =>
    if fits2 x && fits2 y then gcd2 (hiWord x) (loWord x) (hiWord y) (loWord y) else gcdLehmer x y

private theorem toNat_gcdSmall (x y : MPN.Nat) :
    (gcdSmall x y).toNat = _root_.Nat.gcd x.toNat y.toNat := by
  unfold gcdSmall
  split
  · exact toNat_wordGcd _ _
  · split
    · rename_i hf
      simp only [Bool.and_eq_true] at hf
      rw [toNat_gcd2, v2_words _ hf.1, v2_words _ hf.2]
    · exact toNat_gcdLehmer _ _

/-! ## Half-gcd -/

/-- A `2 × 2` matrix of words below `2³¹`, and the sign of its determinant. -/
structure WMat where
  s11 : UInt32
  s12 : UInt32
  s21 : UInt32
  s22 : UInt32
  neg : Bool

/-- `S` has entries below `2³¹` and determinant `±1`, with the sign of `S.neg`. -/
def WMat.OK (S : WMat) : Prop :=
  S.s11.toNat < 2 ^ 31 ∧ S.s12.toNat < 2 ^ 31 ∧ S.s21.toNat < 2 ^ 31 ∧ S.s22.toNat < 2 ^ 31 ∧
    (S.neg = false → S.s11.toNat * S.s22.toNat = S.s12.toNat * S.s21.toNat + 1) ∧
    (S.neg = true → S.s12.toNat * S.s21.toNat = S.s11.toNat * S.s22.toNat + 1)

/-- `|x|` as a word, for the cofactors of `lehmerSteps`. -/
@[inline] def absW (x : Int64) : UInt32 := (if x < 0 then 0 - x else x).toUInt64.toUInt32

/-- The step's result from the two differences of `mulSubMul₂`, when both are nonnegative. -/
def stepOf (S : WMat) (p : (UInt32Array × Bool) × (UInt32Array × Bool)) :
    Option (WMat × UInt32Array.Slice × UInt32Array.Slice) :=
  if p.1.2 = false ∧ p.2.2 = false then some (S, (trim p.1.1).toSlice, (trim p.2.1).toSlice)
  else none

private theorem stepOf_spec (S : WMat) (p : (UInt32Array × Bool) × (UInt32Array × Bool))
    (r : WMat × UInt32Array.Slice × UInt32Array.Slice) (h : stepOf S p = some r) :
    r.1 = S ∧ p.1.2 = false ∧ p.2.2 = false ∧ MPN.toNat r.2.1 = MPN.toNat p.1.1 ∧
      MPN.toNat r.2.2 = MPN.toNat p.2.1 := by
  unfold stepOf at h
  split at h
  · rename_i hn
    rw [Option.some.injEq] at h
    subst h
    exact ⟨rfl, hn.1, hn.2, toNat_trim _, toNat_trim _⟩
  · exact absurd h (by simp)

/--
A step of Lehmer's algorithm for half-gcd's base case, with its matrix: the cofactors `A`, `B`, `C`,
`D` of `lehmerSteps` on the leading words of `a ≥ b` give `S = [[|D|, |B|], [|C|, |A|]]` and the
numbers `x = |A a + B b|` and `y = |C a + D b|` with `(a, b) = S (x, y)`, both from `mulSubMul₂` in
one pass. Only words are checked: below `2³¹`, a determinant of `±1`, and both differences
nonnegative, which make the relation exact; nothing about the cofactors needs a proof.
-/
def stepW (a b : UInt32Array.Slice) : Option (WMat × UInt32Array.Slice × UInt32Array.Slice) :=
  let ca := a.copy
  let cb := b.copy
  let w := leadWords ca cb
  let m := lehmerSteps w.x w.y 1 0 0 1 100
  let A := absW m.A
  let B := absW m.B
  let C := absW m.C
  let D := absW m.D
  if A < 0x80000000 ∧ B < 0x80000000 ∧ C < 0x80000000 ∧ D < 0x80000000 then
    if A.toNat * D.toNat = B.toNat * C.toNat + 1 then
      stepOf ⟨D, B, C, A, false⟩ (mulSubMul₂ ca cb A B C D)
    else if B.toNat * C.toNat = A.toNat * D.toNat + 1 then
      stepOf ⟨D, B, C, A, true⟩ (mulSubMul₂ cb ca B A D C)
    else none
  else none

private theorem fwd_pos₃₂ (p q r s a b X Y : Nat) (hd : s * p = q * r + 1)
    (hX : X + b * q = a * s) (hY : Y + a * r = b * p) :
    a = p * X + q * Y ∧ b = r * X + s * Y := by
  constructor <;> grind

private theorem fwd_neg₃₂ (p q r s a b X Y : Nat) (hd : q * r = s * p + 1)
    (hX : X + a * s = b * q) (hY : Y + b * p = a * r) :
    a = p * X + q * Y ∧ b = r * X + s * Y := by
  constructor <;> grind

private theorem stepW_spec (a b : UInt32Array.Slice) (r : WMat × UInt32Array.Slice ×
    UInt32Array.Slice) (h : stepW a b = some r) : r.1.OK ∧
      MPN.toNat a = r.1.s11.toNat * MPN.toNat r.2.1 + r.1.s12.toNat * MPN.toNat r.2.2 ∧
      MPN.toNat b = r.1.s21.toNat * MPN.toNat r.2.1 + r.1.s22.toNat * MPN.toNat r.2.2 := by
  unfold stepW at h
  dsimp only at h
  generalize lehmerSteps _ _ 1 0 0 1 100 = m at h
  generalize absW m.A = A at h
  generalize absW m.B = B at h
  generalize absW m.C = C at h
  generalize absW m.D = D at h
  split at h
  · rename_i hb
    obtain ⟨hA, hB, hC, hD⟩ := hb
    simp only [UInt32.lt_iff_toNat_lt, UInt32.reduceToNat] at hA hB hC hD
    split at h
    · rename_i hdet
      obtain ⟨e₁, e₂, e₃, e₄, e₅⟩ := stepOf_spec _ _ r h
      rw [mulSubMul₂_eq] at e₂ e₃ e₄ e₅
      have hx := (mulSubMul_spec a.copy b.copy A B (by lia) (by lia)).1 e₂
      have hy := (mulSubMul_spec b.copy a.copy D C (by lia) (by lia)).1 e₃
      simp only [toNat_copy] at hx hy
      rw [e₁]
      refine ⟨⟨hD, hB, hC, hA, fun _ => by lia, fun h => absurd h (by simp)⟩, ?_⟩
      rw [e₄, e₅]
      exact fwd_pos₃₂ _ _ _ _ _ _ _ _ (by lia) hx hy
    · split at h
      · rename_i _ hdet
        obtain ⟨e₁, e₂, e₃, e₄, e₅⟩ := stepOf_spec _ _ r h
        rw [mulSubMul₂_eq] at e₂ e₃ e₄ e₅
        have hx := (mulSubMul_spec b.copy a.copy B A (by lia) (by lia)).1 e₂
        have hy := (mulSubMul_spec a.copy b.copy C D (by lia) (by lia)).1 e₃
        simp only [toNat_copy] at hx hy
        rw [e₁]
        refine ⟨⟨hD, hB, hC, hA, fun h => absurd h (by simp), fun _ => by lia⟩, ?_⟩
        rw [e₄, e₅]
        exact fwd_neg₃₂ _ _ _ _ _ _ _ _ (by lia) hx hy
      · exact absurd h (by simp)
  · exact absurd h (by simp)

/-- `M S`, by `mulAddMul`. -/
def mulMatW (M : Mat2 UInt32Array.Slice) (S : WMat) : Mat2 UInt32Array.Slice :=
  let m11 := M.m11.copy
  let m12 := M.m12.copy
  let m21 := M.m21.copy
  let m22 := M.m22.copy
  ⟨(trim (mulAddMul m11 m12 S.s11 S.s21)).toSlice, (trim (mulAddMul m11 m12 S.s12 S.s22)).toSlice,
    (trim (mulAddMul m21 m22 S.s11 S.s21)).toSlice, (trim (mulAddMul m21 m22 S.s12 S.s22)).toSlice,
    M.neg != S.neg⟩

/--
Half-gcd's base case of word matrices, for `NatOps.smallBase`: Lehmer's steps applied by
`mulSubMul₂` (`stepW`), and the matrix updated by `mulAddMul` (`mulMatW`).
-/
def steps32 : ops32.SmallSteps where
  W := WMat
  e₁₁ S := S.s11.toNat
  e₁₂ S := S.s12.toNat
  e₂₁ S := S.s21.toNat
  e₂₂ S := S.s22.toNat
  neg S := S.neg
  ok S := S.OK
  step := stepW
  mulMat := mulMatW
  geB b s := decide (s < topSize b)
  det_of_ok _ h := ⟨h.2.2.2.2.1, h.2.2.2.2.2⟩
  step_spec a b r h := by
    obtain ⟨h₁, h₂, h₃⟩ := stepW_spec a b r h
    simp only [ops32_val]
    exact ⟨h₁, h₂, h₃⟩
  mulMat_spec M S h := by
    obtain ⟨h₁₁, h₁₂, h₂₁, h₂₂, -, -⟩ := h
    simp only [mulMatW, ops32_val, toNat_trim]
    rw [toNat_mulAddMul _ _ _ _ h₁₁ h₂₁, toNat_mulAddMul _ _ _ _ h₁₂ h₂₂,
      toNat_mulAddMul _ _ _ _ h₁₁ h₂₁, toNat_mulAddMul _ _ _ _ h₁₂ h₂₂]
    simp only [toNat_copy]
    refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> simp

/-- The size below which half-gcd computes its matrices by Lehmer's steps alone. -/
public def hgcdBase : Nat := 128

/-- One reduction of `x ≥ y` by half-gcd (`NatOps.hgcdReduce`), trimmed. -/
public def hgcdNat (x y : MPN.Nat) : MPN.Nat × MPN.Nat :=
  let p := ops32.hgcdReduce (ops32.smallBase steps32) hgcdBase x.limbs.toSlice y.limbs.toSlice
  (ofLimbs (trim p.1.copy) (isTrimmed_trim _), ofLimbs (trim p.2.copy) (isTrimmed_trim _))

private theorem gcd_hgcdNat (x y : MPN.Nat) :
    _root_.Nat.gcd (hgcdNat x y).1.toNat (hgcdNat x y).2.toNat =
      _root_.Nat.gcd x.toNat y.toNat := by
  have h := ops32.gcd_hgcdReduce (ops32.smallBase steps32) (ops32.smallBase_ok steps32) hgcdBase
    x.limbs.toSlice
    y.limbs.toSlice
  simp only [ops32_val] at h
  simp only [hgcdNat, toNat_ofLimbs, toNat_trim, toNat_copy]
  rw [h, toNat_toSlice, toNat_toSlice, ← toNat_toSlice, ← toNat_toSlice, toNat_limbs, toNat_limbs]

/-- The smaller of two numbers. -/
def minNat (x y : MPN.Nat) : MPN.Nat := if blt x y then x else y

/-- `hgcdNat` on the larger number first. -/
def hgcdOrd (x y : MPN.Nat) : MPN.Nat × MPN.Nat := if blt x y then hgcdNat y x else hgcdNat x y

private theorem gcd_hgcdOrd (x y : MPN.Nat) :
    _root_.Nat.gcd (hgcdOrd x y).1.toNat (hgcdOrd x y).2.toNat =
      _root_.Nat.gcd x.toNat y.toNat := by
  unfold hgcdOrd
  split
  · rw [gcd_hgcdNat, Nat.gcd_comm]
  · rw [gcd_hgcdNat]

private theorem toNat_minNat_le (x y : MPN.Nat) : (minNat x y).toNat ≤ y.toNat := by
  unfold minNat
  split
  · rename_i h; rw [blt_iff] at h; lia
  · exact Nat.le_refl _

/--
The greatest common divisor: from `half` limbs of the smaller number, reductions by half-gcd
while they make it smaller, and Lehmer's algorithm (`gcdLehmer`) below and otherwise.
-/
public def gcdWith (half : Nat) (x y : MPN.Nat) : MPN.Nat :=
  if half ≤ (minNat x y).limbs.size then
    let p := hgcdOrd x y
    if _hy : blt p.2 (minNat x y) then gcdWith half p.1 p.2 else gcdLehmer x y
  else gcdSmall x y
termination_by y.toNat
decreasing_by
  rw [blt_iff] at _hy
  have := toNat_minNat_le x y
  lia

@[simp] public theorem toNat_gcdWith (half : Nat) (x y : MPN.Nat) :
    (gcdWith half x y).toNat = _root_.Nat.gcd x.toNat y.toNat := by
  induction x, y using gcdWith.induct half with
  | case1 x y h p hy ih =>
    rw [gcdWith, ite_eq_left h]
    simp only [p] at hy ih
    rw [dite_eq_left hy, ih, gcd_hgcdOrd]
  | case2 x y h p hy =>
    rw [gcdWith, ite_eq_left h]
    simp only [p] at hy
    rw [dite_eq_right hy, toNat_gcdLehmer]
  | case3 x y h =>
    rw [gcdWith, ite_eq_right h, toNat_gcdSmall]

/-- The greatest common divisor, with half-gcd from `config.gcdHalf` limbs (`gcdWith`). -/
public def gcd (x y : MPN.Nat) : MPN.Nat := gcdWith config.gcdHalf x y

@[simp] public theorem toNat_gcd (x y : MPN.Nat) :
    (gcd x y).toNat = _root_.Nat.gcd x.toNat y.toNat := toNat_gcdWith _ x y

/-- The least common multiple, `x / gcd x y * y`, and `0` when either is `0`. -/
public def lcm (x y : MPN.Nat) : MPN.Nat :=
  if gcd x y = small 0 then small 0 else div x (gcd x y) * y

@[simp] public theorem toNat_lcm (x y : MPN.Nat) :
    (lcm x y).toNat = _root_.Nat.lcm x.toNat y.toNat := by
  unfold lcm
  split
  · rename_i h
    have h' := congrArg GNat.toNat h
    rw [toNat_gcd, toNat_small, UInt64.toNat_zero, Nat.gcd_eq_zero_iff] at h'
    rw [toNat_small, UInt64.toNat_zero, h'.1, Nat.lcm_zero_left]
  · show (mul (div x (gcd x y)) y).toNat = _
    rw [toNat_mul, toNat_div, toNat_gcd, _root_.Nat.lcm,
      Nat.div_mul_right_comm (Nat.gcd_dvd_left _ _)]

end Nat

end MPN
