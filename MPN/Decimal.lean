/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import MPN.Generic.Radix
public import MPN.Generic.Ops64
import Std.Data.String.ToNat

/-!
# Decimal strings

Ported from `main` with chunks of nineteen decimal digits, the largest power of ten below `β`:

* `toDecimal a` divides by `10¹⁹` with `divRem1` until nothing is left, which gives the chunks
  from the least significant one up, then writes the top chunk as it is and each other one with
  exactly nineteen digits. It equals `Nat.repr a.toNat`.
* `DecimalState.step`, folded over the characters, reads nineteen digits at a time into a chunk
  and then multiplies the limbs so far by `10¹⁹` and adds the chunk; `finish` does the same with
  `10ᵏ` for a last chunk of `k` digits. It skips `_` and equals `Nat.ofDigitChars` of the
  digits, the value that `String.toNat?` gives.

Both take quadratic time; `Num.toDecimal` and `Num.ofDecimal?` switch to divide and conquer
(`NatOps.toDec`, `NatOps.fromDec`) on long numbers. Like `ops64`, the limb operations check that
their arrays are small enough (`fits`) and otherwise compute with `Nat`, which cannot happen.
-/

open ScalarArray UInt64Array

namespace MPN

/-! ## Digits -/

/-- Pushes the `k` low decimal digits of `d`, with leading zeros, onto `s`. -/
def pushDigits (s : String) : Nat → Nat → String
  | 0, _ => s
  | k + 1, d => (pushDigits s k (d / 10)).push (Nat.digitChar (d % 10))

theorem toList_pushDigits (s : String) (k d : Nat) :
    (pushDigits s k d).toList = s.toList ++ padDigits k d := by
  induction k generalizing d with
  | zero => simp [pushDigits, padDigits]
  | succ k ih => rw [pushDigits, String.toList_push, ih, padDigits, List.append_assoc]

/-! ## Limbs to decimal -/

/-- The value of chunks of nineteen digits, most significant first, after `v`. -/
def ofChunks (l : List Nat) (v : Nat) : Nat := l.foldl (fun v d => 10 ^ 19 * v + d) v

theorem ofChunks_eq (l : List Nat) (v : Nat) :
    ofChunks l v = 10 ^ (19 * l.length) * v + ofChunks l 0 := by
  induction l generalizing v with
  | nil => simp [ofChunks]
  | cons x xs ih =>
    have e (w : Nat) : ofChunks (x :: xs) w = ofChunks xs (10 ^ 19 * w + x) := rfl
    rw [e, e, ih, ih (10 ^ 19 * 0 + x), List.length_cons, Nat.mul_succ, Nat.pow_add,
      Nat.mul_zero, Nat.zero_add, Nat.mul_add, Nat.mul_assoc, Nat.add_assoc]

/-- Whether `a` is zero. -/
def isZero (a : UInt64Array) : Bool :=
  if a.size == 0 then true
  else if fits (a.size + 1) then MPN.log2 a.toUSlice == 0 && a[0]! == 0 else a.toNat == 0

private theorem isZero_iff (a : UInt64Array) : isZero a = true ↔ a.toNat = 0 := by
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
def divRem1N (a : UInt64Array) (d : UInt64) : UInt64Array × Nat :=
  if fits (a.size + 1) then
    let p := MPN.divRem1 (UInt64Array.replicate a.size 0).toUSlice a.toUSlice d
    (p.1, p.2.toNat)
  else (ofNat (a.toNat / d.toNat), a.toNat % d.toNat)

private theorem divRem1N_spec (a : UInt64Array) (d : UInt64) (hd : 0 < d.toNat) :
    (divRem1N a d).1.toNat = a.toNat / d.toNat ∧ (divRem1N a d).2 = a.toNat % d.toNat := by
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
  · exact ⟨toNat_ofNat _, rfl⟩

/--
Puts the chunks of nineteen digits of `a`, most significant first, in front of `acc`, by
dividing by `10¹⁹` until nothing is left.
-/
def chunksLoop (a : UInt64Array) (acc : List Nat) : List Nat :=
  if _hz : isZero a = true then acc
  else
    let p := divRem1N a 10000000000000000000
    chunksLoop p.1 (p.2 :: acc)
termination_by a.toNat
decreasing_by
  rw [(divRem1N_spec a _ (by decide)).1]
  rw [isZero_iff] at _hz
  exact Nat.div_lt_self (by lia) (by decide)

private theorem chunksLoop_spec (a : UInt64Array) (acc : List Nat)
    (hacc : ∀ d ∈ acc, d < 10 ^ 19) :
    (∀ d ∈ chunksLoop a acc, d < 10 ^ 19) ∧
      ofChunks (chunksLoop a acc) 0 = 10 ^ (19 * acc.length) * a.toNat + ofChunks acc 0 ∧
      (0 < a.toNat → ∃ c cs, chunksLoop a acc = c :: cs ∧ 0 < c) := by
  induction a, acc using chunksLoop.induct with
  | case1 a acc hz =>
    rw [chunksLoop, dite_eq_left_of_eq_true (eq_true hz)]
    rw [isZero_iff] at hz
    rw [hz]
    exact ⟨hacc, by simp, fun h => absurd h (Nat.lt_irrefl 0)⟩
  | case2 a acc hz p ih =>
    rw [chunksLoop, dite_eq_right hz]
    have ⟨hq, hr⟩ := divRem1N_spec a 10000000000000000000 (by decide)
    have hd : (10000000000000000000 : UInt64).toNat = 10 ^ 19 := rfl
    rw [hd] at hq hr
    have hpos : 0 < a.toNat := by
      rw [isZero_iff] at hz; lia
    have hmod : a.toNat % 10 ^ 19 < 10 ^ 19 := Nat.mod_lt _ (by decide)
    obtain ⟨ih₁, ih₂, ih₃⟩ := ih (fun d hd => by
      rcases List.mem_cons.1 hd with rfl | hd
      · simp only [p]; rw [hr]; exact hmod
      · exact hacc d hd)
    simp only [p] at ih₁ ih₂ ih₃ ⊢
    refine ⟨ih₁, ?_, fun _ => ?_⟩
    · have hc : ofChunks (a.toNat % 10 ^ 19 :: acc) 0 =
          10 ^ (19 * acc.length) * (a.toNat % 10 ^ 19) + ofChunks acc 0 := by
        rw [show ofChunks (a.toNat % 10 ^ 19 :: acc) 0 = ofChunks acc (a.toNat % 10 ^ 19) by
          simp [ofChunks], ofChunks_eq]
      rw [ih₂, hq, List.length_cons, hr, hc, Nat.mul_succ, Nat.pow_add]
      have := Nat.div_add_mod a.toNat (10 ^ 19)
      generalize a.toNat / 10 ^ 19 = q at *
      generalize a.toNat % 10 ^ 19 = r at *
      generalize 10 ^ (19 * acc.length) = P
      rw [← this, Nat.mul_add, Nat.mul_assoc, Nat.add_assoc]
    · by_cases hq0 : a.toNat / 10 ^ 19 = 0
      · have hs : isZero (divRem1N a 10000000000000000000).1 = true := by
          rw [isZero_iff, hq, hq0]
        rw [chunksLoop, dite_eq_left_of_eq_true (eq_true hs)]
        exact ⟨_, _, rfl, by rw [hr]; lia⟩
      · exact ih₃ (by rw [hq]; lia)

/-- Writes the top chunk `c` as it is and each other chunk with nineteen digits. -/
def renderChunks : List Nat → String
  | [] => "0"
  | c :: cs => cs.foldl (fun s d => pushDigits s 19 d) (Nat.repr c)

private theorem toList_foldl_pushDigits (cs : List Nat) (s : String) (v : Nat) (hv : 0 < v)
    (hs : s.toList = Nat.toDigits 10 v) (hcs : ∀ d ∈ cs, d < 10 ^ 19) :
    (cs.foldl (fun s d => pushDigits s 19 d) s).toList = Nat.toDigits 10 (ofChunks cs v) := by
  induction cs generalizing s v with
  | nil => simpa [ofChunks] using hs
  | cons d ds ih =>
    rw [List.foldl_cons, show ofChunks (d :: ds) v = ofChunks ds (10 ^ 19 * v + d) from rfl]
    apply ih _ _ (by have := Nat.mul_pos (show 0 < 10 ^ 19 by decide) hv; lia)
    · rw [toList_pushDigits, hs, toDigits_pow_mul_add 19 hv (hcs d (by simp))]
    · exact fun d' hd' => hcs d' (by simp [hd'])

/-- The decimal digits of `a`, like `Nat.repr`, by chunks of nineteen digits. -/
public def toDecimal (a : UInt64Array) : String := renderChunks (chunksLoop a [])

public theorem toDecimal_eq (a : UInt64Array) : toDecimal a = Nat.repr a.toNat := by
  rw [← String.toList_inj, Nat.toList_repr, toDecimal]
  by_cases hz : isZero a = true
  · rw [chunksLoop, dite_eq_left_of_eq_true (eq_true hz)]
    rw [isZero_iff] at hz
    rw [hz, renderChunks, Nat.toDigits_zero]
    rfl
  · obtain ⟨hlt, hv, hpos⟩ := chunksLoop_spec a [] (by simp)
    obtain ⟨c, cs, he, hc⟩ := hpos (by rw [isZero_iff] at hz; lia)
    rw [he] at hlt hv
    simp only [List.length_nil, Nat.mul_zero, Nat.pow_zero, Nat.one_mul,
      show ofChunks [] 0 = 0 from rfl, Nat.add_zero] at hv
    rw [he, renderChunks, ← hv, show ofChunks (c :: cs) 0 = ofChunks cs c by simp [ofChunks]]
    exact toList_foldl_pushDigits cs _ c hc Nat.toList_repr
      (fun d hd => hlt d (List.mem_cons_of_mem _ hd))

/-! ## Decimal to limbs -/

/-- `a m + v`, by `mul1` with the carry in `v`. -/
def mulAddLimb (a : UInt64Array) (m v : UInt64) : UInt64Array :=
  if fits (a.size + 2) then
    let p := MPN.mul1 (UInt64Array.replicate (a.size + 1) 0).toUSlice a.toUSlice m v
    p.1.set! a.size p.2
  else ofNat (a.toNat * m.toNat + v.toNat)

private theorem toNat_mulAddLimb (a : UInt64Array) (m v : UInt64) :
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

/--
The state of reading decimal digits: the limbs of the chunks so far, and the value of the
`count < 19` digits of the current chunk.
-/
public structure DecimalState where
  acc : UInt64Array
  chunk : UInt64
  count : UInt64

/-- The state before any digit. -/
public def DecimalState.init : DecimalState := ⟨UInt64Array.replicate 0 0, 0, 0⟩

/--
Reads one character: a digit goes into the current chunk, which moves into the limbs when it has
nineteen digits, and `_` is skipped.
-/
public def DecimalState.step (st : DecimalState) (c : Char) : DecimalState :=
  if c = '_' then
    st
  else
    let v := st.chunk * 10 + (c.val - 48).toUInt64
    if st.count = 18 then ⟨mulAddLimb st.acc 10000000000000000000 v, 0, 0⟩
    else ⟨st.acc, v, st.count + 1⟩

/-- The number read: the limbs times `10ᵏ` for the `k` digits of the last chunk, plus that chunk. -/
public def DecimalState.finish (st : DecimalState) : UInt64Array :=
  if st.count = 0 then st.acc else mulAddLimb st.acc (10 ^ st.count.toNat).toUInt64 st.chunk

/-- After reading `p`, the state holds the value of the digits of `p`. -/
def DecimalState.Inv (st : DecimalState) (p : List Char) : Prop :=
  st.count.toNat < 19 ∧ st.chunk.toNat < 10 ^ st.count.toNat ∧
    st.acc.toNat * 10 ^ st.count.toNat + st.chunk.toNat =
      Nat.ofDigitChars 10 (p.filter (· != '_')) 0

private theorem digit_toNat {c : Char} (h : c.isDigit = true) :
    (c.val - 48).toUInt64.toNat = c.toNat - 48 ∧ c.toNat - 48 ≤ 9 := by
  have := Char.isDigit_iff_toNat.1 h
  simp only [Char.reduceToNat] at this
  have hv : c.val.toNat = c.toNat := rfl
  have hle : (48 : UInt32) ≤ c.val := by rw [UInt32.le_iff_toNat_le, hv]; exact this.1
  rw [UInt32.toNat_toUInt64, UInt32.toNat_sub_of_le _ _ hle, hv]
  exact ⟨rfl, by lia⟩

private theorem inv_step (st : DecimalState) (p : List Char) (c : Char)
    (hc : c.isDigit = true ∨ c = '_') (h : st.Inv p) : (st.step c).Inv (p ++ [c]) := by
  obtain ⟨hk, hch, hv⟩ := h
  by_cases hu : c = '_'
  · subst hu
    rw [DecimalState.step, ite_eq_left rfl, DecimalState.Inv, List.filter_append]
    simp only [List.filter_cons, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte,
      List.filter_nil, List.append_nil]
    exact ⟨hk, hch, hv⟩
  · have hd := hc.resolve_right hu
    obtain ⟨hd₁, hd₂⟩ := digit_toNat hd
    have hf : Nat.ofDigitChars 10 ((p ++ [c]).filter (· != '_')) 0 =
        10 * Nat.ofDigitChars 10 (p.filter (· != '_')) 0 + (c.toNat - 48) := by
      have hne : (c != '_') = true := by simpa using hu
      rw [List.filter_append, Nat.ofDigitChars_append]
      simp [List.filter, hne, Nat.ofDigitChars_cons]
    have hpow : 10 ^ st.count.toNat ≤ 10 ^ 18 := Nat.pow_le_pow_right (by decide) (by lia)
    have hv' : (st.chunk * 10 + (c.val - 48).toUInt64).toNat =
        st.chunk.toNat * 10 + (c.toNat - 48) := by
      have hc8 : st.chunk.toNat < 10 ^ 18 := by lia
      rw [UInt64.toNat_add, UInt64.toNat_mul, hd₁]
      simp only [UInt64.reduceToNat]
      rw [Nat.mod_eq_of_lt (a := st.chunk.toNat * 10) (by lia), Nat.mod_eq_of_lt (by lia)]
    have hlt : st.chunk.toNat * 10 + (c.toNat - 48) < 10 ^ (st.count.toNat + 1) := by
      rw [Nat.pow_succ]; lia
    have hval : st.acc.toNat * 10 ^ (st.count.toNat + 1) +
        (st.chunk.toNat * 10 + (c.toNat - 48)) =
          Nat.ofDigitChars 10 ((p ++ [c]).filter (· != '_')) 0 := by
      rw [hf, ← hv, Nat.pow_succ]
      generalize st.acc.toNat = A
      generalize 10 ^ st.count.toNat = P
      rw [Nat.mul_add, Nat.add_assoc, Nat.mul_comm 10 (A * P), Nat.mul_assoc A P 10,
        Nat.mul_comm 10 st.chunk.toNat]
    by_cases h8 : st.count = 18
    · have h8' : st.count.toNat = 18 := by rw [h8]; rfl
      rw [DecimalState.step, ite_eq_right hu]
      simp only [h8, ↓reduceIte]
      refine ⟨by simp, by simp, ?_⟩
      rw [toNat_mulAddLimb, ← hval, hv', h8']
      simp
    · have hk' : (st.count + 1).toNat = st.count.toNat + 1 := by
        rw [UInt64.toNat_add]
        simp only [UInt64.reduceToNat]
        exact Nat.mod_eq_of_lt (by lia)
      have hne : st.count.toNat ≠ 18 := fun h' => h8 (UInt64.toNat_inj.1 (by rw [h']; rfl))
      rw [DecimalState.step, ite_eq_right hu]
      simp only [h8, ↓reduceIte]
      refine ⟨by rw [hk']; lia, by rw [hk', hv']; exact hlt, ?_⟩
      rw [hk', hv', hval]

private theorem inv_foldl (l p : List Char) (st : DecimalState)
    (hl : ∀ c ∈ l, c.isDigit = true ∨ c = '_') (h : st.Inv p) :
    (l.foldl DecimalState.step st).Inv (p ++ l) := by
  induction l generalizing st p with
  | nil => simpa using h
  | cons c cs ih =>
    rw [List.foldl_cons, show p ++ c :: cs = (p ++ [c]) ++ cs by simp]
    exact ih _ _ (fun c hc => hl c (by simp [hc])) (inv_step st p c (hl c (by simp)) h)

private theorem toNat_finish (st : DecimalState) (p : List Char) (h : st.Inv p) :
    st.finish.toNat = Nat.ofDigitChars 10 (p.filter (· != '_')) 0 := by
  obtain ⟨hk, hch, hv⟩ := h
  by_cases h0 : st.count = 0
  · have hc : st.chunk.toNat = 0 := by rw [h0] at hch; simpa using hch
    rw [DecimalState.finish, ite_eq_left h0, ← hv, h0, hc]
    simp
  · rw [DecimalState.finish, ite_eq_right h0]
    have hp : 10 ^ st.count.toNat ≤ 10 ^ 18 := Nat.pow_le_pow_right (by decide) (by lia)
    have hm : (10 ^ st.count.toNat).toUInt64.toNat = 10 ^ st.count.toNat := by
      simp only [Nat.toUInt64, UInt64.toNat_ofNat']
      exact Nat.mod_eq_of_lt (by lia)
    rw [toNat_mulAddLimb, hm, hv]

/--
The number with the decimal digits of `l`, skipping `_`, like `Nat.ofDigitChars` of the digits;
`l.foldl` and `String.foldl` read it without building lists.
-/
public theorem toNat_finish_foldl (l : List Char) (hl : ∀ c ∈ l, c.isDigit = true ∨ c = '_') :
    (l.foldl DecimalState.step .init).finish.toNat =
      Nat.ofDigitChars 10 (l.filter (· != '_')) 0 := by
  have h := inv_foldl l [] .init hl ⟨by decide, by decide, by
    simp [DecimalState.init, toNat_eq_valAt]⟩
  rw [List.nil_append] at h
  exact toNat_finish _ _ h

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
  (arr.foldl DecimalState.step .init start (start + len)).finish

private theorem foldl_chars (arr : Array Char) (start len : Nat) :
    arr.foldl DecimalState.step .init start (start + len) =
      (NatOps.chars arr start len).foldl DecimalState.step .init := by
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
    else some (s.foldl DecimalState.step .init).finish
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
        simp only [List.toList_toArray, List.mem_filter, bne_iff_ne, ne_eq] at hc
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

/-- The number of limbs from which `Num.toDecimal` uses divide and conquer. -/
public def strDC : Nat := 40

/-- The number of limbs' worth of digits from which `Num.ofDecimal?` uses divide and conquer. -/
public def parseDC : Nat := 512

/-- The decimal digits of `a`, like `Nat.repr a.toNat`. -/
public def Num.toDecimal (a : UInt64Array) : String := toDecimalWith strDC a

@[simp] public theorem Num.toDecimal_eq (a : UInt64Array) : Num.toDecimal a = Nat.repr a.toNat :=
  toDecimalWith_eq ..

/-- The number that a string of decimal digits denotes, like `String.toNat?`. -/
public def Num.ofDecimal? (s : String) : Option UInt64Array := ofDecimalWith parseDC s

@[simp] public theorem Num.ofDecimal?_eq (s : String) :
    (Num.ofDecimal? s).map UInt64Array.toNat = s.toNat? :=
  ofDecimalWith_eq ..

end MPN
