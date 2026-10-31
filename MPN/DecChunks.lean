/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import MPN.LimbArray
public import MPN.Generic.Radix
import Std.Data.String.ToNat

/-!
# Decimal strings by chunks

Like GMP's `mpn_get_str` and `mpn_set_str` below their thresholds, both directions work in chunks
of `k` decimal digits, the largest power of ten below the base of the limbs (`DecOps`):

* `toDecimal a` divides by `10ᵏ` until nothing is left, which gives the chunks from the least
  significant one up, then writes the top chunk as it is and each other one with exactly `k`
  digits. It equals `Nat.repr` of the value.
* `step`, folded over the characters, reads `k` digits at a time into a chunk and then multiplies
  the limbs so far by `10ᵏ` and adds the chunk; `finish` does the same with `10ʲ` for a last chunk
  of `j` digits. It skips `_` and equals `Nat.ofDigitChars` of the digits, the value that
  `String.toNat?` gives.

Both take quadratic time; the libraries switch to divide and conquer (`NatOps.toDec`,
`NatOps.fromDec`) on long numbers. The state of reading is a structure of the instance's, whose
fields are unboxed: a structure over the limbs would box the chunk at every character.
-/

namespace MPN

namespace DecChunks

variable {A L : Type} [LA : LimbArray A L]

/-- The value of an array. -/
@[expose] public def vA (a : A) : Nat := LimbArray.valAt a 0 (LA.size a)

end DecChunks

open DecChunks in
/--
The parts of decimal strings by chunks that depend on the limbs: `k` digits to a chunk, with
`10ᵏ` a limb (`base`); a zero test, one division by `10ᵏ` and one `a m + v`, on arrays; the
chunk being read, as a limb; and the state of reading, a structure of the instance's.
-/
public class DecOps (A : Type) (L : outParam Type) [LA : LimbArray A L] where
  /-- The digits of a chunk. -/
  k : Nat
  one_le_k : 1 ≤ k
  /-- `10ᵏ`. -/
  base : L
  val_base : LA.val base = 10 ^ k
  /-- `10ʲ`, for `j ≤ k`. -/
  pow10 : Nat → L
  val_pow10 : ∀ j, j ≤ k → LA.val (pow10 j) = 10 ^ j
  /-- `0`, as an array. -/
  empty : A
  vA_empty : vA empty = 0
  /-- Whether an array is zero. -/
  isZero : A → Bool
  isZero_iff : ∀ a, isZero a = true ↔ vA a = 0
  /-- The quotient and the remainder of `a` by `10ᵏ`. -/
  divRem : A → A × L
  divRem_spec : ∀ a, vA (divRem a).1 = vA a / 10 ^ k ∧ LA.val (divRem a).2 = vA a % 10 ^ k
  /-- `a m + v`, for `v < m`. -/
  mulAdd : A → L → L → A
  vA_mulAdd : ∀ a m v, LA.val v < LA.val m → vA (mulAdd a m v) = vA a * LA.val m + LA.val v
  /-- The chunk `0`. -/
  chunk0 : L
  val_chunk0 : LA.val chunk0 = 0
  /-- `10 c + d`, for `c < 10ᵏ⁻¹` and a digit `d`. -/
  push : L → UInt32 → L
  val_push : ∀ c d, LA.val c < 10 ^ (k - 1) → d.toNat ≤ 9 →
    LA.val (push c d) = LA.val c * 10 + d.toNat
  /-- The state of reading: the limbs of the chunks so far, the current chunk and its digits. -/
  St : Type
  mkSt : A → L → Nat → St
  acc : St → A
  chunk : St → L
  count : St → Nat
  acc_mkSt : ∀ a c n, acc (mkSt a c n) = a
  chunk_mkSt : ∀ a c n, chunk (mkSt a c n) = c
  count_mkSt : ∀ a c n, count (mkSt a c n) = n

namespace DecChunks

variable {A L : Type} [LA : LimbArray A L] [O : DecOps A L]

/-! ## Digits -/

/-- Pushes the `k` low decimal digits of `d`, with leading zeros, onto `s`. -/
@[expose] public def pushDigits (s : String) : Nat → Nat → String
  | 0, _ => s
  | k + 1, d => (pushDigits s k (d / 10)).push (Nat.digitChar (d % 10))

public theorem toList_pushDigits (s : String) (k d : Nat) :
    (pushDigits s k d).toList = s.toList ++ padDigits k d := by
  induction k generalizing d with
  | zero => simp [pushDigits, padDigits]
  | succ k ih => rw [pushDigits, String.toList_push, ih, padDigits, List.append_assoc]

/-! ## Limbs to decimal -/

variable (A) in
/-- The value of chunks of `k` digits, most significant first, after `v`. -/
@[expose] public def ofChunks (l : List Nat) (v : Nat) : Nat :=
  l.foldl (fun v d => 10 ^ O.k * v + d) v

private theorem ofChunks_eq (l : List Nat) (v : Nat) :
    ofChunks A l v = 10 ^ (O.k * l.length) * v + ofChunks A l 0 := by
  induction l generalizing v with
  | nil => simp [ofChunks]
  | cons x xs ih =>
    have e (w : Nat) : ofChunks A (x :: xs) w = ofChunks A xs (10 ^ O.k * w + x) := rfl
    rw [e, e, ih, ih (10 ^ O.k * 0 + x), List.length_cons, Nat.mul_succ, Nat.pow_add,
      Nat.mul_zero, Nat.zero_add, Nat.mul_add, Nat.mul_assoc, Nat.add_assoc]

/--
Puts the chunks of `k` digits of `a`, most significant first, in front of `acc`, by dividing by
`10ᵏ` until nothing is left.
-/
@[expose, specialize] public def chunksLoop (a : A) (acc : List Nat) : List Nat :=
  if _hz : O.isZero a = true then acc
  else
    let p := O.divRem a
    chunksLoop p.1 (LA.val p.2 :: acc)
termination_by vA a
decreasing_by
  rw [(O.divRem_spec a).1]
  rw [O.isZero_iff] at _hz
  exact Nat.div_lt_self (by lia) (Nat.one_lt_pow (by have := O.one_le_k; lia) (by decide))

private theorem chunksLoop_spec (a : A) (acc : List Nat) (hacc : ∀ d ∈ acc, d < 10 ^ O.k) :
    (∀ d ∈ chunksLoop a acc, d < 10 ^ O.k) ∧
      ofChunks A (chunksLoop a acc) 0 = 10 ^ (O.k * acc.length) * vA a + ofChunks A acc 0 ∧
      (0 < vA a → ∃ c cs, chunksLoop a acc = c :: cs ∧ 0 < c) := by
  have hb : 0 < 10 ^ O.k := Nat.pow_pos (by decide)
  induction a, acc using chunksLoop.induct (O := O) with
  | case1 a acc hz =>
    rw [chunksLoop, dite_eq_left_of_eq_true (eq_true hz)]
    rw [O.isZero_iff] at hz
    rw [hz]
    exact ⟨hacc, by simp, fun h => absurd h (Nat.lt_irrefl 0)⟩
  | case2 a acc hz p ih =>
    rw [chunksLoop, dite_eq_right hz]
    have ⟨hq, hr⟩ := O.divRem_spec a
    have hpos : 0 < vA a := by
      rw [O.isZero_iff] at hz; lia
    have hmod : vA a % 10 ^ O.k < 10 ^ O.k := Nat.mod_lt _ hb
    obtain ⟨ih₁, ih₂, ih₃⟩ := ih (fun d hd => by
      rcases List.mem_cons.1 hd with rfl | hd
      · simp only [p]; rw [hr]; exact hmod
      · exact hacc d hd)
    simp only [p] at ih₁ ih₂ ih₃ ⊢
    refine ⟨ih₁, ?_, fun _ => ?_⟩
    · have hc : ofChunks A (vA a % 10 ^ O.k :: acc) 0 =
          10 ^ (O.k * acc.length) * (vA a % 10 ^ O.k) + ofChunks A acc 0 := by
        rw [show ofChunks A (vA a % 10 ^ O.k :: acc) 0 = ofChunks A acc (vA a % 10 ^ O.k) by
          simp [ofChunks], ofChunks_eq]
      rw [ih₂, hq, List.length_cons, hr, hc, Nat.mul_succ, Nat.pow_add]
      have := Nat.div_add_mod (vA a) (10 ^ O.k)
      generalize vA a / 10 ^ O.k = q at *
      generalize vA a % 10 ^ O.k = r at *
      generalize 10 ^ (O.k * acc.length) = P
      rw [← this, Nat.mul_add, Nat.mul_assoc, Nat.add_assoc]
    · by_cases hq0 : vA a / 10 ^ O.k = 0
      · have hs : O.isZero (O.divRem a).1 = true := by
          rw [O.isZero_iff, hq, hq0]
        rw [chunksLoop, dite_eq_left_of_eq_true (eq_true hs)]
        exact ⟨_, _, rfl, by rw [hr]; have := Nat.div_add_mod (vA a) (10 ^ O.k); lia⟩
      · exact ih₃ (by rw [hq]; lia)

variable (A) in
/-- Writes the top chunk `c` as it is and each other chunk with `k` digits. -/
@[expose] public def renderChunks : List Nat → String
  | [] => "0"
  | c :: cs => cs.foldl (fun s d => pushDigits s O.k d) (Nat.repr c)

private theorem toList_foldl_pushDigits (cs : List Nat) (s : String) (v : Nat) (hv : 0 < v)
    (hs : s.toList = Nat.toDigits 10 v) (hcs : ∀ d ∈ cs, d < 10 ^ O.k) :
    (cs.foldl (fun s d => pushDigits s O.k d) s).toList = Nat.toDigits 10 (ofChunks A cs v) := by
  induction cs generalizing s v with
  | nil => simpa [ofChunks] using hs
  | cons d ds ih =>
    rw [List.foldl_cons, show ofChunks A (d :: ds) v = ofChunks A ds (10 ^ O.k * v + d) from rfl]
    apply ih _ _ (by have := Nat.mul_pos (Nat.pow_pos (n := O.k) (by decide : 0 < 10)) hv; lia)
    · rw [toList_pushDigits, hs, toDigits_pow_mul_add O.k hv (hcs d (by simp))]
    · exact fun d' hd' => hcs d' (by simp [hd'])

/-- The decimal digits of `a`, like `Nat.repr`, by chunks of `k` digits. -/
@[expose, specialize] public def toDecimal (a : A) : String := renderChunks A (chunksLoop a [])

public theorem toDecimal_eq (a : A) : toDecimal a = Nat.repr (vA a) := by
  rw [← String.toList_inj, Nat.toList_repr, toDecimal]
  by_cases hz : O.isZero a = true
  · rw [chunksLoop, dite_eq_left_of_eq_true (eq_true hz)]
    rw [O.isZero_iff] at hz
    rw [hz, renderChunks, Nat.toDigits_zero]
    rfl
  · obtain ⟨hlt, hv, hpos⟩ := chunksLoop_spec a [] (by simp)
    obtain ⟨c, cs, he, hc⟩ := hpos (by rw [O.isZero_iff] at hz; lia)
    rw [he] at hlt hv
    simp only [List.length_nil, Nat.mul_zero, Nat.pow_zero, Nat.one_mul,
      show ofChunks A [] 0 = 0 from rfl, Nat.add_zero] at hv
    rw [he, renderChunks, ← hv, show ofChunks A (c :: cs) 0 = ofChunks A cs c by simp [ofChunks]]
    exact toList_foldl_pushDigits cs _ c hc Nat.toList_repr
      (fun d hd => hlt d (List.mem_cons_of_mem _ hd))

/-! ## Decimal to limbs -/

variable (A) in
/-- The state before any digit. -/
@[expose, specialize] public def init : O.St := O.mkSt O.empty O.chunk0 0

/--
Reads one character: a digit goes into the current chunk, which moves into the limbs when it has
`k` digits, and `_` is skipped.
-/
@[expose, specialize] public def step (st : O.St) (c : Char) : O.St :=
  if c = '_' then
    st
  else
    let v := O.push (O.chunk st) (c.val - 48)
    if O.count st + 1 = O.k then O.mkSt (O.mulAdd (O.acc st) O.base v) O.chunk0 0
    else O.mkSt (O.acc st) v (O.count st + 1)

/-- The number read: the limbs times `10ʲ` for the `j` digits of the last chunk, plus that chunk. -/
@[expose, specialize] public def finish (st : O.St) : A :=
  if O.count st = 0 then O.acc st else O.mulAdd (O.acc st) (O.pow10 (O.count st)) (O.chunk st)

/-- After reading `p`, the state holds the value of the digits of `p`. -/
private def Inv (st : O.St) (p : List Char) : Prop :=
  O.count st < O.k ∧ LA.val (O.chunk st) < 10 ^ O.count st ∧
    vA (O.acc st) * 10 ^ O.count st + LA.val (O.chunk st) =
      Nat.ofDigitChars 10 (p.filter (· != '_')) 0

private theorem digit_toNat {c : Char} (h : c.isDigit = true) :
    (c.val - 48).toNat = c.toNat - 48 ∧ c.toNat - 48 ≤ 9 := by
  have := Char.isDigit_iff_toNat.1 h
  simp only [Char.reduceToNat] at this
  have hv : c.val.toNat = c.toNat := rfl
  have hle : (48 : UInt32) ≤ c.val := by rw [UInt32.le_iff_toNat_le, hv]; exact this.1
  rw [UInt32.toNat_sub_of_le _ _ hle, hv]
  exact ⟨rfl, by lia⟩

private theorem inv_step (st : O.St) (p : List Char) (c : Char)
    (hc : c.isDigit = true ∨ c = '_') (h : Inv st p) : Inv (step st c) (p ++ [c]) := by
  obtain ⟨hk, hch, hv⟩ := h
  by_cases hu : c = '_'
  · subst hu
    rw [step, ite_eq_left rfl, Inv, List.filter_append]
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
    have hpow : 10 ^ O.count st ≤ 10 ^ (O.k - 1) := Nat.pow_le_pow_right (by decide) (by lia)
    have hv' : LA.val (O.push (O.chunk st) (c.val - 48)) =
        LA.val (O.chunk st) * 10 + (c.toNat - 48) := by
      rw [O.val_push _ _ (by lia) (by rw [hd₁]; exact hd₂), hd₁]
    have hlt : LA.val (O.chunk st) * 10 + (c.toNat - 48) < 10 ^ (O.count st + 1) := by
      rw [Nat.pow_succ]; lia
    have hval : vA (O.acc st) * 10 ^ (O.count st + 1) +
        (LA.val (O.chunk st) * 10 + (c.toNat - 48)) =
          Nat.ofDigitChars 10 ((p ++ [c]).filter (· != '_')) 0 := by
      rw [hf, ← hv, Nat.pow_succ]
      generalize vA (O.acc st) = A
      generalize 10 ^ O.count st = P
      rw [Nat.mul_add, Nat.add_assoc, Nat.mul_comm 10 (A * P), Nat.mul_assoc A P 10,
        Nat.mul_comm 10 (LA.val (O.chunk st))]
    by_cases h8 : O.count st + 1 = O.k
    · rw [step, ite_eq_right hu]
      simp only [h8, ↓reduceIte]
      refine ⟨by rw [O.count_mkSt]; have := O.one_le_k; lia, by
        rw [O.chunk_mkSt, O.count_mkSt, O.val_chunk0]; decide, ?_⟩
      rw [O.acc_mkSt, O.chunk_mkSt, O.count_mkSt, O.vA_mulAdd _ _ _ (by
        rw [O.val_base, hv', ← h8]; exact hlt), O.val_base, ← hval, hv', h8, O.val_chunk0]
      simp
    · rw [step, ite_eq_right hu]
      simp only [h8, ↓reduceIte]
      refine ⟨by rw [O.count_mkSt]; lia, by rw [O.chunk_mkSt, O.count_mkSt, hv']; exact hlt, ?_⟩
      rw [O.acc_mkSt, O.chunk_mkSt, O.count_mkSt, hv', hval]

private theorem inv_foldl (l p : List Char) (st : O.St)
    (hl : ∀ c ∈ l, c.isDigit = true ∨ c = '_') (h : Inv st p) :
    Inv (l.foldl step st) (p ++ l) := by
  induction l generalizing st p with
  | nil => simpa using h
  | cons c cs ih =>
    rw [List.foldl_cons, show p ++ c :: cs = (p ++ [c]) ++ cs by simp]
    exact ih _ _ (fun c hc => hl c (by simp [hc])) (inv_step st p c (hl c (by simp)) h)

private theorem vA_finish (st : O.St) (p : List Char) (h : Inv st p) :
    vA (finish st) = Nat.ofDigitChars 10 (p.filter (· != '_')) 0 := by
  obtain ⟨hk, hch, hv⟩ := h
  by_cases h0 : O.count st = 0
  · rw [h0] at hch hv
    rw [finish, ite_eq_left h0, ← hv]
    simp only [Nat.pow_zero] at hch
    simp [show LA.val (O.chunk st) = 0 by lia]
  · rw [finish, ite_eq_right h0, O.vA_mulAdd _ _ _ (by rw [O.val_pow10 _ (by lia)]; exact hch),
      O.val_pow10 _ (by lia), hv]

/--
The number with the decimal digits of `l`, skipping `_`, like `Nat.ofDigitChars` of the digits;
`l.foldl` and `String.foldl` read it without building lists.
-/
public theorem vA_finish_foldl (l : List Char) (hl : ∀ c ∈ l, c.isDigit = true ∨ c = '_') :
    vA (finish (l.foldl step (init A))) = Nat.ofDigitChars 10 (l.filter (· != '_')) 0 := by
  have h := inv_foldl l [] (init A) hl ⟨by rw [init, O.count_mkSt]; exact O.one_le_k, by
    rw [init, O.chunk_mkSt, O.count_mkSt, O.val_chunk0]; decide, by
    rw [init, O.acc_mkSt, O.chunk_mkSt, O.count_mkSt, O.vA_empty, O.val_chunk0]; simp⟩
  rw [List.nil_append] at h
  exact vA_finish _ _ h

end DecChunks

end MPN
