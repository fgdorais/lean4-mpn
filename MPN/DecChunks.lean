/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import MPN.LimbArray
public import MPN.Generic.Radix
public import MPN.IsNat
import Std.Data.String.ToNat
import all Init.Data.Repr

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

Both take quadratic time; on long numbers `toDecimalWith` and `ofDecimalWith` switch to divide and
conquer (`NatOps.toDec`, `NatOps.fromDec`), with the chunks as base cases. The state of reading is
a structure of the instance's, whose fields are unboxed: a structure over the limbs would box the
chunk at every character.
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
  k_lt : k < 256
  /-- `k`, as a word for counting digits. -/
  kU : UInt32
  toNat_kU : kU.toNat = k
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
  /-- A chunk as a word, for writing its digits. -/
  chunkWord : L → UInt64
  toNat_chunkWord : ∀ x, (chunkWord x).toNat = LA.val x
  /-- The chunk `0`. -/
  chunk0 : L
  val_chunk0 : LA.val chunk0 = 0
  /-- `10 c + d`, for `c < 10ᵏ⁻¹` and a digit `d`. -/
  push : L → UInt32 → L
  val_push : ∀ c d, LA.val c < 10 ^ (k - 1) → d.toNat ≤ 9 →
    LA.val (push c d) = LA.val c * 10 + d.toNat
  /-- The state of reading: the limbs of the chunks so far, the current chunk and its digits. -/
  St : Type
  mkSt : A → L → UInt32 → St
  acc : St → A
  chunk : St → L
  count : St → UInt32
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

/-- The character of a decimal digit `d < 10`, built directly: `'0' + d`. -/
@[inline, expose] public def digitW (d : UInt64) (h : d < 10) : Char :=
  ⟨48 + d.toUInt32, by
    have h' : d.toNat < 10 := UInt64.lt_iff_toNat_lt.1 h
    left
    rw [UInt32.toNat_add, UInt64.toNat_toUInt32]
    simp only [UInt32.reduceToNat]
    rw [Nat.mod_eq_of_lt (by lia), Nat.mod_eq_of_lt (by lia)]
    lia⟩

/-- `pushDigits` on a word: its digits by word arithmetic, each the character `48 + d`. -/
@[expose] public def pushDigitsW (s : String) : Nat → UInt64 → String
  | 0, _ => s
  | k + 1, d => (pushDigitsW s k (d / 10)).push (digitW (d % 10) (UInt64.mod_lt _ (by decide)))

private theorem digitChar_eq : ∀ x, x < 10 → Char.ofNat (48 + x) = Nat.digitChar x := by
  intro x hx
  match x, hx with
  | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ | 5, _ | 6, _ | 7, _ | 8, _ | 9, _ => simp [Nat.digitChar]

private theorem digitW_eq (d : UInt64) (h : d < 10) : digitW d h = Nat.digitChar d.toNat := by
  have h' : d.toNat < 10 := UInt64.lt_iff_toNat_lt.1 h
  rw [← digitChar_eq _ h', ← Char.ofNat_toNat (digitW d h)]
  congr 1
  show (48 + d.toUInt32).toNat = 48 + d.toNat
  rw [UInt32.toNat_add, UInt64.toNat_toUInt32]
  simp only [UInt32.reduceToNat]
  rw [Nat.mod_eq_of_lt (by lia), Nat.mod_eq_of_lt (by lia)]

public theorem pushDigitsW_eq (s : String) (k : Nat) (d : UInt64) :
    pushDigitsW s k d = pushDigits s k d.toNat := by
  induction k generalizing d with
  | zero => rfl
  | succ k ih =>
    rw [pushDigitsW, pushDigits, ih, digitW_eq, UInt64.toNat_div, UInt64.toNat_mod]
    simp only [UInt64.reduceToNat]

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

/-- `chunksLoop` with the chunks as words (`chunkWord`), which stay unboxed. -/
@[expose, specialize] public def chunksLoopW (a : A) (acc : List UInt64) : List UInt64 :=
  if _hz : O.isZero a = true then acc
  else
    let p := O.divRem a
    chunksLoopW p.1 (O.chunkWord p.2 :: acc)
termination_by vA a
decreasing_by
  rw [(O.divRem_spec a).1]
  rw [O.isZero_iff] at _hz
  exact Nat.div_lt_self (by lia) (Nat.one_lt_pow (by have := O.one_le_k; lia) (by decide))

private theorem chunksLoopW_eq (a : A) (acc : List UInt64) :
    (chunksLoopW a acc).map UInt64.toNat = chunksLoop a (acc.map UInt64.toNat) := by
  induction a, acc using chunksLoopW.induct (O := O) with
  | case1 a acc hz =>
    rw [chunksLoopW, dite_eq_left_of_eq_true (eq_true hz), chunksLoop,
      dite_eq_left_of_eq_true (eq_true hz)]
  | case2 a acc hz p ih =>
    rw [chunksLoopW, dite_eq_right hz, chunksLoop, dite_eq_right hz]
    simp only [p] at ih ⊢
    rw [ih, List.map_cons, O.toNat_chunkWord]

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

variable (A) in
/-- `renderChunks` on words, by `pushDigitsW`. -/
@[expose] public def renderChunksW : List UInt64 → String
  | [] => "0"
  | c :: cs => cs.foldl (fun s d => pushDigitsW s O.k d) (Nat.repr c.toNat)

private theorem renderChunksW_eq (l : List UInt64) :
    renderChunksW A l = renderChunks A (l.map UInt64.toNat) := by
  cases l with
  | nil => rfl
  | cons c cs =>
    rw [renderChunksW, List.map_cons, renderChunks, List.foldl_map]
    congr 1
    funext s d
    exact pushDigitsW_eq s O.k d

/-- The decimal digits of `a`, like `Nat.repr`, by chunks of `k` digits. -/
@[expose, specialize] public def toDecimal (a : A) : String := renderChunksW A (chunksLoopW a [])

private theorem toDecimal_eq_nat (a : A) :
    toDecimal a = renderChunks A (chunksLoop a []) := by
  rw [toDecimal, renderChunksW_eq, chunksLoopW_eq]
  rfl

public theorem toDecimal_eq (a : A) : toDecimal a = Nat.repr (vA a) := by
  rw [← String.toList_inj, Nat.toList_repr, toDecimal_eq_nat]
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
`k` digits, and `_` is skipped. The digits are counted in a word.
-/
@[expose, specialize] public def step (st : O.St) (c : Char) : O.St :=
  if c = '_' then
    st
  else
    let v := O.push (O.chunk st) (c.val - 48)
    if O.count st + 1 = O.kU then O.mkSt (O.mulAdd (O.acc st) O.base v) O.chunk0 0
    else O.mkSt (O.acc st) v (O.count st + 1)

/-- The number read: the limbs times `10ʲ` for the `j` digits of the last chunk, plus it. -/
@[expose, specialize] public def finish (st : O.St) : A :=
  if O.count st = 0 then O.acc st
  else O.mulAdd (O.acc st) (O.pow10 (O.count st).toNat) (O.chunk st)

/-- After reading `p`, the state holds the value of the digits of `p`. -/
private def Inv (st : O.St) (p : List Char) : Prop :=
  (O.count st).toNat < O.k ∧ LA.val (O.chunk st) < 10 ^ (O.count st).toNat ∧
    vA (O.acc st) * 10 ^ (O.count st).toNat + LA.val (O.chunk st) =
      Nat.ofDigitChars 10 (p.filter (· != '_')) 0

private theorem digit_toNat {c : Char} (h : c.isDigit = true) :
    (c.val - 48).toNat = c.toNat - 48 ∧ c.toNat - 48 ≤ 9 := by
  have := Char.isDigit_iff_toNat.1 h
  simp only [Char.reduceToNat] at this
  have hv : c.val.toNat = c.toNat := rfl
  have hle : (48 : UInt32) ≤ c.val := by rw [UInt32.le_iff_toNat_le, hv]; exact this.1
  rw [UInt32.toNat_sub_of_le _ _ hle, hv]
  exact ⟨rfl, by lia⟩

omit [LimbArray A L] in
private theorem toNat_succ (n : UInt32) (h : n.toNat < 256) : (n + 1).toNat = n.toNat + 1 := by
  rw [UInt32.toNat_add]
  simp only [UInt32.reduceToNat]
  exact Nat.mod_eq_of_lt (by lia)

private theorem inv_step (st : O.St) (p : List Char) (c : Char)
    (hc : c.isDigit = true ∨ c = '_') (h : Inv st p) : Inv (step st c) (p ++ [c]) := by
  obtain ⟨hk, hch, hv⟩ := h
  have hk' := toNat_succ (O.count st) (by have := O.k_lt; lia)
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
    have hpow : 10 ^ (O.count st).toNat ≤ 10 ^ (O.k - 1) :=
      Nat.pow_le_pow_right (by decide) (by lia)
    have hv' : LA.val (O.push (O.chunk st) (c.val - 48)) =
        LA.val (O.chunk st) * 10 + (c.toNat - 48) := by
      rw [O.val_push _ _ (by lia) (by rw [hd₁]; exact hd₂), hd₁]
    have hlt : LA.val (O.chunk st) * 10 + (c.toNat - 48) < 10 ^ ((O.count st).toNat + 1) := by
      rw [Nat.pow_succ]; lia
    have hval : vA (O.acc st) * 10 ^ ((O.count st).toNat + 1) +
        (LA.val (O.chunk st) * 10 + (c.toNat - 48)) =
          Nat.ofDigitChars 10 ((p ++ [c]).filter (· != '_')) 0 := by
      rw [hf, ← hv, Nat.pow_succ]
      generalize vA (O.acc st) = A
      generalize 10 ^ (O.count st).toNat = P
      rw [Nat.mul_add, Nat.add_assoc, Nat.mul_comm 10 (A * P), Nat.mul_assoc A P 10,
        Nat.mul_comm 10 (LA.val (O.chunk st))]
    have hiff : O.count st + 1 = O.kU ↔ (O.count st).toNat + 1 = O.k := by
      rw [← UInt32.toNat_inj, hk', O.toNat_kU]
    by_cases h8 : O.count st + 1 = O.kU
    · have h8' := hiff.1 h8
      rw [step, ite_eq_right hu]
      simp only [h8, ↓reduceIte]
      refine ⟨by rw [O.count_mkSt]; have := O.one_le_k; simp; lia, by
        rw [O.chunk_mkSt, O.count_mkSt, O.val_chunk0]; decide, ?_⟩
      rw [O.acc_mkSt, O.chunk_mkSt, O.count_mkSt, O.vA_mulAdd _ _ _ (by
        rw [O.val_base, hv', ← h8']; exact hlt), O.val_base, ← hval, hv', h8', O.val_chunk0]
      simp
    · have h8' : ¬(O.count st).toNat + 1 = O.k := fun e => h8 (hiff.2 e)
      rw [step, ite_eq_right hu]
      simp only [h8, ↓reduceIte]
      refine ⟨by rw [O.count_mkSt, hk']; lia,
        by rw [O.chunk_mkSt, O.count_mkSt, hk', hv']; exact hlt, ?_⟩
      rw [O.acc_mkSt, O.chunk_mkSt, O.count_mkSt, hk', hv', hval]

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
    simp only [UInt32.toNat_zero, Nat.pow_zero] at hch
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

/-! ## Decimal to limbs, by bytes

A string that `String.isNat` accepts is made of digits and `_`, characters of one byte each in
UTF-8, so that its bytes are its characters: `readB` reads them with `String.getUTF8Byte`, with the
limbs so far, the chunk and its digits in the arguments of the loop instead of a state.
-/

/-- An ASCII character is one byte of UTF-8, its value. -/
private theorem utf8Encode_ascii (l : List Char) (h : ∀ c ∈ l, c.val ≤ 127) :
    l.utf8Encode = (l.map fun c => c.val.toUInt8).toByteArray := by
  rw [List.utf8Encode]
  congr 1
  induction l with
  | nil => rfl
  | cons c cs ih =>
    rw [List.flatMap_cons, List.map_cons,
      String.utf8EncodeChar_eq_singleton (Char.utf8Size_eq_one_iff.2 (h c (by simp))),
      ih (fun d hd => h d (by simp [hd])), List.singleton_append]

/-- The bytes of a string of ASCII characters are its characters. -/
private theorem bytes_ascii (s : String) (h : ∀ c ∈ s.toList, c.val ≤ 127) :
    s.utf8ByteSize = s.toList.length ∧
      ∀ i (hi : i < s.toList.length) hb,
        s.getUTF8Byte ⟨i⟩ hb = (s.toList[i]'hi).val.toUInt8 := by
  have hb : s.toByteArray = (s.toList.map fun c => c.val.toUInt8).toByteArray := by
    rw [← String.utf8Encode_toList, utf8Encode_ascii _ h]
  refine ⟨?_, fun i hi _ => ?_⟩
  · show s.toByteArray.size = _
    rw [hb, List.size_toByteArray, List.length_map]
  · rw [String.getUTF8Byte_eq_getElem]
    simp only [hb, List.getElem_toByteArray, List.getElem_map]

/-- The byte of an ASCII character, as a word, is its value. -/
private theorem toUInt32_byte (c : Char) (h : c.val ≤ 127) : c.val.toUInt8.toUInt32 = c.val := by
  apply UInt32.toNat_inj.1
  rw [UInt8.toNat_toUInt32, UInt32.toNat_toUInt8,
    Nat.mod_eq_of_lt (by have := UInt32.le_iff_toNat_le.1 h; simp at this; lia)]

/-- The byte of an ASCII character is `95` exactly for `_`. -/
private theorem byte_eq_95 (c : Char) (h : c.val ≤ 127) : c.val.toUInt8 = 95 ↔ c = '_' := by
  constructor
  · intro hb
    apply Char.ext
    rw [← toUInt32_byte c h, hb]
    rfl
  · rintro rfl; rfl

/-- Reads the bytes of `s` from `i`, as `step` reads characters, then `finish`. -/
@[expose, specialize] public def readB (s : String) (i : Nat) (acc : A) (c : L) (n : UInt32) : A :=
  if h : i < s.utf8ByteSize then
    let b := s.getUTF8Byte ⟨i⟩ h
    if b = 95 then readB s (i + 1) acc c n
    else
      let v := O.push c (b.toUInt32 - 48)
      if n + 1 = O.kU then readB s (i + 1) (O.mulAdd acc O.base v) O.chunk0 0
      else readB s (i + 1) acc v (n + 1)
  else finish (O.mkSt acc c n)
termination_by s.utf8ByteSize - i

private theorem readB_eq (s : String) (h : ∀ c ∈ s.toList, c.val ≤ 127) (i : Nat) (acc : A)
    (c : L) (n : UInt32) :
    readB s i acc c n = finish ((s.toList.drop i).foldl step (O.mkSt acc c n)) := by
  obtain ⟨hsz, hbyte⟩ := bytes_ascii s h
  induction i, acc, c, n using readB.induct (O := O) s with
  | case1 i acc c n hi b hb ih =>
    rw [readB, dite_eq_left hi]
    simp only [b] at hb ih ⊢
    rw [ite_eq_left hb, ih]
    have hi' : i < s.toList.length := hsz ▸ hi
    rw [List.drop_eq_getElem_cons hi', List.foldl_cons]
    congr 2
    have hc := hbyte i hi' hi
    rw [hc] at hb
    have hv := h _ (List.getElem_mem hi')
    simp [step, (byte_eq_95 _ hv).1 hb]
  | case2 i acc c n hi b hb v hk ih =>
    rw [readB, dite_eq_left hi]
    simp only [b, v] at hb hk ih ⊢
    rw [ite_eq_right hb, ite_eq_left hk, ih]
    have hi' : i < s.toList.length := hsz ▸ hi
    rw [List.drop_eq_getElem_cons hi', List.foldl_cons]
    have hc := hbyte i hi' hi
    have hv := h _ (List.getElem_mem hi')
    rw [hc] at hb ⊢
    have hu : s.toList[i] ≠ '_' := fun e => hb ((byte_eq_95 _ hv).2 e)
    rw [toUInt32_byte _ hv]
    simp only [step, hu, ↓reduceIte, O.chunk_mkSt, O.count_mkSt, O.acc_mkSt, hk]
  | case3 i acc c n hi b hb v hk ih =>
    rw [readB, dite_eq_left hi]
    simp only [b, v] at hb hk ih ⊢
    rw [ite_eq_right hb, ite_eq_right hk, ih]
    have hi' : i < s.toList.length := hsz ▸ hi
    rw [List.drop_eq_getElem_cons hi', List.foldl_cons]
    have hc := hbyte i hi' hi
    have hv := h _ (List.getElem_mem hi')
    rw [hc] at hb ⊢
    have hu : s.toList[i] ≠ '_' := fun e => hb ((byte_eq_95 _ hv).2 e)
    rw [toUInt32_byte _ hv]
    simp only [step, hu, ↓reduceIte, O.chunk_mkSt, O.count_mkSt, O.acc_mkSt, hk]
  | case4 i acc c n hi =>
    rw [readB, dite_eq_right hi]
    have : s.toList.length ≤ i := by rw [← hsz]; lia
    rw [List.drop_eq_nil_of_le this, List.foldl_nil]

/-! ## Divide and conquer

Long numbers go through the base-generic divide and conquer of `MPN.Generic.Radix`
(`NatOps.toDec`, `NatOps.fromDec`) on a representation `α` of numbers that converts to the arrays
(`toA`) and back (`ofA`), with the chunks as its base cases.
-/

section DC

variable {α : Type} (o : NatOps α) (toA : α → A) (ofA : A → α)

/-- The decimal digits of `x` by chunks (`toDecimal`), the base case of `NatOps.toDec`. -/
@[expose, specialize] public def decBase (x : α) : String := toDecimal (toA x)

/--
The decimal digits of `a`: by chunks below `strDC` limbs (`toDecimal`), and by divide and conquer
from `strDC` limbs (`NatOps.toDec`), down to `T` limbs.
-/
@[expose, specialize] public def toDecimalWith (strDC T : Nat) (a : A) : String :=
  if strDC ≤ LA.size a then o.toDec (decBase toA) T (ofA a) else toDecimal a

public theorem toDecimalWith_eq (hto : ∀ x, vA (toA x) = o.val x)
    (hof : ∀ a, o.val (ofA a) = vA a) (strDC T : Nat) (a : A) :
    toDecimalWith o toA ofA strDC T a = Nat.repr (vA a) := by
  unfold toDecimalWith
  split
  · rw [← String.toList_inj, o.toDec_spec (decBase toA) T
      (fun x => by rw [decBase, toDecimal_eq, Nat.toList_repr, hto]), Nat.toList_repr, hof]
  · exact toDecimal_eq a

/-- The value of `len` digits of `arr` from `start` by chunks, the base case of `fromDec`. -/
@[expose, specialize] public def parseBase (arr : Array Char) (start len : Nat) : α :=
  ofA (finish (arr.foldl step (init A) start (start + len)))

omit [DecOps A L] in
private theorem foldl_chars {β : Type} (f : β → Char → β) (b : β) (arr : Array Char)
    (start len : Nat) :
    arr.foldl f b start (start + len) = (NatOps.chars arr start len).foldl f b := by
  rw [Array.foldl_eq_foldl_extract, ← Array.foldl_toList, Array.toList_extract,
    List.extract_eq_take_drop, Nat.add_sub_cancel_left, NatOps.chars]

private theorem parseBase_spec (hof : ∀ a, o.val (ofA a) = vA a) (arr : Array Char)
    (hd : ∀ c ∈ arr.toList, c.isDigit = true) (start len : Nat) :
    o.val (parseBase ofA arr start len) = Nat.ofDigitChars 10 (NatOps.chars arr start len) 0 := by
  have hc : ∀ c ∈ NatOps.chars arr start len, c.isDigit = true := fun c hc =>
    hd c (List.mem_of_mem_drop (List.mem_of_mem_take hc))
  rw [parseBase, hof, foldl_chars, vA_finish_foldl _ (fun c h => Or.inl (hc c h))]
  congr 1
  apply List.filter_eq_self.2
  intro c h
  have := hc c h
  simp only [bne_iff_ne, ne_eq]
  rintro rfl
  exact absurd this (by decide)

/--
The characters of `s` but `_`, as an array, by one fold over the string: no list of its
characters, filtered and then converted.
-/
@[expose] public def digitArray (s : String) : Array Char :=
  s.foldl (fun a c => if c = '_' then a else a.push c) (Array.mkEmpty s.utf8ByteSize)

omit [DecOps A L] in
public theorem digitArray_eq (s : String) :
    digitArray s = (s.toList.filter (· != '_')).toArray := by
  rw [digitArray, String.foldl_eq_foldl_toList]
  suffices h : ∀ (l : List Char) (a : Array Char),
      l.foldl (fun a c => if c = '_' then a else a.push c) a = a ++ (l.filter (· != '_')).toArray by
    rw [h]; simp
  intro l
  induction l with
  | nil => intro a; simp
  | cons c cs ih =>
    intro a
    rw [List.foldl_cons, ih, List.filter_cons]
    by_cases hc : c = '_'
    · simp [hc]
    · simp [hc]

/--
The limbs of a string of decimal digits that `String.isNat` accepts: from `k parseDC` digits by
divide and conquer (`NatOps.fromDec`, by chunks below `T` digits), and below by chunks.
-/
@[expose, specialize] public def ofDecimalWith (parseDC T : Nat) (s : String) : A :=
  if O.k * parseDC ≤ s.length then
    toA (o.fromDec (parseBase ofA) T (digitArray s))
  else readB s 0 O.empty O.chunk0 0

public theorem ofDecimalWith_spec (hto : ∀ x, vA (toA x) = o.val x)
    (hof : ∀ a, o.val (ofA a) = vA a) (parseDC T : Nat) (s : String) (h : s.isNat = true) :
    s.toNat? = some (vA (ofDecimalWith o toA ofA parseDC T s)) := by
  rw [String.toNat?_eq_some_ofDigitChars h, Option.some.injEq]
  unfold ofDecimalWith
  split
  · rw [digitArray_eq]
    have hd : ∀ c ∈ (s.toList.filter (· != '_')).toArray.toList, c.isDigit = true := by
      intro c hc
      simp only [List.mem_filter, bne_iff_ne, ne_eq] at hc
      rcases (String.isNat_iff.1 h).2.1 c hc.1 with h' | h'
      · exact h'
      · exact absurd h' hc.2
    rw [hto, o.fromDec_spec (parseBase ofA) T _
      (fun st ln _ => parseBase_spec o ofA hof _ hd st ln), List.toList_toArray]
  · have hd := (String.isNat_iff.1 h).2.1
    have ha : ∀ c ∈ s.toList, c.val ≤ 127 := fun c hc => by
      rcases hd c hc with h' | rfl
      · simp only [Char.isDigit, Bool.and_eq_true, decide_eq_true_eq] at h'
        exact UInt32.le_iff_toNat_le.2 (by have := UInt32.le_iff_toNat_le.1 h'.2; simp at this ⊢; lia)
      · decide
    rw [readB_eq s ha, List.drop_zero]
    exact (vA_finish_foldl _ hd).symm

end DC

end DecChunks

end MPN
