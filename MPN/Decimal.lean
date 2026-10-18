/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import MPN.Add
public import MPN.Div.Limb
public import MPN.Mul.Limb

/-!
# Decimal strings

Like GMP's `mpn_get_str` and `mpn_set_str` below their thresholds, both directions work in chunks
of nine decimal digits, the largest power of ten below `β`:

* `toDecimal a` divides by `10⁹` with `divRem1` until nothing is left, which gives the chunks
  from the least significant one up, then writes the top chunk as it is and each other one with
  exactly nine digits. It equals `Nat.repr (toNat a)`.
* `DecimalState.step`, folded over the characters, reads nine digits at a time into a chunk
  and then multiplies the limbs so far by `10⁹` and adds the chunk; `finish` does the same with
  `10ᵏ` for a last chunk of `k` digits. It skips `_` and equals `Nat.ofDigitChars` of the
  digits, the value that `String.toNat?` gives.

Both take quadratic time.
-/

open ScalarArray

namespace MPN

/-! ## Digits -/

/-- The `k` low decimal digits of `d`, with leading zeros. -/
def padDigits : Nat → Nat → List Char
  | 0, _ => []
  | k + 1, d => padDigits k (d / 10) ++ [Nat.digitChar (d % 10)]

/-- The digits of `10ᵏ n + d` are those of `n` followed by the `k` digits of `d`. -/
theorem toDigits_pow_mul_add (k : Nat) {n d : Nat} (hn : 0 < n) (hd : d < 10 ^ k) :
    Nat.toDigits 10 (10 ^ k * n + d) = Nat.toDigits 10 n ++ padDigits k d := by
  induction k generalizing d with
  | zero =>
    rw [Nat.pow_zero] at hd
    rw [show d = 0 by lia, padDigits, Nat.pow_zero, Nat.one_mul, Nat.add_zero, List.append_nil]
  | succ k ih =>
    have hpos : 0 < 10 ^ k * n := Nat.mul_pos (Nat.pow_pos (by decide)) hn
    have e : 10 ^ (k + 1) * n + d = 10 * (10 ^ k * n + d / 10) + d % 10 := by
      rw [Nat.pow_succ, Nat.mul_comm (10 ^ k) 10, Nat.mul_assoc]; lia
    rw [e, ← Nat.toDigits_append_toDigits (by decide) (by lia) (Nat.mod_lt _ (by decide)),
      Nat.toDigits_of_lt_base (Nat.mod_lt _ (by decide)),
      ih (by rw [Nat.pow_succ] at hd; lia), padDigits, List.append_assoc]

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

/-- `10⁹`, the largest power of ten below `β`. -/
abbrev chunkBase : UInt32 := 1000000000

/-- The value of chunks of nine digits, most significant first, after `v`. -/
def ofChunks (l : List Nat) (v : Nat) : Nat := l.foldl (fun v d => 10 ^ 9 * v + d) v

theorem ofChunks_eq (l : List Nat) (v : Nat) :
    ofChunks l v = 10 ^ (9 * l.length) * v + ofChunks l 0 := by
  induction l generalizing v with
  | nil => simp [ofChunks]
  | cons x xs ih =>
    have e (w : Nat) : ofChunks (x :: xs) w = ofChunks xs (10 ^ 9 * w + x) := rfl
    rw [e, e, ih, ih (10 ^ 9 * 0 + x), List.length_cons, Nat.mul_succ, Nat.pow_add,
      Nat.mul_zero, Nat.zero_add, Nat.mul_add, Nat.mul_assoc, Nat.add_assoc]

private theorem pos_of_isTrimmed {a : UInt32Array} (h : isTrimmed a = true) (hz : a.size ≠ 0) :
    0 < toNat a := by
  rw [toNat_toSlice]
  rw [isTrimmed_iff] at h
  exact h.ofLimbs_pos (by simpa [← List.length_eq_zero_iff] using hz)

private theorem divRem1_chunk (a : UInt32Array) :
    toNat (divRem1 a chunkBase).1 = toNat a / 10 ^ 9 ∧
      (divRem1 a chunkBase).2.toNat = toNat a % 10 ^ 9 := by
  have ⟨h, hr⟩ := divRem1_spec a chunkBase (by decide)
  have hd : chunkBase.toNat = 10 ^ 9 := rfl
  rw [hd] at h hr
  constructor
  · rw [← h, Nat.add_comm, Nat.add_mul_div_right _ _ (by decide), Nat.div_eq_of_lt hr,
      Nat.zero_add]
  · rw [← h, Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hr]

/--
Puts the chunks of nine digits of `a`, most significant first, in front of `acc`, by dividing by
`10⁹` until nothing is left.
-/
def chunksLoop (a : UInt32Array) (_h : isTrimmed a = true) (acc : List Nat) : List Nat :=
  if _hz : a.size = 0 then
    acc
  else
    let p := divRem1 a chunkBase
    chunksLoop (trim p.1) (isTrimmed_trim _) (p.2.toNat :: acc)
termination_by toNat a
decreasing_by
  rw [toNat_trim, (divRem1_chunk a).1]
  exact Nat.div_lt_self (pos_of_isTrimmed _h _hz) (by decide)

private theorem chunksLoop_spec (a : UInt32Array) (h : isTrimmed a = true) (acc : List Nat)
    (hacc : ∀ d ∈ acc, d < 10 ^ 9) :
    (∀ d ∈ chunksLoop a h acc, d < 10 ^ 9) ∧
      ofChunks (chunksLoop a h acc) 0 = 10 ^ (9 * acc.length) * toNat a + ofChunks acc 0 ∧
      (0 < toNat a → ∃ c cs, chunksLoop a h acc = c :: cs ∧ 0 < c) := by
  induction a, h, acc using chunksLoop.induct with
  | case1 a h acc hz =>
    rw [chunksLoop, dite_eq_left hz, toNat_of_size_eq_zero (by simpa using hz)]
    exact ⟨hacc, by simp, fun h => absurd h (Nat.lt_irrefl 0)⟩
  | case2 a h acc hz p ih =>
    rw [chunksLoop, dite_eq_right hz]
    have ⟨hq, hr⟩ := divRem1_chunk a
    have hpos := pos_of_isTrimmed h hz
    have hmod : toNat a % 10 ^ 9 < 10 ^ 9 := Nat.mod_lt _ (by decide)
    obtain ⟨ih₁, ih₂, ih₃⟩ := ih (fun d hd => by
      rcases List.mem_cons.1 hd with rfl | hd
      · rw [hr]; exact hmod
      · exact hacc d hd)
    refine ⟨ih₁, ?_, fun _ => ?_⟩
    · -- One more chunk below the rest: `a = 10⁹ (a / 10⁹) + a % 10⁹`.
      have hc : ofChunks (toNat a % 10 ^ 9 :: acc) 0 =
          10 ^ (9 * acc.length) * (toNat a % 10 ^ 9) + ofChunks acc 0 := by
        rw [show ofChunks (toNat a % 10 ^ 9 :: acc) 0 = ofChunks acc (toNat a % 10 ^ 9) by
          simp [ofChunks], ofChunks_eq]
      rw [ih₂, toNat_trim, hq, List.length_cons, hr, hc, Nat.mul_succ, Nat.pow_add]
      have := Nat.div_add_mod (toNat a) (10 ^ 9)
      generalize toNat a / 10 ^ 9 = q at *
      generalize toNat a % 10 ^ 9 = r at *
      generalize 10 ^ (9 * acc.length) = P
      rw [← this, Nat.mul_add, Nat.mul_assoc, Nat.add_assoc]
    · by_cases hq0 : toNat a / 10 ^ 9 = 0
      · -- The last division: the quotient is zero, so the remainder is all of `a`.
        have hs : (trim p.1).size = 0 := Decidable.byContradiction fun hs' => by
          have := pos_of_isTrimmed (isTrimmed_trim p.1) hs'
          rw [toNat_trim, hq] at this
          lia
        rw [chunksLoop, dite_eq_left hs]
        exact ⟨_, _, rfl, by rw [hr]; lia⟩
      · exact ih₃ (by rw [toNat_trim, hq]; lia)

/-- Writes the top chunk `c` as it is and each other chunk with nine digits. -/
def renderChunks : List Nat → String
  | [] => "0"
  | c :: cs => cs.foldl (fun s d => pushDigits s 9 d) (Nat.repr c)

private theorem toList_foldl_pushDigits (cs : List Nat) (s : String) (v : Nat) (hv : 0 < v)
    (hs : s.toList = Nat.toDigits 10 v) (hcs : ∀ d ∈ cs, d < 10 ^ 9) :
    (cs.foldl (fun s d => pushDigits s 9 d) s).toList = Nat.toDigits 10 (ofChunks cs v) := by
  induction cs generalizing s v with
  | nil => simpa [ofChunks] using hs
  | cons d ds ih =>
    rw [List.foldl_cons, show ofChunks (d :: ds) v = ofChunks ds (10 ^ 9 * v + d) from rfl]
    apply ih _ _ (by have := Nat.mul_pos (show 0 < 10 ^ 9 by decide) hv; lia)
    · rw [toList_pushDigits, hs, toDigits_pow_mul_add 9 hv (hcs d (by simp))]
    · exact fun d' hd' => hcs d' (by simp [hd'])

/-- The decimal digits of `a`, like `Nat.repr`. -/
public def toDecimal (a : UInt32Array) (h : isTrimmed a = true) : String :=
  renderChunks (chunksLoop a h [])

public theorem toDecimal_eq (a : UInt32Array) (h : isTrimmed a = true) :
    toDecimal a h = Nat.repr (toNat a) := by
  rw [← String.toList_inj, Nat.toList_repr, toDecimal]
  by_cases hz : a.size = 0
  · rw [chunksLoop, dite_eq_left hz, toNat_of_size_eq_zero (by simpa using hz), renderChunks,
      Nat.toDigits_zero]
    rfl
  · obtain ⟨hlt, hv, hpos⟩ := chunksLoop_spec a h [] (by simp)
    obtain ⟨c, cs, he, hc⟩ := hpos (pos_of_isTrimmed h hz)
    rw [he] at hlt hv
    simp only [List.length_nil, Nat.mul_zero, Nat.pow_zero, Nat.one_mul,
      show ofChunks [] 0 = 0 from rfl, Nat.add_zero] at hv
    rw [he, renderChunks, ← hv, show ofChunks (c :: cs) 0 = ofChunks cs c by simp [ofChunks]]
    exact toList_foldl_pushDigits cs _ c hc Nat.toList_repr
      (fun d hd => hlt d (List.mem_cons_of_mem _ hd))

/-! ## Decimal to limbs -/

/-- `a m + v`, trimmed. -/
def mulAddLimb (a : UInt32Array) (m v : UInt32) : UInt32Array :=
  trim (addInto (mulRow a m) 0 (limbArray v))

private theorem toNat_mulAddLimb (a : UInt32Array) (m v : UInt32) (hv : v.toNat < m.toNat) :
    toNat (mulAddLimb a m v) = toNat a * m.toNat + v.toNat := by
  have hA : toNat a < 2 ^ (32 * a.size) := by
    have := toNat_lt a
    simpa using this
  have hfit : toNat (mulRow a m) + 2 ^ (32 * 0) * toNat (limbArray v) <
      2 ^ (32 * (mulRow a m).size) := by
    rw [toNat_mulRow, toNat_limbArray, size_mulRow, Nat.mul_zero, Nat.pow_zero, Nat.one_mul,
      UInt32Array.size_toSlice, Nat.min_self, Nat.sub_zero, Nat.mul_succ, Nat.pow_add]
    -- `a m + v < (a + 1) m ≤ β^n m < β^(n + 1)`.
    have h₁ : toNat a * m.toNat + v.toNat < (toNat a + 1) * m.toNat := by
      rw [Nat.succ_mul]; lia
    have h₂ : (toNat a + 1) * m.toNat ≤ 2 ^ (32 * a.size) * m.toNat := Nat.mul_le_mul_right _ hA
    have h₃ : 2 ^ (32 * a.size) * m.toNat ≤ 2 ^ (32 * a.size) * 2 ^ 32 :=
      Nat.mul_le_mul_left _ (Nat.le_of_lt m.toNat_lt)
    lia
  rw [mulAddLimb, toNat_trim, toNat_addInto_of_lt _ _ _ (by simp [limbArray]) hfit,
    toNat_mulRow, toNat_limbArray, Nat.mul_zero, Nat.pow_zero, Nat.one_mul]

/--
The state of reading decimal digits: the limbs of the chunks so far, and the value of the
`count < 9` digits of the current chunk.
-/
public structure DecimalState where
  acc : UInt32Array
  chunk : UInt32
  count : UInt32

/-- The state before any digit. -/
public def DecimalState.init : DecimalState := ⟨.empty, 0, 0⟩

/--
Reads one character: a digit goes into the current chunk, which moves into the limbs when it has
nine digits, and `_` is skipped.
-/
public def DecimalState.step (st : DecimalState) (c : Char) : DecimalState :=
  if c = '_' then
    st
  else
    let v := st.chunk * 10 + (c.val - 48)
    if st.count = 8 then ⟨mulAddLimb st.acc 1000000000 v, 0, 0⟩ else ⟨st.acc, v, st.count + 1⟩

/-- The number read: the limbs times `10ᵏ` for the `k` digits of the last chunk, plus that chunk. -/
public def DecimalState.finish (st : DecimalState) : UInt32Array :=
  if st.count = 0 then st.acc else mulAddLimb st.acc (10 ^ st.count.toNat).toUInt32 st.chunk

/-- After reading `p`, the state holds the value of the digits of `p`. -/
def DecimalState.Inv (st : DecimalState) (p : List Char) : Prop :=
  st.count.toNat < 9 ∧ st.chunk.toNat < 10 ^ st.count.toNat ∧
    toNat st.acc * 10 ^ st.count.toNat + st.chunk.toNat =
      Nat.ofDigitChars 10 (p.filter (· != '_')) 0

private theorem digit_toNat {c : Char} (h : c.isDigit = true) :
    (c.val - 48).toNat = c.toNat - 48 ∧ c.toNat - 48 ≤ 9 := by
  have := Char.isDigit_iff_toNat.1 h
  simp only [Char.reduceToNat] at this
  have hv : c.val.toNat = c.toNat := rfl
  have hle : (48 : UInt32) ≤ c.val := by rw [UInt32.le_iff_toNat_le, hv]; exact this.1
  rw [UInt32.toNat_sub_of_le _ _ hle, hv]
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
    -- The new chunk `10 chunk + d` has one more digit and still fits in a limb.
    have hpow : 10 ^ st.count.toNat ≤ 10 ^ 8 := Nat.pow_le_pow_right (by decide) (by lia)
    have hv' : (st.chunk * 10 + (c.val - 48)).toNat = st.chunk.toNat * 10 + (c.toNat - 48) := by
      have hc8 : st.chunk.toNat < 10 ^ 8 := by lia
      rw [UInt32.toNat_add, UInt32.toNat_mul, hd₁]
      simp only [UInt32.reduceToNat]
      rw [Nat.mod_eq_of_lt (a := st.chunk.toNat * 10) (by lia), Nat.mod_eq_of_lt (by lia)]
    have hlt : st.chunk.toNat * 10 + (c.toNat - 48) < 10 ^ (st.count.toNat + 1) := by
      rw [Nat.pow_succ]; lia
    have hval : toNat st.acc * 10 ^ (st.count.toNat + 1) + (st.chunk.toNat * 10 + (c.toNat - 48)) =
        Nat.ofDigitChars 10 ((p ++ [c]).filter (· != '_')) 0 := by
      rw [hf, ← hv, Nat.pow_succ]
      generalize toNat st.acc = A
      generalize 10 ^ st.count.toNat = P
      rw [Nat.mul_add, Nat.add_assoc, Nat.mul_comm 10 (A * P), Nat.mul_assoc A P 10,
        Nat.mul_comm 10 st.chunk.toNat]
    by_cases h8 : st.count = 8
    · have h8' : st.count.toNat = 8 := by rw [h8]; rfl
      rw [DecimalState.step, ite_eq_right hu]
      simp only [h8, ↓reduceIte]
      refine ⟨by simp, by simp, ?_⟩
      rw [toNat_mulAddLimb _ _ _ (by rw [hv']; rw [h8'] at hlt; exact hlt), ← hval, hv', h8']
      simp
    · have hk' : (st.count + 1).toNat = st.count.toNat + 1 := by
        rw [UInt32.toNat_add]
        simp only [UInt32.reduceToNat]
        exact Nat.mod_eq_of_lt (by lia)
      have hne : st.count.toNat ≠ 8 := fun h' => h8 (UInt32.toNat_inj.1 (by rw [h']; rfl))
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
    toNat st.finish = Nat.ofDigitChars 10 (p.filter (· != '_')) 0 := by
  obtain ⟨hk, hch, hv⟩ := h
  by_cases h0 : st.count = 0
  · have hc : st.chunk.toNat = 0 := by rw [h0] at hch; simpa using hch
    rw [DecimalState.finish, ite_eq_left h0, ← hv, h0, hc]
    simp
  · rw [DecimalState.finish, ite_eq_right h0]
    have hp : 10 ^ st.count.toNat ≤ 10 ^ 8 := Nat.pow_le_pow_right (by decide) (by lia)
    have hm : (10 ^ st.count.toNat).toUInt32.toNat = 10 ^ st.count.toNat := by
      simp only [Nat.toUInt32, UInt32.toNat_ofNat']
      exact Nat.mod_eq_of_lt (by lia)
    rw [toNat_mulAddLimb _ _ _ (by rw [hm]; exact hch), hm, hv]

/--
The number with the decimal digits of `l`, skipping `_`, like `Nat.ofDigitChars` of the digits;
`l.foldl` and `String.foldl` read it without building lists.
-/
public theorem toNat_finish_foldl (l : List Char) (hl : ∀ c ∈ l, c.isDigit = true ∨ c = '_') :
    toNat (l.foldl DecimalState.step .init).finish =
      Nat.ofDigitChars 10 (l.filter (· != '_')) 0 := by
  have h := inv_foldl l [] .init hl ⟨by decide, by decide, by
    rw [DecimalState.init, toNat_toSlice]
    simp⟩
  rw [List.nil_append] at h
  exact toNat_finish _ _ h

end MPN
