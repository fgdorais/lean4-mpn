/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Std.Data.String.ToNat

/-!
# Strings of decimal digits

`isNatFast s` is `String.isNat s`, which tells whether `String.toNat?` reads a number, by a fold
over the characters (`String.foldl`) with a state of one byte. Lean's `String.isNat` runs a loop
over a slice's iterator, which costs more per character than reading the digits.

The state is `0` before a digit, at the start or after `_`, `1` after a digit and `2` once the
string is rejected: a digit leads to `1`, `_` from `1` to `0`, and anything else to `2`. The string
is accepted when the state ends at `1`. Two predicates on lists of characters, `G0` and `G1`, are
what the states `0` and `1` accept, which the characterization `String.isNat_iff` matches.
-/

namespace MPN

/-- One character of `isNatFast`. -/
@[inline, expose] public def natStep (q : UInt8) (c : Char) : UInt8 :=
  if q = 2 then 2 else if c = '_' then (if q = 1 then 0 else 2) else if c.isDigit then 1 else 2

/-- `String.isNat`, by a fold over the characters with a state of one byte. -/
@[expose] public def isNatFast (s : String) : Bool := s.foldl natStep 0 == 1

namespace IsNat

mutual
/-- What the state `0` accepts: a digit, then what the state `1` accepts. -/
def G0 : List Char → Prop
  | [] => False
  | c :: cs => c.isDigit = true ∧ G1 cs
/-- What the state `1` accepts: nothing more, or `_` then `G0`, or a digit then `G1`. -/
def G1 : List Char → Prop
  | [] => True
  | c :: cs => (c = '_' ∧ G0 cs) ∨ (c.isDigit = true ∧ G1 cs)
end

private theorem foldl_two (l : List Char) : l.foldl natStep 2 = 2 := by
  induction l with
  | nil => rfl
  | cons c cs ih => simpa [natStep] using ih

private theorem run_spec (l : List Char) :
    (l.foldl natStep 0 = 1 ↔ G0 l) ∧ (l.foldl natStep 1 = 1 ↔ G1 l) := by
  induction l with
  | nil => simp [G0, G1]
  | cons c cs ih =>
    obtain ⟨ih₀, ih₁⟩ := ih
    have hu : c = '_' → c.isDigit = false := by rintro rfl; decide
    by_cases h : c = '_'
    · subst h
      simp [natStep, G0, G1, foldl_two, ih₀]
    · by_cases hd : c.isDigit = true
      · simp [natStep, G0, G1, h, hd, ih₁]
      · simp [natStep, G0, G1, h, hd, foldl_two]

private theorem no_uu_cons {c : Char} {l : List Char} :
    (¬ ['_', '_'] <:+: c :: l) ↔ (¬ ['_', '_'] <:+: l ∧ ¬ (c = '_' ∧ l.head? = some '_')) := by
  cases l with
  | nil => simp [List.infix_cons_iff]
  | cons d ds =>
    simp only [List.infix_cons_iff, List.prefix_cons_iff, List.head?_cons, Option.some.injEq]
    grind

private theorem g_spec (l : List Char) :
    (G0 l ↔ l ≠ [] ∧ (∀ c ∈ l, c.isDigit = true ∨ c = '_') ∧ ¬ ['_', '_'] <:+: l ∧
        l.head? ≠ some '_' ∧ l.getLast? ≠ some '_') ∧
      (G1 l ↔ (∀ c ∈ l, c.isDigit = true ∨ c = '_') ∧ ¬ ['_', '_'] <:+: l ∧
        l.getLast? ≠ some '_') := by
  induction l with
  | nil => simp [G0, G1]
  | cons c cs ih =>
    obtain ⟨ih₀, ih₁⟩ := ih
    have hu : c = '_' → c.isDigit = false := by rintro rfl; decide
    have hlast : (c :: cs).getLast? = some '_' ↔ (cs = [] ∧ c = '_') ∨ cs.getLast? = some '_' := by
      cases cs with
      | nil => simp
      | cons d ds => simp [List.getLast?_cons_cons]
    have hhead : cs = [] ∨ ∃ d ds, cs = d :: ds := by cases cs <;> simp
    simp only [G0, G1, ih₀, ih₁, no_uu_cons, List.mem_cons, forall_eq_or_imp, List.head?_cons]
    rcases hhead with rfl | ⟨d, ds, rfl⟩
    · simp; grind
    · simp only [List.head?_cons, Option.some.injEq]
      grind

end IsNat

open IsNat in
/-- `isNatFast` is `String.isNat`. -/
public theorem isNatFast_eq (s : String) : isNatFast s = s.isNat := by
  apply Bool.eq_iff_iff.2
  rw [isNatFast, beq_iff_eq, String.foldl_eq_foldl_toList, (run_spec _).1, (g_spec _).1,
    String.isNat_iff]
  simp only [ne_eq, String.toList_eq_nil_iff]

/-! ## By bytes

`isNatB` runs the same automaton on the UTF-8 bytes of the string, `String.getUTF8Byte`, without
decoding characters: a digit or `_` is one byte, its value, and the first byte of any other
character is not a digit nor `_` (it is below `128` and not one of them, or `0xc0` or more), so that
the automaton rejects at it, as at the character.
-/

/-- One byte of `isNatB`. -/
@[inline, expose] public def natStepB (q b : UInt8) : UInt8 :=
  if q = 2 then 2 else if b = 95 then (if q = 1 then 0 else 2)
  else if 48 ≤ b && b ≤ 57 then 1 else 2

/-- `isNatFast` over the bytes from `i`, in the state `q`. -/
@[expose] public def isNatBLoop (s : String) (i : Nat) (q : UInt8) : Bool :=
  if h : i < s.utf8ByteSize then isNatBLoop s (i + 1) (natStepB q (s.getUTF8Byte ⟨i⟩ h))
  else q == 1
termination_by s.utf8ByteSize - i

/-- `String.isNat`, by the automaton of `isNatFast` on the bytes of the string. -/
@[expose] public def isNatB (s : String) : Bool := isNatBLoop s 0 0

namespace IsNat

private theorem foldlB_two (l : List UInt8) : l.foldl natStepB 2 = 2 := by
  induction l with
  | nil => rfl
  | cons b bs ih => simpa [natStepB] using ih

private theorem loop_eq (s : String) (i : Nat) (q : UInt8) :
    isNatBLoop s i q = ((s.toByteArray.data.toList.drop i).foldl natStepB q == 1) := by
  induction i, q using isNatBLoop.induct s with
  | case1 i q h ih =>
    rw [isNatBLoop, dite_eq_left h, ih]
    have h' : i < s.toByteArray.data.toList.length := by
      simp only [Array.length_toList]; exact h
    rw [List.drop_eq_getElem_cons h', List.foldl_cons, String.getUTF8Byte_eq_getElem]
    rfl
  | case2 i q h =>
    rw [isNatBLoop, dite_eq_right h, List.drop_eq_nil_of_le (by
      simp only [Array.length_toList]; exact Nat.le_of_not_lt h)]
    rfl

/-- The first byte of a character of two to four bytes is `0xc0` or more. -/
private theorem first_byte (c : Char) (h : c.utf8Size ≠ 1) :
    ∃ b bs, String.utf8EncodeChar c = b :: bs ∧ 192 ≤ b.toNat := by
  have h1 := Char.utf8Size_pos c
  have h4 := Char.utf8Size_le_four c
  have hor : ∀ x y : UInt8, y.toNat ≤ (x ||| y).toNat := fun x y => by
    rw [UInt8.toNat_or]; exact Nat.right_le_or
  rcases (by lia : c.utf8Size = 2 ∨ c.utf8Size = 3 ∨ c.utf8Size = 4) with e | e | e
  · rw [String.utf8EncodeChar_eq_cons_cons e]
    exact ⟨_, _, rfl, Nat.le_trans (by decide) (hor _ 0xc0)⟩
  · rw [String.utf8EncodeChar_eq_cons_cons_cons e]
    exact ⟨_, _, rfl, Nat.le_trans (by decide) (hor _ 0xe0)⟩
  · rw [String.utf8EncodeChar_eq_cons_cons_cons_cons e]
    exact ⟨_, _, rfl, Nat.le_trans (by decide) (hor _ 0xf0)⟩

/-- The bytes of a character take the automaton where the character does. -/
private theorem foldl_char (q : UInt8) (c : Char) :
    (String.utf8EncodeChar c).foldl natStepB q = natStep q c := by
  by_cases h : c.utf8Size = 1
  · rw [String.utf8EncodeChar_eq_singleton h, List.foldl_cons, List.foldl_nil]
    have hv := Char.utf8Size_eq_one_iff.1 h
    have hb : c.val.toUInt8.toNat = c.val.toNat := by
      rw [UInt32.toNat_toUInt8, Nat.mod_eq_of_lt (by
        have := UInt32.le_iff_toNat_le.1 hv; simp at this; lia)]
    have hu : c.val.toUInt8 = 95 ↔ c = '_' := by
      constructor
      · intro e
        apply Char.ext; apply UInt32.toNat_inj.1
        have := congrArg UInt8.toNat e
        rw [hb] at this; simpa using this
      · rintro rfl; rfl
    have hd : (48 ≤ c.val.toUInt8 && c.val.toUInt8 ≤ 57) = c.isDigit := by
      simp only [Char.isDigit, UInt8.le_iff_toNat_le, UInt32.le_iff_toNat_le, hb]
      simp
    unfold natStepB natStep
    by_cases hq2 : q = 2
    · simp [hq2]
    · simp only [hq2, ↓reduceIte, hu, hd]
  · obtain ⟨b, bs, e, hb⟩ := first_byte c h
    rw [e, List.foldl_cons]
    have h95 : b ≠ 95 := fun e' => by rw [e'] at hb; simp at hb
    have hdig : (48 ≤ b && b ≤ 57) = false := by
      simp only [Bool.and_eq_false_iff, decide_eq_false_iff_not, UInt8.not_le,
        UInt8.lt_iff_toNat_lt]
      right; simp; lia
    have hc : c ≠ '_' := by rintro rfl; exact h rfl
    have hcd : c.isDigit = false := by
      cases hcd : c.isDigit
      · rfl
      · exfalso; apply h
        simp only [Char.isDigit, Bool.and_eq_true, decide_eq_true_eq] at hcd
        apply Char.utf8Size_eq_one_iff.2
        exact UInt32.le_iff_toNat_le.2 (by
          have := UInt32.le_iff_toNat_le.1 hcd.2; simp at this ⊢; lia)
    have : natStepB q b = 2 := by
      unfold natStepB
      by_cases hq2 : q = 2
      · simp [hq2]
      · simp [hq2, h95, hdig]
    rw [this, foldlB_two]
    unfold natStep
    by_cases hq2 : q = 2
    · simp [hq2]
    · simp [hq2, hc, hcd]

private theorem foldl_bytes (l : List Char) (q : UInt8) :
    (l.flatMap String.utf8EncodeChar).foldl natStepB q = l.foldl natStep q := by
  induction l generalizing q with
  | nil => rfl
  | cons c cs ih =>
    rw [List.flatMap_cons, List.foldl_append, foldl_char q, List.foldl_cons]
    exact ih _

end IsNat

open IsNat in
/-- `isNatB` is `String.isNat`. -/
public theorem isNatB_eq (s : String) : isNatB s = s.isNat := by
  rw [← isNatFast_eq, isNatB, IsNat.loop_eq, List.drop_zero, isNatFast]
  have hb : s.toByteArray.data.toList = s.toList.flatMap String.utf8EncodeChar := by
    rw [← String.utf8Encode_toList, List.utf8Encode, List.toList_data_toByteArray]
  rw [hb, IsNat.foldl_bytes, String.foldl_eq_foldl_toList]

end MPN
