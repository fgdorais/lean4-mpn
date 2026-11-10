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

end MPN
