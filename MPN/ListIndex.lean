/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

/-!
# Lists by index

`List.getD` through `getElem`, on appended, zipped and ranged lists, which the FFT's transform
reads its lists with.
-/

namespace MPN

public theorem getD_of_lt {α : Type} (l : List α) (i : Nat) (d : α) (h : i < l.length) :
    l.getD i d = l[i] := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]

public theorem getD_append_left {α : Type} (l l' : List α) (i : Nat) (d : α) (h : i < l.length) :
    (l ++ l').getD i d = l.getD i d := by
  rw [getD_of_lt _ _ _ (by simp; lia), getD_of_lt _ _ _ h, List.getElem_append_left h]

public theorem getD_append_right {α : Type} (l l' : List α) (i : Nat) (d : α)
    (h : l.length ≤ i) : (l ++ l').getD i d = l'.getD (i - l.length) d := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_right h]

public theorem getD_zipWith {α β γ : Type} (f : α → β → γ) (l : List α) (l' : List β) (i : Nat)
    (d : γ) (a : α) (b : β) (h : i < l.length) (h' : i < l'.length) :
    (List.zipWith f l l').getD i d = f (l.getD i a) (l'.getD i b) := by
  rw [getD_of_lt _ _ _ (by simp; lia), List.getElem_zipWith, getD_of_lt _ _ _ h,
    getD_of_lt _ _ _ h']

public theorem getD_range (m i d : Nat) (h : i < m) : (List.range m).getD i d = i := by
  rw [getD_of_lt _ _ _ (by simp; lia), List.getElem_range]

/-- A property of every entry, from the property of every entry by index. -/
public theorem forall_mem_of_getD {α : Type} {P : α → Prop} (l : List α) (d : α)
    (h : ∀ j < l.length, P (l.getD j d)) : ∀ y ∈ l, P y := by
  intro y hy
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.1 hy
  have := h i hi
  rwa [getD_of_lt _ _ _ hi] at this

public theorem mem_of_getD {α : Type} (l : List α) (i : Nat) (d : α) (h : i < l.length) :
    l.getD i d ∈ l := by
  rw [getD_of_lt _ _ _ h]; exact List.getElem_mem h

end MPN
