/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import MPN.UIntArray

/-!
# Addition and subtraction

Like GMP's `mpn` functions, these write their result into the limbs of `r` from limb `off` on,
in place when `r` is not shared, and return the carry or borrow out:

* `addN r off a b c` and `subN r off a b c` are `a + b + c` and `a - b - c` on the first
  `min a.size b.size` limbs of `a` and `b`, like `mpn_add_n` and `mpn_sub_n`;
* `add1 r off a c` and `sub1 r off a c` are `a + c` and `a - c`, like `mpn_add_1` and
  `mpn_sub_1`;
* `add r off a b c` and `sub r off a b c` are `a + b + c` and `a - b - c` on all of `a`, for
  `b.size ≤ a.size`, like `mpn_add` and `mpn_sub`.

The carry and the borrow are words, so they may be any `UInt64`; from a carry or borrow of at most
one, the result is again at most one.
-/

open ScalarArray

namespace MPN

/-! ## Addition -/

/-- One limb of `addN`: the low word of `x + y + c` and the carry out. -/
private theorem add_step (x y c : UInt64) :
    (x + y + c).toNat + 2 ^ 64 * (UInt64.addh (UInt64.addh 0 x y) (x + y) c).toNat =
      x.toNat + y.toNat + c.toNat := by
  have := x.toNat_lt; have := y.toNat_lt; have := c.toNat_lt
  simp only [UInt64.toNat_addh, UInt64.toNat_add, UInt64.toNat_zero]
  generalize x.toNat = x at *
  generalize y.toNat = y at *
  generalize c.toNat = c at *
  lia

/-- Adds limbs `j` to `n - 1` of `a` and `b`, and the carry `c`, into `r` from limb `off + j` on. -/
def addNLoop (r : UInt64Array) (off : Nat) (a b : UInt64Array.Slice) (n : Nat)
    (hn : n ≤ a.size ∧ n ≤ b.size) (j : Nat) (c : UInt64) : UInt64Array × UInt64 :=
  if h : j < n then
    let x := a[j]
    let y := b[j]
    let s := x + y
    addNLoop (r.set! (off + j) (s + c)) off a b n hn (j + 1)
      (UInt64.addh (UInt64.addh 0 x y) s c)
  else
    (r, c)

/--
Writes the low `n` limbs of `a + b + c` into `r` from limb `off` on, where `n = min a.size b.size`,
and returns the carry out, like GMP's `mpn_add_n` with a carry in.
-/
public def addN (r : UInt64Array) (off : Nat) (a b : UInt64Array.Slice) (c : UInt64 := 0) :
    UInt64Array × UInt64 :=
  addNLoop r off a b (min a.size b.size) ⟨Nat.min_le_left .., Nat.min_le_right ..⟩ 0 c

private theorem addNLoop_spec (r : UInt64Array) (off : Nat) (a b : UInt64Array.Slice) (n : Nat)
    (hn : n ≤ a.size ∧ n ≤ b.size) (j : Nat) (c : UInt64) (hr : off + n ≤ r.size) :
    (addNLoop r off a b n hn j c).1.size = r.size ∧
      (∀ i, (i < off + j ∨ off + n ≤ i) → (addNLoop r off a b n hn j c).1[i]! = r[i]!) ∧
      (addNLoop r off a b n hn j c).1.valAt (off + j) (n - j) +
          2 ^ (64 * (n - j)) * (addNLoop r off a b n hn j c).2.toNat =
        a.array.valAt (a.start + j) (n - j) + b.array.valAt (b.start + j) (n - j) + c.toNat := by
  induction r, j, c using addNLoop.induct off a b n hn with
  | case1 r j c h x y s ih =>
    rw [addNLoop]
    simp only [h, ↓reduceDIte]
    obtain ⟨ih₁, ih₂, ih₃⟩ := ih (by simpa using hr)
    simp only [UInt64Array.size_set!] at ih₁
    have hv : (addNLoop (r.set! (off + j) (s + c)) off a b n hn (j + 1)
        (UInt64.addh (UInt64.addh 0 x y) s c)).1[off + j]! = s + c := by
      rw [ih₂ (off + j) (.inl (by lia)), UInt64Array.getElem!_set!]
      simp; lia
    refine ⟨ih₁, fun i hi => ?_, ?_⟩
    · rw [ih₂ i (by lia), UInt64Array.getElem!_set!]
      grind
    · obtain ⟨k, hk⟩ : ∃ k, n - j = k + 1 := ⟨n - j - 1, by lia⟩
      have hk' : n - (j + 1) = k := by lia
      rw [hk' , ← Nat.add_assoc, ← Nat.add_assoc] at ih₃
      rw [hk, UInt64Array.valAt_succ, UInt64Array.valAt_succ, UInt64Array.valAt_succ, hv,
        ← UInt64Array.Slice.getElem_eq_getElem! a j (by lia),
        ← UInt64Array.Slice.getElem_eq_getElem! b j (by lia), Nat.mul_succ, Nat.pow_add]
      have := add_step x y c
      generalize (addNLoop _ _ _ _ _ _ _ _).1.valAt _ _ = R at *
      generalize (addNLoop _ _ _ _ _ _ _ _).2.toNat = c' at *
      generalize (UInt64.addh _ _ _).toNat = c₁ at *
      generalize 2 ^ (64 * k) = P at *
      grind
  | case2 r j c h =>
    rw [addNLoop]
    simp [h, show n - j = 0 by lia]

@[simp] public theorem size_addN (r : UInt64Array) (off : Nat) (a b : UInt64Array.Slice)
    (c : UInt64) (hr : off + min a.size b.size ≤ r.size) : (addN r off a b c).1.size = r.size :=
  (addNLoop_spec r off a b _ _ 0 c hr).1

/-- `addN` leaves the limbs of `r` outside the ones it writes unchanged. -/
public theorem getElem!_addN (r : UInt64Array) (off : Nat) (a b : UInt64Array.Slice) (c : UInt64)
    (hr : off + min a.size b.size ≤ r.size) (i : Nat)
    (hi : i < off ∨ off + min a.size b.size ≤ i) :
    (addN r off a b c).1[i]! = r[i]! :=
  (addNLoop_spec r off a b _ _ 0 c hr).2.1 i (by lia)

public theorem valAt_addN (r : UInt64Array) (off : Nat) (a b : UInt64Array.Slice) (c : UInt64)
    (hr : off + min a.size b.size ≤ r.size) :
    (addN r off a b c).1.valAt off (min a.size b.size) +
        2 ^ (64 * min a.size b.size) * (addN r off a b c).2.toNat =
      a.array.valAt a.start (min a.size b.size) + b.array.valAt b.start (min a.size b.size) +
        c.toNat := by
  simpa [addN] using (addNLoop_spec r off a b _ _ 0 c hr).2.2

/-- `addN` on slices of the same size. -/
public theorem valAt_addN_of_size_eq (r : UInt64Array) (off : Nat) (a b : UInt64Array.Slice)
    (c : UInt64) (hab : a.size = b.size) (hr : off + a.size ≤ r.size) :
    (addN r off a b c).1.valAt off a.size + 2 ^ (64 * a.size) * (addN r off a b c).2.toNat =
      a.toNat + b.toNat + c.toNat := by
  have := valAt_addN r off a b c (by simpa [hab] using hr)
  simpa [hab, UInt64Array.Slice.toNat_eq_valAt] using this

/-- One limb of `add1`: the low word of `x + c` and the carry out. -/
private theorem add1_step (x c : UInt64) :
    (x + c).toNat + 2 ^ 64 * (UInt64.addh 0 x c).toNat = x.toNat + c.toNat := by
  have := x.toNat_lt; have := c.toNat_lt
  simp only [UInt64.toNat_addh, UInt64.toNat_add, UInt64.toNat_zero]
  generalize x.toNat = x at *
  generalize c.toNat = c at *
  lia

/-- Adds the carry `c` to limbs `j` to `a.size - 1` of `a` into `r` from limb `off + j` on. -/
def add1Loop (r : UInt64Array) (off : Nat) (a : UInt64Array.Slice) (j : Nat) (c : UInt64) :
    UInt64Array × UInt64 :=
  if h : j < a.size then
    let x := a[j]
    add1Loop (r.set! (off + j) (x + c)) off a (j + 1) (UInt64.addh 0 x c)
  else
    (r, c)

/--
Writes the limbs of `a + c` into `r` from limb `off` on and returns the carry out, like GMP's
`mpn_add_1`.
-/
public def add1 (r : UInt64Array) (off : Nat) (a : UInt64Array.Slice) (c : UInt64) :
    UInt64Array × UInt64 :=
  add1Loop r off a 0 c

private theorem add1Loop_spec (r : UInt64Array) (off : Nat) (a : UInt64Array.Slice) (j : Nat)
    (c : UInt64) (hr : off + a.size ≤ r.size) :
    (add1Loop r off a j c).1.size = r.size ∧
      (∀ i, (i < off + j ∨ off + a.size ≤ i) → (add1Loop r off a j c).1[i]! = r[i]!) ∧
      (add1Loop r off a j c).1.valAt (off + j) (a.size - j) +
          2 ^ (64 * (a.size - j)) * (add1Loop r off a j c).2.toNat =
        a.array.valAt (a.start + j) (a.size - j) + c.toNat := by
  induction r, j, c using add1Loop.induct off a with
  | case1 r j c h x ih =>
    rw [add1Loop]
    simp only [h, ↓reduceDIte]
    obtain ⟨ih₁, ih₂, ih₃⟩ := ih (by simpa using hr)
    simp only [UInt64Array.size_set!] at ih₁
    have hv : (add1Loop (r.set! (off + j) (x + c)) off a (j + 1)
        (UInt64.addh 0 x c)).1[off + j]! = x + c := by
      rw [ih₂ (off + j) (.inl (by lia)), UInt64Array.getElem!_set!]
      simp; lia
    refine ⟨ih₁, fun i hi => ?_, ?_⟩
    · rw [ih₂ i (by lia), UInt64Array.getElem!_set!]
      grind
    · obtain ⟨k, hk⟩ : ∃ k, a.size - j = k + 1 := ⟨a.size - j - 1, by lia⟩
      have hk' : a.size - (j + 1) = k := by lia
      rw [hk', ← Nat.add_assoc, ← Nat.add_assoc] at ih₃
      rw [hk, UInt64Array.valAt_succ, UInt64Array.valAt_succ, hv,
        ← UInt64Array.Slice.getElem_eq_getElem! a j (by lia), Nat.mul_succ, Nat.pow_add]
      have := add1_step x c
      generalize (add1Loop _ _ _ _ _).1.valAt _ _ = R at *
      generalize (add1Loop _ _ _ _ _).2.toNat = c' at *
      generalize (UInt64.addh _ _ _).toNat = c₁ at *
      generalize 2 ^ (64 * k) = P at *
      grind
  | case2 r j c h =>
    rw [add1Loop]
    simp [h, show a.size - j = 0 by lia]

@[simp] public theorem size_add1 (r : UInt64Array) (off : Nat) (a : UInt64Array.Slice)
    (c : UInt64) (hr : off + a.size ≤ r.size) : (add1 r off a c).1.size = r.size :=
  (add1Loop_spec r off a 0 c hr).1

/-- `add1` leaves the limbs of `r` outside the ones it writes unchanged. -/
public theorem getElem!_add1 (r : UInt64Array) (off : Nat) (a : UInt64Array.Slice) (c : UInt64)
    (hr : off + a.size ≤ r.size) (i : Nat) (hi : i < off ∨ off + a.size ≤ i) :
    (add1 r off a c).1[i]! = r[i]! :=
  (add1Loop_spec r off a 0 c hr).2.1 i (by lia)

public theorem valAt_add1 (r : UInt64Array) (off : Nat) (a : UInt64Array.Slice) (c : UInt64)
    (hr : off + a.size ≤ r.size) :
    (add1 r off a c).1.valAt off a.size + 2 ^ (64 * a.size) * (add1 r off a c).2.toNat =
      a.toNat + c.toNat := by
  simpa [add1, UInt64Array.Slice.toNat_eq_valAt] using (add1Loop_spec r off a 0 c hr).2.2

/--
Writes the limbs of `a + b + c` into `r` from limb `off` on and returns the carry out, like GMP's
`mpn_add`. It writes `a.size` limbs and requires `b.size ≤ a.size`.
-/
public def add (r : UInt64Array) (off : Nat) (a b : UInt64Array.Slice) (c : UInt64 := 0) :
    UInt64Array × UInt64 :=
  let p := addN r off a b c
  add1Loop p.1 off a b.size p.2

@[simp] public theorem size_add (r : UInt64Array) (off : Nat) (a b : UInt64Array.Slice)
    (c : UInt64) (hba : b.size ≤ a.size) (hr : off + a.size ≤ r.size) :
    (add r off a b c).1.size = r.size := by
  have h₁ := size_addN r off a b c (by lia)
  rw [add, (add1Loop_spec _ off a b.size _ (by lia)).1, h₁]

/-- `add` leaves the limbs of `r` outside the ones it writes unchanged. -/
public theorem getElem!_add (r : UInt64Array) (off : Nat) (a b : UInt64Array.Slice) (c : UInt64)
    (hba : b.size ≤ a.size) (hr : off + a.size ≤ r.size) (i : Nat)
    (hi : i < off ∨ off + a.size ≤ i) :
    (add r off a b c).1[i]! = r[i]! := by
  have h₁ := size_addN r off a b c (by lia)
  rw [add, (add1Loop_spec _ off a b.size _ (by lia)).2.1 i (by lia),
    getElem!_addN r off a b c (by lia) i (by lia)]

public theorem valAt_add (r : UInt64Array) (off : Nat) (a b : UInt64Array.Slice) (c : UInt64)
    (hba : b.size ≤ a.size) (hr : off + a.size ≤ r.size) :
    (add r off a b c).1.valAt off a.size + 2 ^ (64 * a.size) * (add r off a b c).2.toNat =
      a.toNat + b.toNat + c.toNat := by
  have hmin : min a.size b.size = b.size := by lia
  have h₁ := size_addN r off a b c (by lia)
  have h₂ := valAt_addN r off a b c (by lia)
  rw [hmin] at h₂
  obtain ⟨-, h₃, h₄⟩ := add1Loop_spec (addN r off a b c).1 off a b.size (addN r off a b c).2
    (by lia)
  have h₅ : (add r off a b c).1.valAt off b.size = (addN r off a b c).1.valAt off b.size :=
    UInt64Array.valAt_congr _ fun i _ hi => h₃ i (by lia)
  rw [add] at h₅ ⊢
  obtain ⟨k, hk⟩ : ∃ k, a.size = b.size + k := ⟨a.size - b.size, by lia⟩
  rw [show a.size - b.size = k by lia] at h₄
  rw [UInt64Array.Slice.toNat_eq_valAt, UInt64Array.Slice.toNat_eq_valAt, hk,
    UInt64Array.valAt_add, UInt64Array.valAt_add, h₅, Nat.mul_add, Nat.pow_add]
  generalize (add1Loop _ _ _ _ _).1.valAt _ _ = R at *
  generalize (add1Loop _ _ _ _ _).2.toNat = c' at *
  generalize (addN _ _ _ _ _).1.valAt _ _ = L at *
  generalize (addN _ _ _ _ _).2.toNat = c₁ at *
  generalize 2 ^ (64 * b.size) = P at *
  generalize 2 ^ (64 * k) = Q at *
  grind

/-! ## Subtraction -/

/-- One limb of `subN`: the low word of `x - y - c` and the borrow out. -/
private theorem sub_step (x y c : UInt64) :
    (x - y - c).toNat + y.toNat + c.toNat =
      x.toNat + 2 ^ 64 * (UInt64.subh (UInt64.subh 0 x y) (x - y) c).toNat := by
  have := x.toNat_lt; have := y.toNat_lt; have := c.toNat_lt
  simp only [UInt64.toNat_subh, UInt64.toNat_sub, UInt64.toNat_zero]
  generalize x.toNat = x at *
  generalize y.toNat = y at *
  generalize c.toNat = c at *
  split <;> split <;> lia

/--
Subtracts limbs `j` to `n - 1` of `b`, and the borrow `c`, from those of `a` into `r` from limb
`off + j` on.
-/
def subNLoop (r : UInt64Array) (off : Nat) (a b : UInt64Array.Slice) (n : Nat)
    (hn : n ≤ a.size ∧ n ≤ b.size) (j : Nat) (c : UInt64) : UInt64Array × UInt64 :=
  if h : j < n then
    let x := a[j]
    let y := b[j]
    let d := x - y
    subNLoop (r.set! (off + j) (d - c)) off a b n hn (j + 1)
      (UInt64.subh (UInt64.subh 0 x y) d c)
  else
    (r, c)

/--
Writes the low `n` limbs of `a - b - c` into `r` from limb `off` on, where `n = min a.size b.size`,
and returns the borrow out, like GMP's `mpn_sub_n` with a borrow in.
-/
public def subN (r : UInt64Array) (off : Nat) (a b : UInt64Array.Slice) (c : UInt64 := 0) :
    UInt64Array × UInt64 :=
  subNLoop r off a b (min a.size b.size) ⟨Nat.min_le_left .., Nat.min_le_right ..⟩ 0 c

private theorem subNLoop_spec (r : UInt64Array) (off : Nat) (a b : UInt64Array.Slice) (n : Nat)
    (hn : n ≤ a.size ∧ n ≤ b.size) (j : Nat) (c : UInt64) (hr : off + n ≤ r.size) :
    (subNLoop r off a b n hn j c).1.size = r.size ∧
      (∀ i, (i < off + j ∨ off + n ≤ i) → (subNLoop r off a b n hn j c).1[i]! = r[i]!) ∧
      (subNLoop r off a b n hn j c).1.valAt (off + j) (n - j) +
          b.array.valAt (b.start + j) (n - j) + c.toNat =
        a.array.valAt (a.start + j) (n - j) +
          2 ^ (64 * (n - j)) * (subNLoop r off a b n hn j c).2.toNat := by
  induction r, j, c using subNLoop.induct off a b n hn with
  | case1 r j c h x y d ih =>
    rw [subNLoop]
    simp only [h, ↓reduceDIte]
    obtain ⟨ih₁, ih₂, ih₃⟩ := ih (by simpa using hr)
    simp only [UInt64Array.size_set!] at ih₁
    have hv : (subNLoop (r.set! (off + j) (d - c)) off a b n hn (j + 1)
        (UInt64.subh (UInt64.subh 0 x y) d c)).1[off + j]! = d - c := by
      rw [ih₂ (off + j) (.inl (by lia)), UInt64Array.getElem!_set!]
      simp; lia
    refine ⟨ih₁, fun i hi => ?_, ?_⟩
    · rw [ih₂ i (by lia), UInt64Array.getElem!_set!]
      grind
    · obtain ⟨k, hk⟩ : ∃ k, n - j = k + 1 := ⟨n - j - 1, by lia⟩
      have hk' : n - (j + 1) = k := by lia
      rw [hk' , ← Nat.add_assoc, ← Nat.add_assoc] at ih₃
      rw [hk, UInt64Array.valAt_succ, UInt64Array.valAt_succ, UInt64Array.valAt_succ, hv,
        ← UInt64Array.Slice.getElem_eq_getElem! a j (by lia),
        ← UInt64Array.Slice.getElem_eq_getElem! b j (by lia), Nat.mul_succ, Nat.pow_add]
      have := sub_step x y c
      generalize (subNLoop _ _ _ _ _ _ _ _).1.valAt _ _ = R at *
      generalize (subNLoop _ _ _ _ _ _ _ _).2.toNat = c' at *
      generalize (UInt64.subh _ _ _).toNat = c₁ at *
      generalize 2 ^ (64 * k) = P at *
      grind
  | case2 r j c h =>
    rw [subNLoop]
    simp [h, show n - j = 0 by lia]

@[simp] public theorem size_subN (r : UInt64Array) (off : Nat) (a b : UInt64Array.Slice)
    (c : UInt64) (hr : off + min a.size b.size ≤ r.size) : (subN r off a b c).1.size = r.size :=
  (subNLoop_spec r off a b _ _ 0 c hr).1

/-- `subN` leaves the limbs of `r` outside the ones it writes unchanged. -/
public theorem getElem!_subN (r : UInt64Array) (off : Nat) (a b : UInt64Array.Slice) (c : UInt64)
    (hr : off + min a.size b.size ≤ r.size) (i : Nat)
    (hi : i < off ∨ off + min a.size b.size ≤ i) :
    (subN r off a b c).1[i]! = r[i]! :=
  (subNLoop_spec r off a b _ _ 0 c hr).2.1 i (by lia)

public theorem valAt_subN (r : UInt64Array) (off : Nat) (a b : UInt64Array.Slice) (c : UInt64)
    (hr : off + min a.size b.size ≤ r.size) :
    (subN r off a b c).1.valAt off (min a.size b.size) +
        b.array.valAt b.start (min a.size b.size) + c.toNat =
      a.array.valAt a.start (min a.size b.size) +
        2 ^ (64 * min a.size b.size) * (subN r off a b c).2.toNat := by
  simpa [subN] using (subNLoop_spec r off a b _ _ 0 c hr).2.2

/-- `subN` on slices of the same size. -/
public theorem valAt_subN_of_size_eq (r : UInt64Array) (off : Nat) (a b : UInt64Array.Slice)
    (c : UInt64) (hab : a.size = b.size) (hr : off + a.size ≤ r.size) :
    (subN r off a b c).1.valAt off a.size + b.toNat + c.toNat =
      a.toNat + 2 ^ (64 * a.size) * (subN r off a b c).2.toNat := by
  have := valAt_subN r off a b c (by simpa [hab] using hr)
  simpa [hab, UInt64Array.Slice.toNat_eq_valAt] using this

/-- One limb of `sub1`: the low word of `x - c` and the borrow out. -/
private theorem sub1_step (x c : UInt64) :
    (x - c).toNat + c.toNat = x.toNat + 2 ^ 64 * (UInt64.subh 0 x c).toNat := by
  have := x.toNat_lt; have := c.toNat_lt
  simp only [UInt64.toNat_subh, UInt64.toNat_sub, UInt64.toNat_zero]
  generalize x.toNat = x at *
  generalize c.toNat = c at *
  split <;> lia

/--
Subtracts the borrow `c` from limbs `j` to `a.size - 1` of `a` into `r` from limb `off + j` on.
-/
def sub1Loop (r : UInt64Array) (off : Nat) (a : UInt64Array.Slice) (j : Nat) (c : UInt64) :
    UInt64Array × UInt64 :=
  if h : j < a.size then
    let x := a[j]
    sub1Loop (r.set! (off + j) (x - c)) off a (j + 1) (UInt64.subh 0 x c)
  else
    (r, c)

/--
Writes the limbs of `a - c` into `r` from limb `off` on and returns the borrow out, like GMP's
`mpn_sub_1`.
-/
public def sub1 (r : UInt64Array) (off : Nat) (a : UInt64Array.Slice) (c : UInt64) :
    UInt64Array × UInt64 :=
  sub1Loop r off a 0 c

private theorem sub1Loop_spec (r : UInt64Array) (off : Nat) (a : UInt64Array.Slice) (j : Nat)
    (c : UInt64) (hr : off + a.size ≤ r.size) :
    (sub1Loop r off a j c).1.size = r.size ∧
      (∀ i, (i < off + j ∨ off + a.size ≤ i) → (sub1Loop r off a j c).1[i]! = r[i]!) ∧
      (sub1Loop r off a j c).1.valAt (off + j) (a.size - j) + c.toNat =
        a.array.valAt (a.start + j) (a.size - j) +
          2 ^ (64 * (a.size - j)) * (sub1Loop r off a j c).2.toNat := by
  induction r, j, c using sub1Loop.induct off a with
  | case1 r j c h x ih =>
    rw [sub1Loop]
    simp only [h, ↓reduceDIte]
    obtain ⟨ih₁, ih₂, ih₃⟩ := ih (by simpa using hr)
    simp only [UInt64Array.size_set!] at ih₁
    have hv : (sub1Loop (r.set! (off + j) (x - c)) off a (j + 1)
        (UInt64.subh 0 x c)).1[off + j]! = x - c := by
      rw [ih₂ (off + j) (.inl (by lia)), UInt64Array.getElem!_set!]
      simp; lia
    refine ⟨ih₁, fun i hi => ?_, ?_⟩
    · rw [ih₂ i (by lia), UInt64Array.getElem!_set!]
      grind
    · obtain ⟨k, hk⟩ : ∃ k, a.size - j = k + 1 := ⟨a.size - j - 1, by lia⟩
      have hk' : a.size - (j + 1) = k := by lia
      rw [hk', ← Nat.add_assoc, ← Nat.add_assoc] at ih₃
      rw [hk, UInt64Array.valAt_succ, UInt64Array.valAt_succ, hv,
        ← UInt64Array.Slice.getElem_eq_getElem! a j (by lia), Nat.mul_succ, Nat.pow_add]
      have := sub1_step x c
      generalize (sub1Loop _ _ _ _ _).1.valAt _ _ = R at *
      generalize (sub1Loop _ _ _ _ _).2.toNat = c' at *
      generalize (UInt64.subh _ _ _).toNat = c₁ at *
      generalize 2 ^ (64 * k) = P at *
      grind
  | case2 r j c h =>
    rw [sub1Loop]
    simp [h, show a.size - j = 0 by lia]

@[simp] public theorem size_sub1 (r : UInt64Array) (off : Nat) (a : UInt64Array.Slice)
    (c : UInt64) (hr : off + a.size ≤ r.size) : (sub1 r off a c).1.size = r.size :=
  (sub1Loop_spec r off a 0 c hr).1

/-- `sub1` leaves the limbs of `r` outside the ones it writes unchanged. -/
public theorem getElem!_sub1 (r : UInt64Array) (off : Nat) (a : UInt64Array.Slice) (c : UInt64)
    (hr : off + a.size ≤ r.size) (i : Nat) (hi : i < off ∨ off + a.size ≤ i) :
    (sub1 r off a c).1[i]! = r[i]! :=
  (sub1Loop_spec r off a 0 c hr).2.1 i (by lia)

public theorem valAt_sub1 (r : UInt64Array) (off : Nat) (a : UInt64Array.Slice) (c : UInt64)
    (hr : off + a.size ≤ r.size) :
    (sub1 r off a c).1.valAt off a.size + c.toNat =
      a.toNat + 2 ^ (64 * a.size) * (sub1 r off a c).2.toNat := by
  simpa [sub1, UInt64Array.Slice.toNat_eq_valAt] using (sub1Loop_spec r off a 0 c hr).2.2

/--
Writes the limbs of `a - b - c` into `r` from limb `off` on and returns the borrow out, like GMP's
`mpn_sub`. It writes `a.size` limbs and requires `b.size ≤ a.size`.
-/
public def sub (r : UInt64Array) (off : Nat) (a b : UInt64Array.Slice) (c : UInt64 := 0) :
    UInt64Array × UInt64 :=
  let p := subN r off a b c
  sub1Loop p.1 off a b.size p.2

@[simp] public theorem size_sub (r : UInt64Array) (off : Nat) (a b : UInt64Array.Slice)
    (c : UInt64) (hba : b.size ≤ a.size) (hr : off + a.size ≤ r.size) :
    (sub r off a b c).1.size = r.size := by
  have h₁ := size_subN r off a b c (by lia)
  rw [sub, (sub1Loop_spec _ off a b.size _ (by lia)).1, h₁]

/-- `sub` leaves the limbs of `r` outside the ones it writes unchanged. -/
public theorem getElem!_sub (r : UInt64Array) (off : Nat) (a b : UInt64Array.Slice) (c : UInt64)
    (hba : b.size ≤ a.size) (hr : off + a.size ≤ r.size) (i : Nat)
    (hi : i < off ∨ off + a.size ≤ i) :
    (sub r off a b c).1[i]! = r[i]! := by
  have h₁ := size_subN r off a b c (by lia)
  rw [sub, (sub1Loop_spec _ off a b.size _ (by lia)).2.1 i (by lia),
    getElem!_subN r off a b c (by lia) i (by lia)]

public theorem valAt_sub (r : UInt64Array) (off : Nat) (a b : UInt64Array.Slice) (c : UInt64)
    (hba : b.size ≤ a.size) (hr : off + a.size ≤ r.size) :
    (sub r off a b c).1.valAt off a.size + b.toNat + c.toNat =
      a.toNat + 2 ^ (64 * a.size) * (sub r off a b c).2.toNat := by
  have hmin : min a.size b.size = b.size := by lia
  have h₁ := size_subN r off a b c (by lia)
  have h₂ := valAt_subN r off a b c (by lia)
  rw [hmin] at h₂
  obtain ⟨-, h₃, h₄⟩ := sub1Loop_spec (subN r off a b c).1 off a b.size (subN r off a b c).2
    (by lia)
  have h₅ : (sub r off a b c).1.valAt off b.size = (subN r off a b c).1.valAt off b.size :=
    UInt64Array.valAt_congr _ fun i _ hi => h₃ i (by lia)
  rw [sub] at h₅ ⊢
  obtain ⟨k, hk⟩ : ∃ k, a.size = b.size + k := ⟨a.size - b.size, by lia⟩
  rw [show a.size - b.size = k by lia] at h₄
  rw [UInt64Array.Slice.toNat_eq_valAt, UInt64Array.Slice.toNat_eq_valAt, hk,
    UInt64Array.valAt_add, UInt64Array.valAt_add, h₅, Nat.mul_add, Nat.pow_add]
  generalize (sub1Loop _ _ _ _ _).1.valAt _ _ = R at *
  generalize (sub1Loop _ _ _ _ _).2.toNat = c' at *
  generalize (subN _ _ _ _ _).1.valAt _ _ = L at *
  generalize (subN _ _ _ _ _).2.toNat = c₁ at *
  generalize 2 ^ (64 * b.size) = P at *
  generalize 2 ^ (64 * k) = Q at *
  grind

end MPN
