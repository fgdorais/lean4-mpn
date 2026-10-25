/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ScalarArray.UInt32
public import ScalarArray.UInt64

/-!
# In-place folds over a range of an array

lean4-scalar-arrays dropped the array folds `foldInPlace` and `foldInPlaceThen` in favor of the
slice folds `foldlInPlace` and `foldlInPlaceThen`. This module defines the array folds again, for
`UInt32Array` and `UInt64Array`, as the same plain loops of `set`s as before, which the proofs
are about, and `@[csimp]` lemmas make the compiler run the slice folds in their place, on the
slice `[start, start + len)` built from the bounds proof without checks. Nothing here is trusted:
the in-place loop is the library's.
-/

open ScalarArray

namespace ScalarArray.UInt32Array

/-- The loop of `foldInPlace`, over `Nat` indices. -/
@[expose]
public def foldInPlace.loop {β : Type v} (len' : USize)
    (f : (k : USize) → k.toNat < len'.toNat → UInt32 → β → UInt32 × β)
    (start len : Nat) (a : UInt32Array) (h : start + len ≤ a.size) (hlen : len ≤ len'.toNat)
    (k : Nat) (b : β) : UInt32Array × β :=
  if hk : k < len then
    let p := f k.toUSize (by
      have := len'.toNat_lt_size
      rw [USize.toNat_ofNat_of_lt' (by lia)]
      lia) (a[start + k]'(by lia)) b
    foldInPlace.loop len' f start len (a.set (start + k) p.1 (by lia)) (by simpa using h) hlen
      (k + 1) p.2
  else
    (a, b)
termination_by len - k

/--
Replaces each element of `a` from index `start` for `len` elements while threading an
accumulator: for each `k < len`, the element `x` at `start + k` becomes the first component of
`f k hk x b`, whose second component is the next accumulator. Returns the new array and the last
accumulator. The compiler runs `foldlInPlace` on the slice of those elements instead
(`foldInPlace_eq_fast`), which stores in place without checks.
-/
@[expose]
public def foldInPlace {β : Type v} (a : UInt32Array) (start len : USize) (init : β)
    (f : (k : USize) → k.toNat < len.toNat → UInt32 → β → UInt32 × β)
    (h : start.toNat + len.toNat ≤ a.size) : UInt32Array × β :=
  foldInPlace.loop len f start.toNat len.toNat a h (Nat.le_refl _) 0 init

public theorem size_foldInPlace_loop {β : Type v} (len' : USize)
    (f : (k : USize) → k.toNat < len'.toNat → UInt32 → β → UInt32 × β) (start len : Nat)
    (a : UInt32Array) (h : start + len ≤ a.size) (hlen : len ≤ len'.toNat) (k : Nat) (b : β) :
    (foldInPlace.loop len' f start len a h hlen k b).1.size = a.size := by
  induction a, h, k, b using foldInPlace.loop.induct len' f start len hlen with
  | case1 a h k b hk p ih =>
    rw [foldInPlace.loop]
    simp only [hk, ↓reduceDIte]
    rw [ih]
    simp
  | case2 a h k b hk =>
    rw [foldInPlace.loop]
    simp [hk]

@[simp] public theorem size_foldInPlace {β : Type v} (a : UInt32Array) (start len : USize)
    (init : β) (f : (k : USize) → k.toNat < len.toNat → UInt32 → β → UInt32 × β)
    (h : start.toNat + len.toNat ≤ a.size) :
    (a.foldInPlace start len init f h).1.size = a.size :=
  size_foldInPlace_loop len f _ _ a h _ 0 init

/-- `foldInPlace` followed by `g` on the new array and the last accumulator. -/
@[expose]
public def foldInPlaceThen {β : Type v} {γ : Type w} (a : UInt32Array) (start len : USize)
    (init : β) (f : (k : USize) → k.toNat < len.toNat → UInt32 → β → UInt32 × β)
    (g : UInt32Array → β → γ) (h : start.toNat + len.toNat ≤ a.size) : γ :=
  g (a.foldInPlace start len init f h).1 (a.foldInPlace start len init f h).2

@[simp] public theorem foldInPlaceThen_eq {β : Type v} {γ : Type w} (a : UInt32Array)
    (start len : USize) (init : β)
    (f : (k : USize) → k.toNat < len.toNat → UInt32 → β → UInt32 × β)
    (g : UInt32Array → β → γ) (h : start.toNat + len.toNat ≤ a.size) :
    a.foldInPlaceThen start len init f g h =
      g (a.foldInPlace start len init f h).1 (a.foldInPlace start len init f h).2 :=
  rfl

/-! ## The compiled folds -/

/-- The slice `[start, start + len)` of `a`, without checks. -/
@[inline, expose]
public def rangeSlice (a : UInt32Array) (start len : Nat) (h : start + len ≤ a.size) :
    UInt32Array.Slice :=
  ⟨{ array := a, start, stop := start + len, start_le_stop := Nat.le_add_right _ _,
     stop_le_array_size := h }⟩

private theorem size_rangeSlice (a : UInt32Array) (start len : Nat) (h : start + len ≤ a.size) :
    (rangeSlice a start len h).size = len := by
  rw [Slice.size_eq]
  show start + len - start = len
  lia

/--
`foldInPlace` by the slice fold on `rangeSlice`, which the compiler uses in its place. The fold
ends with the continuation `(s.array, b)`, so the slice it would return is never built.
-/
@[inline, expose]
public def foldInPlaceFast {β : Type v} (a : UInt32Array) (start len : USize) (init : β)
    (f : (k : USize) → k.toNat < len.toNat → UInt32 → β → UInt32 × β)
    (h : start.toNat + len.toNat ≤ a.size) : UInt32Array × β :=
  (rangeSlice a start.toNat len.toNat h).foldlInPlaceThen init
    (fun k hk => f k (by rw [size_rangeSlice] at hk; exact hk)) fun s b => (s.array, b)

/-- `foldInPlaceThen` by `foldlInPlaceThen` on `rangeSlice`. -/
@[inline, expose]
public def foldInPlaceThenFast {β : Type v} {γ : Type w} (a : UInt32Array) (start len : USize)
    (init : β) (f : (k : USize) → k.toNat < len.toNat → UInt32 → β → UInt32 × β)
    (g : UInt32Array → β → γ) (h : start.toNat + len.toNat ≤ a.size) : γ :=
  (rangeSlice a start.toNat len.toNat h).foldlInPlaceThen init
    (fun k hk => f k (by rw [size_rangeSlice] at hk; exact hk)) fun s b => g s.array b

/-- The slice loop from index `k`, up to `n = len`, is the array loop from `k`. -/
private theorem foldlInPlace_loop_eq {β : Type v} (len' : USize)
    (f : (k : USize) → k.toNat < len'.toNat → UInt32 → β → UInt32 × β) (len n : Nat)
    (hn : n = len) (hlen : len ≤ len'.toNat)
    (f' : (k : USize) → k.toNat < n → UInt32 → β → UInt32 × β)
    (hf : ∀ k hk, f' k hk = f k (by lia)) (k : Nat) :
    ∀ (s : UInt32Array.Slice) (hs : s.size = n) (h : s.start + len ≤ s.array.size) (b : β),
      ((Slice.foldlInPlace.loop n f' s hs k b).1.array,
          (Slice.foldlInPlace.loop n f' s hs k b).2) =
        foldInPlace.loop len' f s.start len s.array h hlen k b := by
  subst hn
  induction hd : n - k generalizing k with
  | zero =>
    intro s hs h b
    rw [Slice.foldlInPlace.loop, foldInPlace.loop]
    simp only [show ¬k < n by lia, ↓reduceDIte]
  | succ d ih =>
    intro s hs h b
    have hk : k < n := by lia
    rw [Slice.foldlInPlace.loop, foldInPlace.loop]
    simp only [hk, ↓reduceDIte]
    rw [hf]
    exact ih (k + 1) (by lia) _ _ (by simpa using h) _

@[csimp] public theorem foldInPlace_eq_fast : @foldInPlace.{v} = @foldInPlaceFast.{v} := by
  funext β a start len init f h
  rw [foldInPlaceFast, Slice.foldlInPlaceThen_eq]
  exact (foldlInPlace_loop_eq len f len.toNat _ (size_rangeSlice ..) (Nat.le_refl _) _
    (fun _ _ => rfl) 0 (rangeSlice a start.toNat len.toNat h) rfl h init).symm

@[csimp] public theorem foldInPlaceThen_eq_fast :
    @foldInPlaceThen.{v, w} = @foldInPlaceThenFast.{v, w} := by
  funext β γ a start len init f g h
  rw [foldInPlaceThen, foldInPlaceThenFast, Slice.foldlInPlaceThen_eq, foldInPlace_eq_fast]
  rfl

end ScalarArray.UInt32Array

namespace ScalarArray.UInt64Array

/-- The loop of `foldInPlace`, over `Nat` indices. -/
@[expose]
public def foldInPlace.loop {β : Type v} (len' : USize)
    (f : (k : USize) → k.toNat < len'.toNat → UInt64 → β → UInt64 × β)
    (start len : Nat) (a : UInt64Array) (h : start + len ≤ a.size) (hlen : len ≤ len'.toNat)
    (k : Nat) (b : β) : UInt64Array × β :=
  if hk : k < len then
    let p := f k.toUSize (by
      have := len'.toNat_lt_size
      rw [USize.toNat_ofNat_of_lt' (by lia)]
      lia) (a[start + k]'(by lia)) b
    foldInPlace.loop len' f start len (a.set (start + k) p.1 (by lia)) (by simpa using h) hlen
      (k + 1) p.2
  else
    (a, b)
termination_by len - k

/--
Replaces each element of `a` from index `start` for `len` elements while threading an
accumulator: for each `k < len`, the element `x` at `start + k` becomes the first component of
`f k hk x b`, whose second component is the next accumulator. Returns the new array and the last
accumulator. The compiler runs `foldlInPlace` on the slice of those elements instead
(`foldInPlace_eq_fast`), which stores in place without checks.
-/
@[expose]
public def foldInPlace {β : Type v} (a : UInt64Array) (start len : USize) (init : β)
    (f : (k : USize) → k.toNat < len.toNat → UInt64 → β → UInt64 × β)
    (h : start.toNat + len.toNat ≤ a.size) : UInt64Array × β :=
  foldInPlace.loop len f start.toNat len.toNat a h (Nat.le_refl _) 0 init

public theorem size_foldInPlace_loop {β : Type v} (len' : USize)
    (f : (k : USize) → k.toNat < len'.toNat → UInt64 → β → UInt64 × β) (start len : Nat)
    (a : UInt64Array) (h : start + len ≤ a.size) (hlen : len ≤ len'.toNat) (k : Nat) (b : β) :
    (foldInPlace.loop len' f start len a h hlen k b).1.size = a.size := by
  induction a, h, k, b using foldInPlace.loop.induct len' f start len hlen with
  | case1 a h k b hk p ih =>
    rw [foldInPlace.loop]
    simp only [hk, ↓reduceDIte]
    rw [ih]
    simp
  | case2 a h k b hk =>
    rw [foldInPlace.loop]
    simp [hk]

@[simp] public theorem size_foldInPlace {β : Type v} (a : UInt64Array) (start len : USize)
    (init : β) (f : (k : USize) → k.toNat < len.toNat → UInt64 → β → UInt64 × β)
    (h : start.toNat + len.toNat ≤ a.size) :
    (a.foldInPlace start len init f h).1.size = a.size :=
  size_foldInPlace_loop len f _ _ a h _ 0 init

/-- `foldInPlace` followed by `g` on the new array and the last accumulator. -/
@[expose]
public def foldInPlaceThen {β : Type v} {γ : Type w} (a : UInt64Array) (start len : USize)
    (init : β) (f : (k : USize) → k.toNat < len.toNat → UInt64 → β → UInt64 × β)
    (g : UInt64Array → β → γ) (h : start.toNat + len.toNat ≤ a.size) : γ :=
  g (a.foldInPlace start len init f h).1 (a.foldInPlace start len init f h).2

@[simp] public theorem foldInPlaceThen_eq {β : Type v} {γ : Type w} (a : UInt64Array)
    (start len : USize) (init : β)
    (f : (k : USize) → k.toNat < len.toNat → UInt64 → β → UInt64 × β)
    (g : UInt64Array → β → γ) (h : start.toNat + len.toNat ≤ a.size) :
    a.foldInPlaceThen start len init f g h =
      g (a.foldInPlace start len init f h).1 (a.foldInPlace start len init f h).2 :=
  rfl

/-! ## The compiled folds -/

/-- The slice `[start, start + len)` of `a`, without checks. -/
@[inline, expose]
public def rangeSlice (a : UInt64Array) (start len : Nat) (h : start + len ≤ a.size) :
    UInt64Array.Slice :=
  ⟨{ array := a, start, stop := start + len, start_le_stop := Nat.le_add_right _ _,
     stop_le_array_size := h }⟩

private theorem size_rangeSlice (a : UInt64Array) (start len : Nat) (h : start + len ≤ a.size) :
    (rangeSlice a start len h).size = len := by
  rw [Slice.size_eq]
  show start + len - start = len
  lia

/--
`foldInPlace` by the slice fold on `rangeSlice`, which the compiler uses in its place. The fold
ends with the continuation `(s.array, b)`, so the slice it would return is never built.
-/
@[inline, expose]
public def foldInPlaceFast {β : Type v} (a : UInt64Array) (start len : USize) (init : β)
    (f : (k : USize) → k.toNat < len.toNat → UInt64 → β → UInt64 × β)
    (h : start.toNat + len.toNat ≤ a.size) : UInt64Array × β :=
  (rangeSlice a start.toNat len.toNat h).foldlInPlaceThen init
    (fun k hk => f k (by rw [size_rangeSlice] at hk; exact hk)) fun s b => (s.array, b)

/-- `foldInPlaceThen` by `foldlInPlaceThen` on `rangeSlice`. -/
@[inline, expose]
public def foldInPlaceThenFast {β : Type v} {γ : Type w} (a : UInt64Array) (start len : USize)
    (init : β) (f : (k : USize) → k.toNat < len.toNat → UInt64 → β → UInt64 × β)
    (g : UInt64Array → β → γ) (h : start.toNat + len.toNat ≤ a.size) : γ :=
  (rangeSlice a start.toNat len.toNat h).foldlInPlaceThen init
    (fun k hk => f k (by rw [size_rangeSlice] at hk; exact hk)) fun s b => g s.array b

/-- The slice loop from index `k`, up to `n = len`, is the array loop from `k`. -/
private theorem foldlInPlace_loop_eq {β : Type v} (len' : USize)
    (f : (k : USize) → k.toNat < len'.toNat → UInt64 → β → UInt64 × β) (len n : Nat)
    (hn : n = len) (hlen : len ≤ len'.toNat)
    (f' : (k : USize) → k.toNat < n → UInt64 → β → UInt64 × β)
    (hf : ∀ k hk, f' k hk = f k (by lia)) (k : Nat) :
    ∀ (s : UInt64Array.Slice) (hs : s.size = n) (h : s.start + len ≤ s.array.size) (b : β),
      ((Slice.foldlInPlace.loop n f' s hs k b).1.array,
          (Slice.foldlInPlace.loop n f' s hs k b).2) =
        foldInPlace.loop len' f s.start len s.array h hlen k b := by
  subst hn
  induction hd : n - k generalizing k with
  | zero =>
    intro s hs h b
    rw [Slice.foldlInPlace.loop, foldInPlace.loop]
    simp only [show ¬k < n by lia, ↓reduceDIte]
  | succ d ih =>
    intro s hs h b
    have hk : k < n := by lia
    rw [Slice.foldlInPlace.loop, foldInPlace.loop]
    simp only [hk, ↓reduceDIte]
    rw [hf]
    exact ih (k + 1) (by lia) _ _ (by simpa using h) _

@[csimp] public theorem foldInPlace_eq_fast : @foldInPlace.{v} = @foldInPlaceFast.{v} := by
  funext β a start len init f h
  rw [foldInPlaceFast, Slice.foldlInPlaceThen_eq]
  exact (foldlInPlace_loop_eq len f len.toNat _ (size_rangeSlice ..) (Nat.le_refl _) _
    (fun _ _ => rfl) 0 (rangeSlice a start.toNat len.toNat h) rfl h init).symm

@[csimp] public theorem foldInPlaceThen_eq_fast :
    @foldInPlaceThen.{v, w} = @foldInPlaceThenFast.{v, w} := by
  funext β γ a start len init f g h
  rw [foldInPlaceThen, foldInPlaceThenFast, Slice.foldlInPlaceThen_eq, foldInPlace_eq_fast]
  rfl

end ScalarArray.UInt64Array
