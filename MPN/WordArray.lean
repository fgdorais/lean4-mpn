/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import MPN.LimbArray

/-!
# Arrays of words

`WordArray A L` gives arrays `A` of limbs `L` of `w` bits the reads and writes at `USize` indices
of their in-place loops, and the word operations on limbs that carry loops use: sums and
differences modulo `2ʷ` with their carries and borrows, shifts and comparisons with zero, each with
its value. `WordFolds A L` adds the in-place folds of lean4-scalar-arrays over one window (`foldThen`)
and over one window while reading two others of the same array (`fold2Then`), which make the array
exclusive once and then store without checks, and states that they are the plain loops of `uget`s
and `uset`s (`foldUInPlaceThen`, `foldUInPlace2Then`), which the proofs are about.

Code written once over these classes, with `@[expose, specialize]`, compiles in `main32` and
`main64` to the loops on their own arrays of 32-bit and 64-bit limbs.
-/

namespace MPN

/-! ## `USize` arithmetic -/

/-- `USize` addition that does not overflow. -/
public theorem _root_.USize.toNat_add_of_lt {a b : USize} (h : a.toNat + b.toNat < USize.size) :
    (a + b).toNat = a.toNat + b.toNat := by
  rw [USize.toNat_add]
  exact Nat.mod_eq_of_lt h

/-- The successor of an index below `n` does not overflow. -/
public theorem _root_.USize.toNat_add_one_of_lt {j n : USize} (h : j < n) :
    (j + 1).toNat = j.toNat + 1 := by
  have := USize.lt_iff_toNat_lt.1 h
  have := n.toNat_lt_size
  have : 4294967296 ≤ USize.size := by cases USize.size_eq <;> lia
  rw [USize.toNat_add_of_lt (a := j) (b := 1) (by rw [USize.toNat_one]; lia), USize.toNat_one]

namespace WordArray

variable {A L : Type} [LA : LimbArray A L]

/--
The bounds of a loop over limbs `rs` to `rs + n - 1` of `arr`: they are limbs of `arr`, and their
indices do not overflow.
-/
public abbrev LoopBound (arr : A) (rs n : USize) : Prop :=
  rs.toNat + n.toNat ≤ LA.size arr ∧ rs.toNat + n.toNat < USize.size

public theorem LoopBound.toNat_add {arr : A} {rs n j : USize} (hr : LoopBound arr rs n)
    (h : j < n) : (rs + j).toNat = rs.toNat + j.toNat := by
  have := USize.lt_iff_toNat_lt.1 h
  exact USize.toNat_add_of_lt (by lia)

public theorem LoopBound.uset_bound {arr : A} {rs n j : USize} (hr : LoopBound arr rs n)
    (h : j < n) : (rs + j).toNat < LA.size arr := by
  have := USize.lt_iff_toNat_lt.1 h
  rw [hr.toNat_add h]
  lia

/-- The same bounds on an array of the same size. -/
public theorem LoopBound.of_size {arr arr' : A} {rs n : USize} (hr : LoopBound arr rs n)
    (h : LA.size arr' = LA.size arr) : LoopBound arr' rs n := by
  simp only [LoopBound, h]; exact hr

end WordArray

open WordArray in
/--
Arrays `A` of limbs `L` with reads and writes at `USize` indices, and the word operations of their
limbs, with their values.
-/
public class WordArray (A : Type) (L : outParam Type) [LA : LimbArray A L] where
  /-- Limb `i` of an array, within it. -/
  uget : (a : A) → (i : USize) → i.toNat < LA.size a → L
  /-- Sets limb `i` of an array, within it. -/
  uset : (a : A) → (i : USize) → L → i.toNat < LA.size a → A
  uget_eq : ∀ a i h, uget a i h = LA.get a i.toNat
  size_uset : ∀ a i v h, LA.size (uset a i v h) = LA.size a
  get_uset : ∀ a i v h j, LA.get (uset a i v h) j = if i.toNat = j then v else LA.get a j
  /-- The limb `0`. -/
  zero : L
  /-- The limb `1`. -/
  one : L
  /-- `x + y` modulo `2ʷ`. -/
  add : L → L → L
  /-- `x - y` modulo `2ʷ`. -/
  sub : L → L → L
  /-- `x 2ᵇ` modulo `2ʷ`, for `b < w`. -/
  shl : L → L → L
  /-- `⌊x / 2ᵇ⌋`, for `b < w`. -/
  shr : L → L → L
  /-- `c` plus the carry out of `x + y`. -/
  addh : L → L → L → L
  /-- `b` plus the borrow out of `x - y`. -/
  subh : L → L → L → L
  /-- `x y` modulo `2ʷ`. -/
  mul : L → L → L
  /-- The high limb of `x y`. -/
  mulh : L → L → L
  /-- `⌊(h 2ʷ + l) / d⌋`, for `h < d`: `div2 h l d`. -/
  div2 : L → L → L → L
  /-- Whether `x < y`. -/
  ltB : L → L → Bool
  /-- Whether `x = y`. -/
  eqB : L → L → Bool
  /-- The bitwise and, for masks. -/
  land : L → L → L
  /-- `1` or `0`. -/
  ofBool : Bool → L
  /-- Whether a limb is zero. -/
  isZero : L → Bool
  /-- A `USize` as a limb, modulo `2ʷ`. -/
  ofUSize : USize → L
  /-- The width `w` as a `USize`. -/
  wU : USize
  val_zero : LA.val zero = 0
  val_one : LA.val one = 1
  val_add : ∀ x y, LA.val (add x y) = (LA.val x + LA.val y) % 2 ^ LA.w
  val_sub : ∀ x y, LA.val (sub x y) = (LA.val x + (2 ^ LA.w - LA.val y)) % 2 ^ LA.w
  val_shl : ∀ x b, LA.val (shl x b) = LA.val x * 2 ^ (LA.val b % LA.w) % 2 ^ LA.w
  val_shr : ∀ x b, LA.val (shr x b) = LA.val x / 2 ^ (LA.val b % LA.w)
  val_addh : ∀ c x y,
    LA.val (addh c x y) = (LA.val c + (LA.val x + LA.val y) / 2 ^ LA.w) % 2 ^ LA.w
  val_subh : ∀ b x y,
    LA.val (subh b x y) = (LA.val b + if LA.val x < LA.val y then 1 else 0) % 2 ^ LA.w
  val_mul : ∀ x y, LA.val (mul x y) = LA.val x * LA.val y % 2 ^ LA.w
  val_mulh : ∀ x y, LA.val (mulh x y) = LA.val x * LA.val y / 2 ^ LA.w
  val_div2 : ∀ h l d, LA.val h < LA.val d →
    LA.val (div2 h l d) = (LA.val h * 2 ^ LA.w + LA.val l) / LA.val d
  ltB_iff : ∀ x y, ltB x y = true ↔ LA.val x < LA.val y
  eqB_iff : ∀ x y, eqB x y = true ↔ LA.val x = LA.val y
  isZero_iff : ∀ x, isZero x = true ↔ LA.val x = 0
  val_ofUSize : ∀ i, LA.val (ofUSize i) = i.toNat % 2 ^ LA.w
  toNat_wU : wU.toNat = LA.w
  /-- Limbs have at least two bits, so that a limb holds a sum of two carries. -/
  w_ge : 2 ≤ LA.w

namespace WordArray

/-! ## Carries and borrows of limbs -/

/-- A sum below `2 B` carries at most `1`. -/
public theorem carry_le {s B : Nat} (h : s < 2 * B) : s / B ≤ 1 :=
  Nat.le_of_lt_succ ((Nat.div_lt_iff_lt_mul (by lia)).2 (by lia))

/-- `(a - b) % B` with its borrow, for `a, b < B`. -/
public theorem sub_mod_eq {a b B : Nat} (ha : a < B) (hb : b < B) :
    (a + (B - b)) % B + b = a + B * (if a < b then 1 else 0) := by
  split
  · rw [Nat.mod_eq_of_lt (by lia)]; lia
  · rw [show a + (B - b) = (a - b) + B * 1 by lia, Nat.add_mul_mod_self_left,
      Nat.mod_eq_of_lt (by lia)]
    lia

variable {A L : Type} [LA : LimbArray A L] [R : WordArray A L]

/-- `2ʷ` is at least `4`. -/
public theorem four_le : 4 ≤ 2 ^ LA.w :=
  calc 4 = 2 ^ 2 := rfl
    _ ≤ 2 ^ LA.w := Nat.pow_le_pow_right (by decide) R.w_ge

/-- `x + c` with its carry. -/
public theorem incr_step (x c : L) :
    LA.val (R.add x c) + 2 ^ LA.w * LA.val (R.addh R.zero x c) = LA.val x + LA.val c := by
  have hx := LA.val_lt x; have hc := LA.val_lt c; have hB := four_le (R := R)
  rw [R.val_add, R.val_addh, R.val_zero, Nat.zero_add]
  have := carry_le (s := LA.val x + LA.val c) (B := 2 ^ LA.w) (by lia)
  rw [Nat.mod_eq_of_lt (a := _ / _) (by lia)]
  exact Nat.mod_add_div _ _

/-- `x - c` with its borrow. -/
public theorem decr_step (x c : L) :
    LA.val (R.sub x c) + LA.val c = LA.val x + 2 ^ LA.w * LA.val (R.subh R.zero x c) := by
  have hx := LA.val_lt x; have hc := LA.val_lt c; have hB := four_le (R := R)
  rw [R.val_sub, R.val_subh, R.val_zero, Nat.zero_add, sub_mod_eq hx hc]
  split <;> simp [Nat.mod_eq_of_lt (show 1 < 2 ^ LA.w by lia)]

/-- `x + y + c` with its carry. -/
public theorem add_step (x y c : L) :
    LA.val (R.add (R.add x y) c) + 2 ^ LA.w * LA.val (R.addh (R.addh R.zero x y) (R.add x y) c) =
      LA.val x + LA.val y + LA.val c := by
  have hx := LA.val_lt x; have hy := LA.val_lt y; have hc := LA.val_lt c
  have hB := four_le (R := R)
  simp only [R.val_add, R.val_addh, R.val_zero, Nat.zero_add]
  generalize LA.val x = X at *
  generalize LA.val y = Y at *
  generalize LA.val c = C at *
  generalize 2 ^ LA.w = B at *
  have h₁ : (X + Y) / B ≤ 1 := carry_le (by lia)
  have hm := Nat.mod_lt (X + Y) (show 0 < B by lia)
  have h₂ : ((X + Y) % B + C) / B ≤ 1 := carry_le (by lia)
  rw [Nat.mod_eq_of_lt (a := (X + Y) / B) (by lia), Nat.mod_eq_of_lt (a := (X + Y) / B + _) (by lia)]
  have e₁ := Nat.mod_add_div (X + Y) B
  have e₂ := Nat.mod_add_div ((X + Y) % B + C) B
  generalize (X + Y) / B = q₁ at *
  generalize ((X + Y) % B + C) / B = q₂ at *
  rw [Nat.mul_add]
  lia

/-- `x - y - c` with its borrow. -/
public theorem sub_step (x y c : L) :
    LA.val (R.sub (R.sub x y) c) + LA.val y + LA.val c =
      LA.val x + 2 ^ LA.w * LA.val (R.subh (R.subh R.zero x y) (R.sub x y) c) := by
  have hx := LA.val_lt x; have hy := LA.val_lt y; have hc := LA.val_lt c
  have hB := four_le (R := R)
  simp only [R.val_sub, R.val_subh, R.val_zero, Nat.zero_add]
  generalize LA.val x = X at *
  generalize LA.val y = Y at *
  generalize LA.val c = C at *
  generalize 2 ^ LA.w = B at *
  have e₁ := sub_mod_eq hx hy
  have hm := Nat.mod_lt (X + (B - Y)) (show 0 < B by lia)
  have e₂ := sub_mod_eq hm hc
  generalize (X + (B - Y)) % B = D at *
  rw [Nat.mod_eq_of_lt (a := if X < Y then 1 else 0) (by split <;> lia),
    Nat.mod_eq_of_lt (a := (if X < Y then 1 else 0) + _) (by split <;> split <;> lia)]
  generalize (if X < Y then 1 else 0) = b₁ at *
  generalize (if D < C then 1 else 0) = b₂ at *
  rw [Nat.mul_add]
  lia

public theorem LoopBound.of_uset {arr : A} {rs n : USize} (hr : LoopBound arr rs n)
    (i : USize) (v : L) (h) : LoopBound (R.uset arr i v h) rs n :=
  hr.of_size (R.size_uset ..)

/-- `valAt` does not see a `uset` outside the limbs it reads. -/
public theorem valAt_uset_of (a : A) (i : USize) (v : L) (h : i.toNat < LA.size a)
    (lo n : Nat) (hi : i.toNat < lo ∨ lo + n ≤ i.toNat) :
    LimbArray.valAt (R.uset a i v h) lo n = LimbArray.valAt a lo n :=
  LimbArray.valAt_congr _ fun k h₁ h₂ => by
    rw [R.get_uset]
    simp only [show ¬(i.toNat = k) by lia, ↓reduceIte]

/-! ## In-place loops

`foldUInPlace n f arr rs hr j b` replaces limbs `rs + j` to `rs + n - 1` of `arr` while threading
an accumulator: limb `rs + j` holding `x` becomes `(f j hj x b).1`, and `(f j hj x b).2` is the
next accumulator. `f` may read other arrays, such as the operand of a multiply-subtract pass.
-/

/-- Replaces limbs `rs + j` to `rs + n - 1` of `arr` with `f`, threading an accumulator. -/
@[expose] public def foldUInPlace {β : Type} (n : USize) (f : (j : USize) → j < n → L → β → L × β)
    (arr : A) (rs : USize) (hr : LoopBound arr rs n) (j : USize) (b : β) : A × β :=
  if h : j < n then
    let p := f j h (R.uget arr (rs + j) (hr.uset_bound h)) b
    foldUInPlace n f (R.uset arr (rs + j) p.1 (hr.uset_bound h)) rs (hr.of_uset ..) (j + 1) p.2
  else
    (arr, b)
termination_by n.toNat - j.toNat
decreasing_by
  have := USize.lt_iff_toNat_lt.1 h
  rw [USize.toNat_add_one_of_lt h]
  lia

public theorem foldUInPlace_lt {β : Type} (n : USize) (f : (j : USize) → j < n → L → β → L × β)
    (arr : A) (rs : USize) (hr : LoopBound arr rs n) (j : USize) (b : β) (h : j < n) :
    foldUInPlace n f arr rs hr j b =
      foldUInPlace n f (R.uset arr (rs + j) (f j h (R.uget arr (rs + j) (hr.uset_bound h)) b).1
        (hr.uset_bound h)) rs (hr.of_uset ..) (j + 1)
        (f j h (R.uget arr (rs + j) (hr.uset_bound h)) b).2 := by
  rw [foldUInPlace]
  simp only [h, ↓reduceDIte]

public theorem foldUInPlace_ge {β : Type} (n : USize) (f : (j : USize) → j < n → L → β → L × β)
    (arr : A) (rs : USize) (hr : LoopBound arr rs n) (j : USize) (b : β) (h : ¬j < n) :
    foldUInPlace n f arr rs hr j b = (arr, b) := by
  rw [foldUInPlace]
  simp only [h, ↓reduceDIte]

public theorem size_foldUInPlace {β : Type} (n : USize) (f : (j : USize) → j < n → L → β → L × β)
    (arr : A) (rs : USize) (hr : LoopBound arr rs n) (j : USize) (b : β) :
    LA.size (foldUInPlace n f arr rs hr j b).1 = LA.size arr := by
  induction arr, hr, j, b using foldUInPlace.induct (R := R) n f rs with
  | case1 arr hr j b h p ih =>
    rw [foldUInPlace_lt _ _ _ _ _ _ _ h]
    exact ih.trans (R.size_uset ..)
  | case2 arr hr j b h =>
    rw [foldUInPlace_ge _ _ _ _ _ _ _ h]

/-- `foldUInPlace` followed by `g` on the new array and the last accumulator, like
`foldUInPlace2Then`. -/
@[expose]
public def foldUInPlaceThen {β γ : Type} (n : USize) (f : (j : USize) → j < n → L → β → L × β)
    (arr : A) (rs : USize) (hr : LoopBound arr rs n) (j : USize) (b : β)
    (g : (arr' : A) → LA.size arr' = LA.size arr → β → γ) : γ :=
  g (foldUInPlace n f arr rs hr j b).1 (size_foldUInPlace ..) (foldUInPlace n f arr rs hr j b).2

/-! ## In-place loops reading the same array

`foldUInPlace2 n f arr rs xs ys hr hx hy j b` replaces limbs `rs + j` to `rs + n - 1` of `arr`
while threading an accumulator, where `f` also receives limbs `xs + j` and `ys + j` of `arr`
itself, read at the time of the step. A function on several windows of one array, such as the
butterflies of the FFT on its flat array, can then read and write them without a second reference
to the array, which would copy it. When each window read starts at or after the window written, or
ends before it, the limbs read are those from before the loop (`foldUInPlace2_spec`).
-/

/-- Replaces limbs `rs + j` to `rs + n - 1` of `arr` with `f` of limbs `xs + j` and `ys + j`. -/
@[expose] public def foldUInPlace2 {β : Type} (n : USize)
    (f : (j : USize) → j < n → L → L → β → L × β)
    (arr : A) (rs xs ys : USize) (hr : LoopBound arr rs n) (hx : LoopBound arr xs n)
    (hy : LoopBound arr ys n) (j : USize) (b : β) : A × β :=
  if h : j < n then
    let p := f j h (R.uget arr (xs + j) (hx.uset_bound h)) (R.uget arr (ys + j) (hy.uset_bound h)) b
    foldUInPlace2 n f (R.uset arr (rs + j) p.1 (hr.uset_bound h)) rs xs ys (hr.of_uset ..)
      (hx.of_uset ..) (hy.of_uset ..) (j + 1) p.2
  else
    (arr, b)
termination_by n.toNat - j.toNat
decreasing_by
  have := USize.lt_iff_toNat_lt.1 h
  rw [USize.toNat_add_one_of_lt h]
  lia

public theorem size_foldUInPlace2 {β : Type} (n : USize)
    (f : (j : USize) → j < n → L → L → β → L × β) (arr : A)
    (rs xs ys : USize) (hr : LoopBound arr rs n) (hx : LoopBound arr xs n)
    (hy : LoopBound arr ys n) (j : USize) (b : β) :
    LA.size (foldUInPlace2 n f arr rs xs ys hr hx hy j b).1 = LA.size arr := by
  induction arr, hr, hx, hy, j, b using foldUInPlace2.induct (R := R) n f rs xs ys with
  | case1 arr hr hx hy j b h p ih =>
    rw [foldUInPlace2]
    simp only [h, ↓reduceDIte]
    exact ih.trans (R.size_uset ..)
  | case2 arr hr hx hy j b h =>
    rw [foldUInPlace2]
    simp only [h, ↓reduceDIte]

/--
`foldUInPlace2` followed by `g` on the new array and the last accumulator, which the loop calls
itself instead of returning a pair. `g` also receives a proof that the size is unchanged.
-/
@[expose]
public def foldUInPlace2Then {β γ : Type} (n : USize)
    (f : (j : USize) → j < n → L → L → β → L × β) (arr : A)
    (rs xs ys : USize) (hr : LoopBound arr rs n) (hx : LoopBound arr xs n)
    (hy : LoopBound arr ys n) (j : USize) (b : β)
    (g : (arr' : A) → LA.size arr' = LA.size arr → β → γ) : γ :=
  g (foldUInPlace2 n f arr rs xs ys hr hx hy j b).1 (size_foldUInPlace2 ..)
    (foldUInPlace2 n f arr rs xs ys hr hx hy j b).2

/--
The value of `foldUInPlace2` for a step with a linear carry law: if every step turns limbs `x`,
`y` and the accumulator `c` into a limb `out` and an accumulator `c'` with
`out + 2ʷ P c' + ux x + uy y + Q c = vx x + vy y + 2ʷ Q c' + P c` and keeps the invariant `I` of
the accumulator, then the limbs written and the last accumulator satisfy the same law with the
values of the windows, as long as the windows read are not overwritten before they are read. `P`
is a carry and `Q` a borrow.
-/
public theorem foldUInPlace2_spec {β : Type} (n : USize)
    (f : (j : USize) → j < n → L → L → β → L × β) (P Q : β → Nat)
    (ux uy vx vy : Nat) (I : β → Prop) (inv : ∀ j h x y c, I c → I (f j h x y c).2)
    (law : ∀ j h x y c, I c → LA.val (f j h x y c).1 + 2 ^ LA.w * P (f j h x y c).2 +
      ux * LA.val x + uy * LA.val y + Q c =
        vx * LA.val x + vy * LA.val y + 2 ^ LA.w * Q (f j h x y c).2 + P c)
    (arr : A) (rs xs ys : USize) (hr : LoopBound arr rs n) (hx : LoopBound arr xs n)
    (hy : LoopBound arr ys n)
    (hdx : rs.toNat ≤ xs.toNat ∨ xs.toNat + n.toNat ≤ rs.toNat)
    (hdy : rs.toNat ≤ ys.toNat ∨ ys.toNat + n.toNat ≤ rs.toNat) (j : USize) (b : β) (hb : I b) :
    LA.size (foldUInPlace2 n f arr rs xs ys hr hx hy j b).1 = LA.size arr ∧
      I (foldUInPlace2 n f arr rs xs ys hr hx hy j b).2 ∧
      (∀ i, (i < rs.toNat + j.toNat ∨ rs.toNat + n.toNat ≤ i) →
        LA.get (foldUInPlace2 n f arr rs xs ys hr hx hy j b).1 i = LA.get arr i) ∧
      LimbArray.valAt (foldUInPlace2 n f arr rs xs ys hr hx hy j b).1 (rs.toNat + j.toNat)
          (n.toNat - j.toNat) +
        2 ^ (LA.w * (n.toNat - j.toNat)) * P (foldUInPlace2 n f arr rs xs ys hr hx hy j b).2 +
        ux * LimbArray.valAt arr (xs.toNat + j.toNat) (n.toNat - j.toNat) +
        uy * LimbArray.valAt arr (ys.toNat + j.toNat) (n.toNat - j.toNat) + Q b =
      vx * LimbArray.valAt arr (xs.toNat + j.toNat) (n.toNat - j.toNat) +
        vy * LimbArray.valAt arr (ys.toNat + j.toNat) (n.toNat - j.toNat) +
        2 ^ (LA.w * (n.toNat - j.toNat)) * Q (foldUInPlace2 n f arr rs xs ys hr hx hy j b).2 +
        P b := by
  induction arr, hr, hx, hy, j, b using foldUInPlace2.induct (R := R) n f rs xs ys with
  | case1 arr hr hx hy j b h p ih =>
    rw [foldUInPlace2]
    simp only [h, ↓reduceDIte]
    have hI := inv j h (R.uget arr (xs + j) (hx.uset_bound h)) (R.uget arr (ys + j) (hy.uset_bound h))
      b hb
    have hj := USize.lt_iff_toNat_lt.1 h
    have hj₁ := USize.toNat_add_one_of_lt h
    have hri := hr.toNat_add h
    have hxi := hx.toNat_add h
    have hyi := hy.toNat_add h
    obtain ⟨ih₁, ih₀, ih₂, ih₃⟩ := ih hI
    rw [hj₁] at ih₂ ih₃
    rw [R.size_uset] at ih₁
    have hv : LA.get (foldUInPlace2 n f (R.uset arr (rs + j) p.1 (hr.uset_bound h)) rs xs ys
        (hr.of_uset ..) (hx.of_uset ..) (hy.of_uset ..) (j + 1) p.2).1 (rs.toNat + j.toNat) =
          p.1 := by
      rw [ih₂ _ (.inl (by lia)), R.get_uset]
      simp [hri]
    have hX : LimbArray.valAt (R.uset arr (rs + j) p.1 (hr.uset_bound h))
        (xs.toNat + (j.toNat + 1)) (n.toNat - (j.toNat + 1)) =
          LimbArray.valAt arr (xs.toNat + (j.toNat + 1)) (n.toNat - (j.toNat + 1)) :=
      valAt_uset_of _ _ _ _ _ _ (by rw [hri]; lia)
    have hY : LimbArray.valAt (R.uset arr (rs + j) p.1 (hr.uset_bound h))
        (ys.toNat + (j.toNat + 1)) (n.toNat - (j.toNat + 1)) =
          LimbArray.valAt arr (ys.toNat + (j.toNat + 1)) (n.toNat - (j.toNat + 1)) :=
      valAt_uset_of _ _ _ _ _ _ (by rw [hri]; lia)
    have hx' : R.uget arr (xs + j) (hx.uset_bound h) = LA.get arr (xs.toNat + j.toNat) := by
      rw [R.uget_eq, hxi]
    have hy' : R.uget arr (ys + j) (hy.uset_bound h) = LA.get arr (ys.toNat + j.toNat) := by
      rw [R.uget_eq, hyi]
    refine ⟨ih₁, ih₀, fun i hi => ?_, ?_⟩
    · rw [ih₂ i (by lia), R.get_uset]
      simp only [hri]
      split <;> lia
    · rw [hX, hY] at ih₃
      obtain ⟨k, hk⟩ : ∃ k, n.toNat - j.toNat = k + 1 := ⟨n.toNat - j.toNat - 1, by lia⟩
      rw [show n.toNat - (j.toNat + 1) = k by lia, ← Nat.add_assoc, ← Nat.add_assoc,
        ← Nat.add_assoc] at ih₃
      have hl := law j h (R.uget arr (xs + j) (hx.uset_bound h))
        (R.uget arr (ys + j) (hy.uset_bound h)) b hb
      rw [hx', hy'] at hl
      rw [hk, LimbArray.valAt_succ, LimbArray.valAt_succ, LimbArray.valAt_succ, hv, Nat.mul_succ,
        Nat.pow_add]
      show _ + _ * P (foldUInPlace2 n f (R.uset arr (rs + j) p.1 (hr.uset_bound h)) rs xs ys
        (hr.of_uset ..) (hx.of_uset ..) (hy.of_uset ..) (j + 1) p.2).2 + _ + _ + _ = _
      generalize (foldUInPlace2 n f (R.uset arr (rs + j) p.1 (hr.uset_bound h)) rs xs ys
        (hr.of_uset ..) (hx.of_uset ..) (hy.of_uset ..) (j + 1) p.2) = q at *
      simp only [p] at *
      generalize f j h (LA.get arr (xs.toNat + j.toNat)) (LA.get arr (ys.toNat + j.toNat)) b = p'
        at *
      generalize LimbArray.valAt q.1 _ _ = V at *
      generalize LimbArray.valAt arr (xs.toNat + j.toNat + 1) k = X at *
      generalize LimbArray.valAt arr (ys.toNat + j.toNat + 1) k = Y at *
      generalize 2 ^ (LA.w * k) = B at *
      generalize 2 ^ LA.w = W at *
      grind
  | case2 arr hr hx hy j b h =>
    rw [foldUInPlace2]
    have : n.toNat - j.toNat = 0 := by have := USize.lt_iff_toNat_lt (a := j) (b := n); lia
    simp [h, this, Nat.add_comm, hb]

end WordArray

open WordArray in
/--
The in-place folds of lean4-scalar-arrays on arrays of words, over one window and over one window
while reading two others of the same array, which run in place of `foldUInPlaceThen` and
`foldUInPlace2Then`.
-/
public class WordFolds (A : Type) (L : outParam Type) [LA : LimbArray A L] [WordArray A L] where
  /-- `foldUInPlace2Then`, compiled. -/
  fold2Then : {β γ : Type} → (n : USize) → ((j : USize) → j < n → L → L → β → L × β) →
    (arr : A) → (rs xs ys : USize) → LoopBound arr rs n → LoopBound arr xs n →
    LoopBound arr ys n → USize → β → ((arr' : A) → LA.size arr' = LA.size arr → β → γ) → γ
  fold2Then_eq : ∀ {β γ : Type} n f arr rs xs ys hr hx hy j b g,
    @fold2Then β γ n f arr rs xs ys hr hx hy j b g =
      foldUInPlace2Then n f arr rs xs ys hr hx hy j b g
  /-- `foldUInPlaceThen`, compiled. -/
  foldThen : {β γ : Type} → (n : USize) → ((j : USize) → j < n → L → β → L × β) → (arr : A) →
    (rs : USize) → LoopBound arr rs n → USize → β →
    ((arr' : A) → LA.size arr' = LA.size arr → β → γ) → γ
  foldThen_eq : ∀ {β γ : Type} n f arr rs hr j b g,
    @foldThen β γ n f arr rs hr j b g = foldUInPlaceThen n f arr rs hr j b g

namespace WordArray

variable {A L : Type} [LA : LimbArray A L] [R : WordArray A L] [F : WordFolds A L]

/--
`fold2Then` as an intermediate result: the array and the accumulator of `foldUInPlace2`, and the
size proof that `g` receives, as variables. Proofs about a chain of loops go through this, so
that the later loops mention variables, not the earlier loops.
-/
public theorem fold2Then_cases {β γ : Type} {n : USize}
    {f : (j : USize) → j < n → L → L → β → L × β} {arr : A}
    {rs xs ys : USize} {hr : LoopBound arr rs n} {hx : LoopBound arr xs n}
    {hy : LoopBound arr ys n} {j : USize} {b : β}
    {g : (arr' : A) → LA.size arr' = LA.size arr → β → γ} {G : γ}
    (h : F.fold2Then n f arr rs xs ys hr hx hy j b g = G) :
    ∃ a, ∃ ha : LA.size a = LA.size arr, ∃ c,
      foldUInPlace2 n f arr rs xs ys hr hx hy j b = (a, c) ∧ g a ha c = G := by
  rw [F.fold2Then_eq, foldUInPlace2Then] at h
  exact ⟨_, _, _, rfl, h⟩

/-- `foldThen` as an intermediate result, like `fold2Then_cases`. -/
public theorem foldThen_cases {β γ : Type} {n : USize} {f : (j : USize) → j < n → L → β → L × β}
    {arr : A} {rs : USize} {hr : LoopBound arr rs n} {j : USize} {b : β}
    {g : (arr' : A) → LA.size arr' = LA.size arr → β → γ} {G : γ}
    (h : F.foldThen n f arr rs hr j b g = G) :
    ∃ a, ∃ ha : LA.size a = LA.size arr, ∃ c,
      foldUInPlace n f arr rs hr j b = (a, c) ∧ g a ha c = G := by
  rw [F.foldThen_eq, foldUInPlaceThen] at h
  exact ⟨_, _, _, rfl, h⟩

public theorem foldThen_eq' {β γ : Type} (n : USize) (f : (j : USize) → j < n → L → β → L × β)
    (arr : A) (rs : USize) (hr : LoopBound arr rs n) (j : USize) (b : β)
    (g : (arr' : A) → LA.size arr' = LA.size arr → β → γ) :
    F.foldThen n f arr rs hr j b g =
      g (foldUInPlace n f arr rs hr j b).1 (size_foldUInPlace ..) (foldUInPlace n f arr rs hr j b).2 := by
  rw [F.foldThen_eq, foldUInPlaceThen]

public theorem fold2Then_eq' {β γ : Type} (n : USize)
    (f : (j : USize) → j < n → L → L → β → L × β) (arr : A)
    (rs xs ys : USize) (hr : LoopBound arr rs n) (hx : LoopBound arr xs n)
    (hy : LoopBound arr ys n) (j : USize) (b : β)
    (g : (arr' : A) → LA.size arr' = LA.size arr → β → γ) :
    F.fold2Then n f arr rs xs ys hr hx hy j b g =
      g (foldUInPlace2 n f arr rs xs ys hr hx hy j b).1 (size_foldUInPlace2 ..)
        (foldUInPlace2 n f arr rs xs ys hr hx hy j b).2 := by
  rw [F.fold2Then_eq, foldUInPlace2Then]

end WordArray

end MPN
