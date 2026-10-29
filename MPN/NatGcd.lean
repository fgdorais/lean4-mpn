/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import MPN.Natural
public import MPN.WordGcd

/-!
# The greatest common divisor of natural numbers

`GNat.gcd x y` is `Nat.gcd x.toNat y.toNat`, by the same algorithms on both libraries:

* Euclid's algorithm on words when both numbers are, and on pairs of words (`gcd2`, like GMP's
  `mpn_gcd_22`) when both fit in the instance's two words;
* Lehmer's algorithm (`gcdLehmer`) above: the instance's step on the leading words of the two
  numbers, applied to the full numbers when it makes them smaller, and otherwise one step of
  Euclid's algorithm;
* reductions by the instance's half-gcd while they make the smaller number smaller, from `half`
  limbs of it (`gcdWith`).

The instance of `GcdLimbs A` gives the parts that depend on the width of the limbs: the high word
of a product of words, the remainder of two words by one, the two words of a small number, and
Lehmer's step and half-gcd with their laws, which are that they keep the greatest common divisor.
-/

namespace MPN

/--
The parts of the greatest common divisor of `GNat A` that depend on the limbs, with their laws:
nothing more is needed of Lehmer's step and of half-gcd than that they keep the greatest common
divisor; `size` and `half` only affect speed.
-/
public class GcdLimbs (A : Type) [C : NatLimbs A] where
  /-- The high word of `a b`. -/
  mulh : UInt64 → UInt64 → UInt64
  toNat_mulh : ∀ a b, (mulh a b).toNat = a.toNat * b.toNat / 2 ^ 64
  /-- `(ah 2⁶⁴ + al) % bl`. -/
  rem2 : UInt64 → UInt64 → UInt64 → UInt64
  toNat_rem2 : ∀ ah al bl, 0 < bl.toNat →
    (rem2 ah al bl).toNat = (ah.toNat * 2 ^ 64 + al.toNat) % bl.toNat
  /-- Whether `gcd2` should take a number, as two words `hi` and `lo`. -/
  fits2 : GNat A → Bool
  hi : GNat A → UInt64
  lo : GNat A → UInt64
  val_two : ∀ x, fits2 x = true → (hi x).toNat * 2 ^ 64 + (lo x).toNat = x.toNat
  /-- Lehmer's step on `x ≥ y`: two numbers with the same greatest common divisor, or none. -/
  lehmer : GNat A → GNat A → Option (GNat A × GNat A)
  gcd_lehmer : ∀ x y p, lehmer x y = some p →
    Nat.gcd p.1.toNat p.2.toNat = Nat.gcd x.toNat y.toNat
  /-- One reduction of `x ≥ y` by half-gcd. -/
  hgcd : GNat A → GNat A → GNat A × GNat A
  gcd_hgcd : ∀ x y, Nat.gcd (hgcd x y).1.toNat (hgcd x y).2.toNat = Nat.gcd x.toNat y.toNat
  /-- The size of a number, in limbs. -/
  size : GNat A → Nat
  /-- The size of the smaller number from which `gcd` reduces by half-gcd. -/
  half : Nat

namespace GNat

variable {A : Type} [C : NatLimbs A] [G : GcdLimbs A]

/-! ## Two words -/

/-- The number `h 2⁶⁴ + l`. -/
@[expose] public def v2 (h l : UInt64) : Nat := h.toNat * 2 ^ 64 + l.toNat

/-- `(ah 2⁶⁴ + al) - (bh 2⁶⁴ + bl)` in two words. -/
@[inline, expose] public def sub2h (ah al bh bl : UInt64) : UInt64 :=
  ah - bh - (if al < bl then 1 else 0)

private theorem toNat_sub_add (a b : UInt64) :
    (a - b).toNat + b.toNat = a.toNat + (if a.toNat < b.toNat then 2 ^ 64 else 0) := by
  rw [UInt64.toNat_sub]
  have := a.toNat_lt; have := b.toNat_lt
  split
  · rw [Nat.mod_eq_of_lt (by lia)]; lia
  · rw [show 2 ^ 64 - b.toNat + a.toNat = a.toNat - b.toNat + 2 ^ 64 by lia, Nat.add_mod_right,
      Nat.mod_eq_of_lt (by lia)]
    lia

private theorem v2_sub (ah al bh bl : UInt64) (h : v2 bh bl ≤ v2 ah al) :
    v2 (sub2h ah al bh bl) (al - bl) = v2 ah al - v2 bh bl := by
  unfold v2 sub2h at *
  have := al.toNat_lt; have := bl.toNat_lt; have := ah.toNat_lt; have := bh.toNat_lt
  have := (ah - bh).toNat_lt; have := (al - bl).toNat_lt
  have e₁ := toNat_sub_add al bl
  have e₂ := toNat_sub_add ah bh
  have e₃ := toNat_sub_add (ah - bh) (if al < bl then 1 else 0)
  have := (ah - bh - if al < bl then 1 else 0).toNat_lt
  generalize ah - bh - (if al < bl then 1 else 0) = t at *
  by_cases hl : al < bl
  · have hl' := UInt64.lt_iff_toNat_lt.1 hl
    simp only [hl, hl', ↓reduceIte, UInt64.toNat_one] at e₁ e₃
    split at e₃ <;> lia
  · have hl' := mt UInt64.lt_iff_toNat_lt.2 hl
    simp only [hl, hl', ↓reduceIte, UInt64.toNat_zero] at e₁ e₃
    split at e₃ <;> lia

/-- Whether `ah 2⁶⁴ + al < bh 2⁶⁴ + bl`. -/
@[inline, expose] public def lt2 (ah al bh bl : UInt64) : Bool := ah < bh || (ah == bh && al < bl)

private theorem lt2_iff (ah al bh bl : UInt64) : lt2 ah al bh bl = true ↔ v2 ah al < v2 bh bl := by
  unfold lt2 v2
  have := al.toNat_lt; have := bl.toNat_lt
  simp only [Bool.or_eq_true, decide_eq_true_eq, Bool.and_eq_true, beq_iff_eq,
    UInt64.lt_iff_toNat_lt, ← UInt64.toNat_inj]
  constructor
  · rintro (h | ⟨h₁, h₂⟩) <;> lia
  · intro h
    rcases Nat.lt_or_ge ah.toNat bh.toNat with h' | h'
    · exact .inl h'
    · exact .inr ⟨by lia, by lia⟩

/-- The quotient estimate of a step: `⌊ah / (bh + 1)⌋`, at least `1`. -/
@[inline, expose] public def q2 (ah bh : UInt64) : UInt64 :=
  let q := ah / (bh + 1); if q = 0 then 1 else q

private theorem q2_mul_le (ah al bh bl : UInt64) (h : v2 bh bl ≤ v2 ah al) :
    (q2 ah bh).toNat * v2 bh bl ≤ v2 ah al ∧ 1 ≤ (q2 ah bh).toNat := by
  unfold q2
  dsimp only
  split
  · simp only [UInt64.toNat_one]; lia
  · rename_i hq
    have hq' : (ah / (bh + 1)).toNat ≠ 0 := fun e => hq (UInt64.toNat_inj.1 (by rw [e]; rfl))
    rw [UInt64.toNat_div] at hq' ⊢
    have hb1 : (bh + 1).toNat = bh.toNat + 1 := by
      rw [UInt64.toNat_add, UInt64.toNat_one]
      rcases Nat.lt_or_ge (bh.toNat + 1) (2 ^ 64) with e | e
      · exact Nat.mod_eq_of_lt e
      · exfalso; apply hq'
        rw [UInt64.toNat_add, UInt64.toNat_one,
          show bh.toNat + 1 = 2 ^ 64 by have := bh.toNat_lt; lia]
        simp
    rw [hb1] at hq' ⊢
    have hd := Nat.div_mul_le_self ah.toNat (bh.toNat + 1)
    have := bl.toNat_lt
    unfold v2
    constructor
    · have : ah.toNat / (bh.toNat + 1) * (bh.toNat * 2 ^ 64 + bl.toNat) ≤
          ah.toNat / (bh.toNat + 1) * ((bh.toNat + 1) * 2 ^ 64) :=
        Nat.mul_le_mul_left _ (by lia)
      have : ah.toNat / (bh.toNat + 1) * ((bh.toNat + 1) * 2 ^ 64) ≤ ah.toNat * 2 ^ 64 := by
        rw [← Nat.mul_assoc]; exact Nat.mul_le_mul_right _ hd
      lia
    · lia

variable (A) in
/-- The high word of `q (bh 2⁶⁴ + bl)`. -/
@[inline, expose] public def mul2h (q bh bl : UInt64) : UInt64 := q * bh + G.mulh q bl

private theorem v2_mul (q bh bl : UInt64) (h : q.toNat * v2 bh bl < 2 ^ 128) :
    v2 (mul2h A q bh bl) (q * bl) = q.toNat * v2 bh bl := by
  unfold v2 mul2h at *
  have hm := Nat.div_add_mod (q.toNat * bl.toNat) (2 ^ 64)
  rw [UInt64.toNat_add, UInt64.toNat_mul, G.toNat_mulh, UInt64.toNat_mul]
  have : q.toNat * bh.toNat * 2 ^ 64 + q.toNat * bl.toNat < 2 ^ 128 := by
    rw [Nat.mul_add, ← Nat.mul_assoc] at h; exact h
  have : q.toNat * bh.toNat < 2 ^ 64 := by
    rcases Nat.lt_or_ge (q.toNat * bh.toNat) (2 ^ 64) with e | e
    · exact e
    · exfalso
      have := Nat.mul_le_mul_right (2 ^ 64) e
      lia
  rw [Nat.mod_eq_of_lt (a := q.toNat * bh.toNat) this]
  have : q.toNat * bh.toNat + q.toNat * bl.toNat / 2 ^ 64 < 2 ^ 64 := by
    rcases Nat.lt_or_ge (q.toNat * bh.toNat + q.toNat * bl.toNat / 2 ^ 64) (2 ^ 64) with e | e
    · exact e
    · exfalso
      have := Nat.mul_le_mul_right (2 ^ 64) e
      lia
  rw [Nat.mod_eq_of_lt this]
  lia

/-- A step of `gcd2`: `a = (a - q b) + q b` with `q ≥ 1`. -/
private theorem v2_step (ah al bh bl : UInt64) (h : ¬lt2 ah al bh bl = true) :
    v2 (sub2h ah al (mul2h A (q2 ah bh) bh bl) (q2 ah bh * bl)) (al - q2 ah bh * bl) +
      (q2 ah bh).toNat * v2 bh bl = v2 ah al ∧ 1 ≤ (q2 ah bh).toNat := by
  rw [lt2_iff] at h
  have hle : v2 bh bl ≤ v2 ah al := Nat.le_of_not_lt h
  obtain ⟨hq, h1⟩ := q2_mul_le ah al bh bl hle
  have h128 : v2 ah al < 2 ^ 128 := by
    unfold v2; have := ah.toNat_lt; have := al.toNat_lt; lia
  have hm := v2_mul (A := A) (q2 ah bh) bh bl (Nat.lt_of_le_of_lt hq h128)
  have hq' : v2 (mul2h A (q2 ah bh) bh bl) (q2 ah bh * bl) ≤ v2 ah al := by rw [hm]; exact hq
  rw [v2_sub _ _ _ _ hq', hm]
  exact ⟨Nat.sub_add_cancel hq, h1⟩

/--
The greatest common divisor of `ah 2⁶⁴ + al` and `bh 2⁶⁴ + bl` by Euclid's algorithm on pairs of
words, like GMP's `mpn_gcd_22`: steps `a - q b` with the estimate `q2` of the quotient, which is
never too large, until `b` fits in a word, then one remainder by the instance's `rem2` and
`wordGcd`.
-/
@[expose, specialize] public def gcd2 (ah al bh bl : UInt64) : GNat A :=
  if bh = 0 then
    if bl = 0 then wideOf al ah
    else small (wordGcd bl (G.rem2 ah al bl))
  else if _h : lt2 ah al bh bl then gcd2 bh bl ah al
  else
    let q := q2 ah bh
    gcd2 bh bl (sub2h ah al (mul2h A q bh bl) (q * bl)) (al - q * bl)
termination_by v2 ah al + v2 bh bl + (if v2 ah al < v2 bh bl then 1 else 0)
decreasing_by
  · rw [lt2_iff] at _h
    generalize v2 ah al = A at *
    generalize v2 bh bl = B at *
    split <;> (try split) <;> lia
  · rename_i hb
    obtain ⟨e, h1⟩ := v2_step (A := A) ah al bh bl _h
    have hpos : 2 ^ 64 ≤ v2 bh bl := by
      have : bh.toNat ≠ 0 := fun e => hb (UInt64.toNat_inj.1 (by rw [e]; rfl))
      unfold v2; lia
    have hb1 : v2 bh bl ≤ (q2 ah bh).toNat * v2 bh bl := Nat.le_mul_of_pos_left _ h1
    rw [lt2_iff] at _h
    generalize v2 (sub2h ah al (mul2h A (q2 ah bh) bh bl) (q2 ah bh * bl))
      (al - q2 ah bh * bl) = R at *
    generalize v2 ah al = A at *
    generalize v2 bh bl = B at *
    generalize (q2 ah bh).toNat * B = P at *
    split <;> lia

public theorem toNat_gcd2 (ah al bh bl : UInt64) :
    (gcd2 ah al bh bl : GNat A).toNat = Nat.gcd (v2 ah al) (v2 bh bl) := by
  induction ah, al, bh, bl using gcd2.induct (A := A) with
  | case1 ah al =>
    rw [gcd2, ite_eq_left rfl, ite_eq_left rfl, toNat_wideOf]
    simp only [v2, UInt64.toNat_zero, Nat.zero_mul, Nat.zero_add, Nat.gcd_zero_right]
    lia
  | case2 ah al bl hl =>
    rw [gcd2, ite_eq_left rfl, ite_eq_right hl]
    have hl' : 0 < bl.toNat :=
      Nat.pos_of_ne_zero fun e => hl (UInt64.toNat_inj.1 (by rw [e]; rfl))
    rw [toNat_small, toNat_wordGcd, G.toNat_rem2 _ _ _ hl', show v2 0 bl = bl.toNat by simp [v2],
      ← v2, Nat.gcd_comm, ← Nat.gcd_rec, Nat.gcd_comm]
  | case3 ah al bh bl hb h ih =>
    rw [gcd2, ite_eq_right hb, dite_eq_left h, ih, Nat.gcd_comm]
  | case4 ah al bh bl hb h q ih =>
    simp only [q] at ih
    rw [gcd2, ite_eq_right hb, dite_eq_right h, ih]
    obtain ⟨e, -⟩ := v2_step (A := A) ah al bh bl h
    rw [← e, Nat.gcd_comm (_ + _), Nat.gcd_add_mul_right_right]

/-! ## Lehmer's algorithm -/

/-- Whether `x = 0`. -/
@[inline, expose] public def isZero : GNat A → Bool
  | small n => n == 0
  | large _ _ => false

omit G in
private theorem isZero_iff (x : GNat A) : isZero x = true ↔ x.toNat = 0 := by
  cases x with
  | small n =>
    simp only [isZero, beq_iff_eq, toNat_small]
    exact ⟨fun h => by rw [h]; rfl, fun h => UInt64.toNat_inj.1 (by rw [h]; rfl)⟩
  | large a ha =>
    simp only [isZero, Bool.false_eq_true, false_iff]
    have := ha.2
    show C.val a ≠ 0
    lia

/--
The greatest common divisor by Lehmer's algorithm: the instance's step on `x ≥ y`, when it makes
the second number smaller, and otherwise one step of Euclid's algorithm; on words when both
numbers are, and on pairs of words (`gcd2`) when both fit in two.
-/
@[expose, specialize] public def gcdLehmer (x y : GNat A) : GNat A :=
  match x, y with
  | small a, small b => small (wordGcd a b)
  | x, y =>
    if G.fits2 x && G.fits2 y then gcd2 (G.hi x) (G.lo x) (G.hi y) (G.lo y)
    else if _h : isZero y then x
    else if blt x y then gcdLehmer y (mod x y)
    else
      match G.lehmer x y with
      | some p => if _hy : blt p.2 y then gcdLehmer p.1 p.2 else gcdLehmer y (mod x y)
      | none => gcdLehmer y (mod x y)
termination_by y.toNat
decreasing_by
  all_goals first
    | (rw [blt_iff] at _hy; exact _hy)
    | (have : y.toNat ≠ 0 := fun h' => _h ((isZero_iff y).2 h')
       rw [toNat_mod]
       exact Nat.mod_lt _ (by lia))

omit G in
/-- One step of Euclid's algorithm keeps the greatest common divisor. -/
private theorem gcd_mod_step (x y : GNat A) :
    Nat.gcd y.toNat (mod x y).toNat = Nat.gcd x.toNat y.toNat := by
  rw [toNat_mod, Nat.gcd_comm x.toNat y.toNat, Nat.gcd_rec y.toNat x.toNat, Nat.gcd_comm]

public theorem toNat_gcdLehmer (x y : GNat A) :
    (gcdLehmer x y).toNat = Nat.gcd x.toNat y.toNat := by
  induction x, y using gcdLehmer.induct with
  | case1 a b => rw [gcdLehmer]; exact toNat_wordGcd a b
  | case2 x y hxy hf =>
    rw [gcdLehmer]
    · simp only [Bool.and_eq_true] at hf
      rw [ite_eq_left (by simp [hf.1, hf.2]), toNat_gcd2, v2, v2, G.val_two x hf.1, G.val_two y hf.2]
    · exact hxy
  | case3 x y hxy hf h =>
    rw [gcdLehmer]
    · rw [ite_eq_right hf, dite_eq_left h, show y.toNat = 0 from (isZero_iff y).1 h, Nat.gcd_zero_right]
    · exact hxy
  | case4 x y hxy hf h hlt ih =>
    rw [gcdLehmer]
    · rw [ite_eq_right hf, dite_eq_right h, ite_eq_left hlt, ih, gcd_mod_step]
    · exact hxy
  | case5 x y hxy hf h hlt p hp hy ih =>
    rw [gcdLehmer]
    · rw [ite_eq_right hf, dite_eq_right h, ite_eq_right hlt]
      simp only [hp, dite_eq_left hy, ih, G.gcd_lehmer _ _ _ hp]
    · exact hxy
  | case6 x y hxy hf h hlt p hp hy ih =>
    rw [gcdLehmer]
    · rw [ite_eq_right hf, dite_eq_right h, ite_eq_right hlt]
      simp only [hp, dite_eq_right hy, ih, gcd_mod_step]
    · exact hxy
  | case7 x y hxy hf h hlt hp ih =>
    rw [gcdLehmer]
    · rw [ite_eq_right hf, dite_eq_right h, ite_eq_right hlt]
      simp only [hp, ih, gcd_mod_step]
    · exact hxy

/-! ## Half-gcd -/

/-- The smaller of two numbers. -/
@[inline, expose] public def minNat (x y : GNat A) : GNat A := if blt x y then x else y

omit G in
private theorem toNat_minNat_le (x y : GNat A) : (minNat x y).toNat ≤ y.toNat := by
  unfold minNat
  split
  · rename_i h; rw [blt_iff] at h; lia
  · exact Nat.le_refl _

/-- The instance's half-gcd on the larger number first. -/
@[inline, expose] public def hgcdOrd (x y : GNat A) : GNat A × GNat A :=
  if blt x y then G.hgcd y x else G.hgcd x y

private theorem gcd_hgcdOrd (x y : GNat A) :
    Nat.gcd (hgcdOrd x y).1.toNat (hgcdOrd x y).2.toNat = Nat.gcd x.toNat y.toNat := by
  unfold hgcdOrd
  split
  · rw [G.gcd_hgcd, Nat.gcd_comm]
  · rw [G.gcd_hgcd]

/--
The greatest common divisor: from `half` limbs of the smaller number, reductions by half-gcd
while they make it smaller, and Lehmer's algorithm (`gcdLehmer`) below and otherwise.
-/
@[expose, specialize] public def gcdWith (half : Nat) (x y : GNat A) : GNat A :=
  if half ≤ G.size (minNat x y) then
    let p := hgcdOrd x y
    if _hy : blt p.2 (minNat x y) then gcdWith half p.1 p.2 else gcdLehmer x y
  else gcdLehmer x y
termination_by y.toNat
decreasing_by
  rw [blt_iff] at _hy
  have := toNat_minNat_le x y
  lia

@[simp] public theorem toNat_gcdWith (half : Nat) (x y : GNat A) :
    (gcdWith half x y).toNat = Nat.gcd x.toNat y.toNat := by
  induction x, y using gcdWith.induct (G := G) half with
  | case1 x y h p hy ih =>
    rw [gcdWith, ite_eq_left h]
    simp only [p] at hy ih
    rw [dite_eq_left hy, ih, gcd_hgcdOrd]
  | case2 x y h p hy =>
    rw [gcdWith, ite_eq_left h]
    simp only [p] at hy
    rw [dite_eq_right hy, toNat_gcdLehmer]
  | case3 x y h =>
    rw [gcdWith, ite_eq_right h, toNat_gcdLehmer]

/-- The greatest common divisor, with half-gcd from the instance's `half` limbs (`gcdWith`). -/
@[expose, specialize] public def gcd (x y : GNat A) : GNat A := gcdWith G.half x y

@[simp] public theorem toNat_gcd (x y : GNat A) :
    (gcd x y).toNat = Nat.gcd x.toNat y.toNat := toNat_gcdWith _ x y

/-- The least common multiple, `x / gcd x y * y`, and `0` when either is `0`. -/
@[expose, specialize] public def lcm (x y : GNat A) : GNat A :=
  let g := gcd x y
  if isZero g then small 0 else mul (div x g) y

@[simp] public theorem toNat_lcm (x y : GNat A) :
    (lcm x y).toNat = Nat.lcm x.toNat y.toNat := by
  unfold lcm
  dsimp only
  split
  · rename_i h
    rw [isZero_iff, toNat_gcd, Nat.gcd_eq_zero_iff] at h
    rw [toNat_small, UInt64.toNat_zero, h.1, Nat.lcm_zero_left]
  · rw [toNat_mul, toNat_div, toNat_gcd, Nat.lcm, Nat.div_mul_right_comm (Nat.gcd_dvd_left _ _)]

end GNat

end MPN
