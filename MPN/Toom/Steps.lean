/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import MPN.Toom.Ops

/-!
# Steps of the Toom methods

The passes of `ToomOps` as equations on values, for the interpolations: each takes the value `Q`
of the window it writes and gives the value `V` of the result from an equation `Q = … + V`, so
that a chain of them needs no subtraction or division on `Nat`. Then the recombination: clearing
the middle of the result and adding a coefficient at its place.
-/

namespace MPN.Toom

open LimbArray

variable {A L : Type} [LA : LimbArray A L] [R : ToomOps A L]

/-- A multiplier `m < 2³²` is a limb. -/
public theorem lt_limb {m : Nat} (h : m < 2 ^ 32) : m < 2 ^ LA.w :=
  Nat.lt_of_lt_of_le h (Nat.pow_le_pow_right (by decide) R.w_ge)

/-! ## Passes by values -/

public theorem sub_val {q : A} {o len : Nat} (h : o + len ≤ LA.size q) (s : A) (so sl : Nat)
    {Q S V : Nat} (hq : valAt q o len = Q) (hs : valAt s so sl = S) (hV : Q = S + V) :
    LA.size (R.subInto q o len s so sl) = LA.size q ∧
      valAt (R.subInto q o len s so sl) o len = V := by
  obtain ⟨w, e⟩ := R.subInto_spec q o len s so sl h (by lia)
  exact ⟨w.1, by rw [e]; lia⟩

public theorem subMul_val {q : A} {o len : Nat} (h : o + len ≤ LA.size q) (s : A) (so sl m : Nat)
    (hm : m < 2 ^ 32) {Q S V : Nat} (hq : valAt q o len = Q) (hs : valAt s so sl = S)
    (hV : Q = m * S + V) :
    LA.size (R.subMulInto q o len s so sl m) = LA.size q ∧
      valAt (R.subMulInto q o len s so sl m) o len = V := by
  obtain ⟨w, e⟩ := R.subMulInto_spec q o len s so sl m h (lt_limb hm) (by rw [hq, hs]; lia)
  exact ⟨w.1, by rw [e, hq, hs]; lia⟩

public theorem div_val {q : A} {o len : Nat} (h : o + len ≤ LA.size q) (d : Nat) (hd : d % 2 = 1)
    (hd' : d < 2 ^ 32) {Q V : Nat} (hq : valAt q o len = Q) (hV : Q = d * V) :
    LA.size (R.divExact q o len d) = LA.size q ∧ valAt (R.divExact q o len d) o len = V := by
  have hd0 : 0 < d := by lia
  obtain ⟨w, e⟩ := R.divExact_spec q o len d h hd (lt_limb hd') (by rw [hq, hV]; simp)
  exact ⟨w.1, by rw [e, hq, hV, Nat.mul_div_cancel_left _ hd0]⟩

public theorem shr_val {q : A} {o len : Nat} (h : o + len ≤ LA.size q) (s : Nat) (hs₀ : 0 < s)
    (hs : s < 32) {Q V : Nat} (hq : valAt q o len = Q) (hV : Q = 2 ^ s * V) :
    LA.size (R.shr q o len s) = LA.size q ∧ valAt (R.shr q o len s) o len = V := by
  obtain ⟨w, e⟩ := R.shr_spec q o len s h hs₀ (by have := R.w_ge; lia)
  exact ⟨w.1, by rw [e, hq, hV, Nat.mul_div_cancel_left _ (Nat.two_pow_pos _)]⟩

/-- `shlTop` halves an even value below `2^(w (len - 1))` into the limbs from the second on. -/
public theorem half_val {q : A} {len : Nat} (h : len ≤ LA.size q) (h₁ : 1 ≤ len) {Q V : Nat}
    (hq : valAt q 0 len = Q) (hV : Q = 2 * V) (hlt : Q < 2 ^ (LA.w * (len - 1))) :
    LA.size (R.shlTop q 0 len) = LA.size q ∧ valAt (R.shlTop q 0 len) 1 (len - 1) = V := by
  obtain ⟨w, e⟩ := R.shlTop_spec q 0 len (by lia)
  refine ⟨w.1, ?_⟩
  have hw := LA.w_pos
  have hB : 2 ^ LA.w = 2 * 2 ^ (LA.w - 1) := by
    rw [← Nat.pow_succ']; congr 1; lia
  have hP : 2 ^ (LA.w * len) = 2 ^ LA.w * 2 ^ (LA.w * (len - 1)) := by
    rw [← Nat.pow_add]; congr 1
    conv => lhs; rw [show len = (len - 1) + 1 by lia]
    rw [Nat.mul_succ, Nat.add_comm]
  -- The value times `2^(w - 1)` is `V 2ʷ`, which fits.
  have hfit : Q * 2 ^ (LA.w - 1) = 2 ^ LA.w * V := by rw [hV, hB]; grind
  have hVlt : V < 2 ^ (LA.w * (len - 1)) := by lia
  rw [hq, hfit, hP, Nat.mod_eq_of_lt (Nat.mul_lt_mul_of_pos_left hVlt (Nat.two_pow_pos _))] at e
  have hs := valAt_add (R.shlTop q 0 len) 0 1 (len - 1)
  rw [show 1 + (len - 1) = len by lia, e, valAt_one, Nat.mul_one, Nat.zero_add] at hs
  -- The low limb is `0`, and the others are `V`.
  have hlo := LA.val_lt (LA.get (R.shlTop q 0 len) 0)
  have h0 : LA.val (LA.get (R.shlTop q 0 len) 0) = 0 := by
    have := congrArg (· % 2 ^ LA.w) hs
    simp only [Nat.mul_mod_right, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hlo] at this
    exact this.symm
  rw [h0, Nat.zero_add] at hs
  exact (Nat.eq_of_mul_eq_mul_left (Nat.two_pow_pos _) hs).symm

omit R in
/-- The low `len - 1` limbs of a value that fits in them. -/
public theorem low_val {q : A} {len : Nat} (_hlen : 1 ≤ len) {Q : Nat} (hq : valAt q 0 len = Q)
    (hlt : Q < 2 ^ (LA.w * (len - 1))) : valAt q 0 (len - 1) = Q := by
  rw [valAt_mod q 0 (Nat.sub_le len 1), hq, Nat.mod_eq_of_lt hlt]

/-! ## The recombination -/

/-- The sum of the terms is at least each of them. -/
public theorem coeff_lt {P Q c x : Nat} (_hP : 0 < P) (h : P * c ≤ x) (hx : x < P * Q) : c < Q :=
  Nat.lt_of_mul_lt_mul_left (a := P) (by lia)

/--
Clearing limbs `[o + i, o + j)` of the window of `n` limbs from `o`: its value keeps its low `i`
limbs and the limbs from `j` on.
-/
public theorem zero_mid (d : A) (o n i j : Nat) (hd : o + n ≤ LA.size d) (hij : i ≤ j)
    (hj : j ≤ n) :
    Writes (R.zeroInto d (o + i) (j - i)) d (o + i) (j - i) ∧
      valAt (R.zeroInto d (o + i) (j - i)) o n =
        valAt d o i + 2 ^ (LA.w * j) * valAt d (o + j) (n - j) := by
  obtain ⟨w, e⟩ := R.zeroInto_spec d (o + i) (j - i) (by lia)
  refine ⟨w, ?_⟩
  have s₁ := valAt_add (R.zeroInto d (o + i) (j - i)) o i (j - i)
  have s₂ := valAt_add (R.zeroInto d (o + i) (j - i)) o j (n - j)
  rw [show i + (j - i) = j by lia, e, Nat.mul_zero, Nat.add_zero] at s₁
  rw [show j + (n - j) = n by lia, s₁] at s₂
  rw [s₂, w.valAt_eq (lo := o) (n := i) (by lia), w.valAt_eq (lo := o + j) (n := n - j) (by lia)]

/--
Adding a coefficient `c`, the window of `s` from `so` to its end at `sl`, at limb `off` of the
window of `n` limbs from `o`: only its limbs that fit, which hold all of `c` when the sum fits.
-/
public theorem add_coef (d : A) (o n off : Nat) (hd : o + n ≤ LA.size d) (hoff : off ≤ n)
    (s : A) (so sl c : Nat) (hc : valAt s so sl = c)
    (hlt : valAt d o n + 2 ^ (LA.w * off) * c < 2 ^ (LA.w * n)) :
    Writes (R.addInto d (o + off) (n - off) s so (min (n - off) sl)) d (o + off) (n - off) ∧
      valAt (R.addInto d (o + off) (n - off) s so (min (n - off) sl)) o n =
        valAt d o n + 2 ^ (LA.w * off) * c := by
  have hP : 2 ^ (LA.w * n) = 2 ^ (LA.w * off) * 2 ^ (LA.w * (n - off)) := by
    rw [← Nat.pow_add]; congr 1; rw [← Nat.mul_add]; congr 1; lia
  have hpos := Nat.two_pow_pos (LA.w * off)
  have hsplit : ∀ a : A, valAt a o n =
      valAt a o off + 2 ^ (LA.w * off) * valAt a (o + off) (n - off) := by
    intro a; rw [← valAt_add, show off + (n - off) = n by lia]
  have hcl : c < 2 ^ (LA.w * (n - off)) :=
    coeff_lt hpos (Nat.le_add_left _ _) (by rw [← hP]; exact hlt)
  -- The limbs read hold all of `c`.
  have hC : valAt s so (min (n - off) sl) = c := by
    rcases Nat.le_total (n - off) sl with hle | hle
    · rw [Nat.min_eq_left hle, valAt_mod s so hle, hc, Nat.mod_eq_of_lt hcl]
    · rw [Nat.min_eq_right hle, hc]
  have hlo : valAt d o off < 2 ^ (LA.w * off) := by
    have := valAt_lt d o off; rw [Nat.mul_comm] at this ⊢; exact this
  obtain ⟨w, e⟩ := R.addInto_spec d (o + off) (n - off) s so (min (n - off) sl) (by lia) (by
    rw [hsplit d, hP] at hlt
    rw [hC]
    refine Nat.lt_of_mul_lt_mul_left (a := 2 ^ (LA.w * off)) ?_
    rw [Nat.mul_add]
    generalize valAt d o off = L₀ at *
    generalize 2 ^ (LA.w * off) = P at *
    lia)
  refine ⟨w, ?_⟩
  rw [hsplit, hsplit d, e, hC, w.valAt_eq (lo := o) (n := off) (by lia), Nat.mul_add,
    Nat.add_assoc]

end MPN.Toom
