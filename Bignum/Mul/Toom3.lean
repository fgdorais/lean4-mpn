/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bignum.Add
public import Bignum.Sub
public import Bignum.Bits
public import Bignum.Mul.Limb

/-!
# Toom-3 multiplication

Splitting `a = a₀ + a₁ x + a₂ x²` and `b = b₀ + b₁ x + b₂ x²` at `x = βᵏ` makes `a * b` the value at
`x` of `c(t) = c₀ + c₁ t + c₂ t² + c₃ t³ + c₄ t⁴`, the product of the two polynomials. Its five
coefficients are recovered from five products of about a third of the size: `c₀ = a₀ b₀`,
`c₄ = a₂ b₂`, and the values `w₁ = c(1)`, `w₂ = c(2)` and `w₃ = c(3)` as products of the values
of the two polynomials at `1`, `2` and `3`.

GMP evaluates at `-1` instead of `3`, which makes the evaluations smaller but some intermediate
values negative. The points `0, 1, 2, 3, ∞` keep every intermediate value a natural number, since
the coefficients are, and each step of the interpolation

* `r₁ = w₁ - c₀ - c₄ = c₁ + c₂ + c₃`,
* `s₂ = (w₂ - c₀ - 16 c₄) / 2 = c₁ + 2 c₂ + 4 c₃`,
* `s₃ = (w₃ - c₀ - 81 c₄) / 3 = c₁ + 3 c₂ + 9 c₃`,
* `t₂ = s₂ - r₁ = c₂ + 3 c₃`,
* `t₃ = (s₃ - r₁) / 2 = c₂ + 4 c₃`,
* `c₃ = t₃ - t₂`, `c₂ = t₂ - 3 c₃`, `c₁ = r₁ - c₂ - c₃`

subtracts a part of what it subtracts from and divides exactly. The divisions avoid the hardware
divider: by `2` it is a shift by one bit, and by `3` a multiplication by the inverse of `3` modulo
`β` from the bottom limb up, like GMP's `mpn_divexact_by3`. Like `karatsuba`, `toom3` takes the
multiplier for the five products as a parameter. `toom3Sqr` squares the same way with five
squares.
-/

open ScalarArray

namespace Bignum

/-! ## Building blocks -/

/-- `x / 2`, which is exact when `x` is even: `x` shifted right by one bit in place. -/
def divExact2 (x : UInt32Array) : UInt32Array := shrLimbs x (1 : Nat).toUInt64

private theorem toNat_divExact2 (x : UInt32Array) (X : Nat) (hx : toNat x = 2 * X) :
    toNat (divExact2 x) = X := by
  rw [divExact2, toNat_shrLimbs _ _ (by decide), hx, Nat.pow_one, Nat.mul_div_cancel_left _
    (by decide)]

/--
One limb of an exact division by `3`, like GMP's `mpn_divexact_by3`: the quotient limb `q` is
`(v - c) 3⁻¹` modulo `β`, with `3⁻¹ = 0xAAAAAAAB`, so that `3 q + c = v + β c'`, where the carry
out `c'` is the high limb of `3 q` plus the borrow of `v - c`.
-/
@[inline] def div3Step (v c : UInt32) : UInt32 × UInt32 :=
  let t := v.toUInt64 - c.toUInt64
  let q := t.toUInt32 * 0xAAAAAAAB
  (q, ((q.toUInt64 * 3) >>> 32).toUInt32 + (t >>> 63).toUInt32)

/-- `0xAAAAAAAB` is the inverse of `3` modulo `β`: `3 · 0xAAAAAAAB = 1 + 2 β`. -/
private theorem mul_inv3 (s : Nat) (hs : s < 4294967296) :
    3 * (s * 2863311531 % 4294967296) % 4294967296 = s := by
  rw [Nat.mul_mod, Nat.mod_mod, ← Nat.mul_mod,
    show 3 * (s * 2863311531) = s + 4294967296 * (2 * s) by omega, Nat.add_mul_mod_self_left,
    Nat.mod_eq_of_lt hs]

private theorem div3Step_spec (v c : UInt32) (hc : c.toNat ≤ 3) :
    3 * (div3Step v c).1.toNat + c.toNat = v.toNat + 2 ^ 32 * (div3Step v c).2.toNat ∧
      (div3Step v c).2.toNat ≤ 3 := by
  have := v.toNat_lt
  simp only [div3Step, UInt32.toNat_mul, UInt32.toNat_add, UInt64.toNat_toUInt32,
    UInt64.toNat_sub, UInt64.toNat_mul, UInt64.toNat_shiftRight, UInt32.toNat_toUInt64,
    Nat.shiftRight_eq_div_pow, UInt64.reduceToNat, UInt32.reduceToNat, Nat.reducePow,
    Nat.reduceMod]
  -- `t = v - c` as a 64-bit word: its low limb `s` and its borrow `b`.
  generalize ht : (18446744073709551616 - c.toNat + v.toNat) % 18446744073709551616 = t
  have hsb : t % 4294967296 + c.toNat = v.toNat + 4294967296 * (t / 9223372036854775808) ∧
      t / 9223372036854775808 ≤ 1 := by
    omega
  have hq := mul_inv3 (t % 4294967296) (Nat.mod_lt _ (by decide))
  have hqlt := Nat.mod_lt (t % 4294967296 * 2863311531) (show 0 < 4294967296 by decide)
  generalize t % 4294967296 * 2863311531 % 4294967296 = q at *
  generalize t % 4294967296 = s at *
  generalize t / 9223372036854775808 = b at *
  -- `3 q < 2⁶⁴` and its high limb is at most `2`, so the reductions are trivial.
  have hhi : q * 3 / 4294967296 ≤ 2 := by omega
  rw [Nat.mod_eq_of_lt (show q * 3 < 18446744073709551616 by omega),
    Nat.mod_eq_of_lt (show q * 3 / 4294967296 < 4294967296 by omega),
    Nat.mod_eq_of_lt (show b < 4294967296 by omega),
    Nat.mod_eq_of_lt (show q * 3 / 4294967296 + b < 4294967296 by omega)]
  omega

/--
The loop of `foldlInPlace` with `div3Step`: the first `k` limbs hold `W`, the rest still hold `O`
from `k` on, and `3 W = (the first k limbs of O) + βᵏ c`.
-/
private theorem div3_loop (O : List UInt32) (n : Nat) (hn : n = O.length) (r : UInt32Array.Slice)
    (hs : r.size = n) (k : Nat) (c : UInt32) (W : List UInt32) (h0 : r.start = 0)
    (hl : r.array.toList = W ++ O.drop k) (hW : W.length = k) (hkn : k ≤ n)
    (hv : 3 * ofLimbs W = ofLimbs (O.take k) + 2 ^ (32 * k) * c.toNat) (hc : c.toNat ≤ 3) :
    ∃ W', (UInt32Array.Slice.foldlInPlace.loop n (fun _ _ v c => div3Step v c) r hs k
        c).1.array.toList = W' ∧ W'.length = n ∧
      3 * ofLimbs W' = ofLimbs O + 2 ^ (32 * n) * (UInt32Array.Slice.foldlInPlace.loop n
        (fun _ _ v c => div3Step v c) r hs k c).2.toNat := by
  induction hd : n - k generalizing k r c W with
  | zero =>
    have hk : k = n := by omega
    subst hk
    rw [UInt32Array.Slice.foldlInPlace.loop, dite_eq_right (by omega)]
    refine ⟨W, ?_, hW, ?_⟩
    · rw [hl, List.drop_of_length_le (by omega), List.append_nil]
    · rw [hv, List.take_of_length_le (by omega)]
  | succ d ih =>
    have hk : k < n := by omega
    have hkO : k < O.length := by omega
    rw [UInt32Array.Slice.foldlInPlace.loop, dite_eq_left hk]
    have hsa : k < r.array.size := by
      have := r.stop_le_array_size; have := r.size_eq; have := r.start_le_stop; omega
    have hdrop := List.drop_eq_getElem_cons hkO
    have hl' := hl
    rw [hdrop] at hl'
    have hrk : r[k]'(by omega) = O[k] := by
      have h := List.getElem_of_eq hl' (i := k) (by simpa using hsa)
      rw [List.getElem_append_right (by omega)] at h
      simp only [hW, Nat.sub_self, List.getElem_cons_zero, UInt32Array.getElem_toList] at h
      rw [UInt32Array.Slice.getElem_eq]
      simpa [h0] using h
    obtain ⟨h₁, h₂⟩ := div3Step_spec (r[k]'(by omega)) c hc
    refine ih _ _ (k + 1) _ (W ++ [(div3Step (r[k]'(by omega)) c).1]) ?_ ?_ ?_ (by omega)
      ?_ h₂ (by omega)
    · rw [UInt32Array.Slice.start_set, h0]
    · rw [UInt32Array.Slice.array_set, UInt32Array.toList_set, hl', h0,
        List.set_append_right _ _ (by simp; omega)]
      simp [hW]
      rw [hdrop]
      rfl
    · simp [hW]
    · rw [ofLimbs_concat, hW, List.take_succ_eq_append_getElem hkO, ofLimbs_append, ofLimbs_cons,
        ofLimbs_nil, Nat.mul_zero, Nat.add_zero, List.length_take,
        Nat.min_eq_left (Nat.le_of_lt hkO), ← hrk, Nat.mul_succ, Nat.pow_add]
      generalize (div3Step (r[k]'(by omega)) c).1.toNat = q at *
      generalize (div3Step (r[k]'(by omega)) c).2.toNat = c' at *
      generalize (r[k]'(by omega)).toNat = v at *
      generalize ofLimbs W = A at *
      generalize ofLimbs (O.take k) = T at *
      generalize 2 ^ (32 * k) = P at *
      generalize (2 : Nat) ^ 32 = B at *
      -- `3 (A + P q) = T + P c + P (v + B c' - c) = T + P v + P B c'`.
      have e : 3 * (A + P * q) + P * c.toNat = T + P * v + P * B * c' + P * c.toNat := by
        rw [Nat.mul_add, hv, Nat.mul_left_comm 3 P q, Nat.mul_assoc P B c']
        have := congrArg (P * ·) h₁
        simp only [Nat.mul_add] at this
        omega
      omega

/-- `βⁿ ≡ 1` modulo `3`, since `β = 2³² ≡ 1`. -/
private theorem pow_mod_three (n : Nat) : 2 ^ (32 * n) % 3 = 1 := by
  rw [Nat.pow_mul, Nat.pow_mod]
  simp

/--
`x / 3`, which is exact when `3` divides `x`: one pass from the bottom limb up with `div3Step`, in
place with `foldlInPlaceThen`, where `divRem1` divides from the top limb down with the hardware
divider.
-/
def divExact3 (x : UInt32Array) : UInt32Array :=
  x.toSlice.foldlInPlaceThen (0 : UInt32) (fun _ _ v c => div3Step v c) (fun r _ => r.array)

private theorem toNat_divExact3 (x : UInt32Array) (X : Nat) (hx : toNat x = 3 * X) :
    toNat (divExact3 x) = X := by
  rw [divExact3, UInt32Array.Slice.foldlInPlaceThen_eq, UInt32Array.Slice.foldlInPlace,
    toNat_toSlice]
  obtain ⟨W, hl, hW, hv⟩ := div3_loop x.toList x.toSlice.size (by simp) x.toSlice rfl 0 0 []
    (by simp) (by simp) rfl (Nat.zero_le _) (by simp) (by decide)
  rw [hl]
  generalize (UInt32Array.Slice.foldlInPlace.loop _ (fun _ _ v (c : UInt32) => div3Step v c) _ _
    0 (0 : UInt32)).2 = cc at hv
  generalize cc.toNat = c at hv
  rw [toNat_toSlice] at hx
  rw [hx] at hv
  have hQ := ofLimbs_lt W
  have hX := ofLimbs_lt x.toList
  rw [hW] at hQ
  simp only [UInt32Array.size_toSlice, UInt32Array.length_toList, Nat.min_self,
    Nat.sub_zero] at hQ hv hX
  rw [hx] at hX
  have hm := pow_mod_three x.size
  generalize 2 ^ (32 * x.size) = P at *
  -- `3 (W - X) = P c` with `W - X < P` and `P ≡ 1 (mod 3)`, so `c = 0`.
  have hc : c = 0 := by
    rcases Nat.lt_or_ge c 3 with h | h
    · rcases (show c = 0 ∨ c = 1 ∨ c = 2 by omega) with h | h | h
      · exact h
      · subst h; omega
      · subst h; omega
    · have := Nat.mul_le_mul_left P h
      omega
  subst hc
  omega

/-- `x₀ + x₁ + x₂`. -/
def eval1 (x₀ x₁ x₂ : UInt32Array.Slice) : UInt32Array := addLimbs (addLimbs x₀ x₁) x₂

/-- `x₀ + 2 x₁ + 4 x₂`. -/
def eval2 (x₀ x₁ x₂ : UInt32Array.Slice) : UInt32Array :=
  addLimbs (addLimbs x₀ (mulRow x₁ 2)) (mulRow x₂ 4)

/-- `x₀ + 3 x₁ + 9 x₂`. -/
def eval3 (x₀ x₁ x₂ : UInt32Array.Slice) : UInt32Array :=
  addLimbs (addLimbs x₀ (mulRow x₁ 3)) (mulRow x₂ 9)

private theorem size_eval1 (x₀ x₁ x₂ : UInt32Array.Slice) :
    (eval1 x₀ x₁ x₂).size = max (max x₀.size x₁.size + 1) x₂.size + 1 := by
  simp [eval1]

private theorem size_eval2 (x₀ x₁ x₂ : UInt32Array.Slice) :
    (eval2 x₀ x₁ x₂).size = max (max x₀.size (x₁.size + 1) + 1) (x₂.size + 1) + 1 := by
  simp [eval2]

private theorem size_eval3 (x₀ x₁ x₂ : UInt32Array.Slice) :
    (eval3 x₀ x₁ x₂).size = max (max x₀.size (x₁.size + 1) + 1) (x₂.size + 1) + 1 := by
  simp [eval3]

private theorem toNat_eval1 (x₀ x₁ x₂ : UInt32Array.Slice) :
    toNat (eval1 x₀ x₁ x₂) = toNat x₀ + toNat x₁ + toNat x₂ := by
  rw [eval1, toNat_addLimbs, toNat_addLimbs]

private theorem toNat_eval2 (x₀ x₁ x₂ : UInt32Array.Slice) :
    toNat (eval2 x₀ x₁ x₂) = toNat x₀ + 2 * toNat x₁ + 4 * toNat x₂ := by
  rw [eval2, toNat_addLimbs, toNat_addLimbs, toNat_mulRow, toNat_mulRow]
  simp only [UInt32.reduceToNat]
  omega

private theorem toNat_eval3 (x₀ x₁ x₂ : UInt32Array.Slice) :
    toNat (eval3 x₀ x₁ x₂) = toNat x₀ + 3 * toNat x₁ + 9 * toNat x₂ := by
  rw [eval3, toNat_addLimbs, toNat_addLimbs, toNat_mulRow, toNat_mulRow]
  simp only [UInt32.reduceToNat]
  omega

/-- Splitting a slice at `k` and `2 k` splits its value in three. -/
private theorem toNat_slice_three (s : UInt32Array.Slice) (k : Nat) (hk : 2 * k ≤ s.size) :
    toNat s = toNat (s.slice 0 k) + 2 ^ (32 * k) * toNat (s.slice k (2 * k)) +
      2 ^ (32 * k) * 2 ^ (32 * k) * toNat (s.slice (2 * k) s.size) := by
  have h₁ := toNat_slice_add_toNat_slice s k (by omega)
  have h₂ := toNat_slice_add_toNat_slice (s.slice k s.size) k (by simp; omega)
  have e₁ : toNat ((s.slice k s.size).slice 0 k) = toNat (s.slice k (2 * k)) := by
    simp only [toNat, UInt32Array.Slice.copy_slice, UInt32Array.extract_extract]
    rw [show k + 0 = k by omega, show min (k + k) s.size = 2 * k by omega]
  have e₂ : toNat ((s.slice k s.size).slice k (s.slice k s.size).size) =
      toNat (s.slice (2 * k) s.size) := by
    simp only [toNat, UInt32Array.Slice.copy_slice, UInt32Array.extract_extract,
      UInt32Array.Slice.size_slice]
    rw [show k + k = 2 * k by omega,
      show min (k + (min s.size s.size - k)) s.size = s.size by omega]
  rw [e₁, e₂] at h₂
  rw [← h₁, ← h₂]
  rw [Nat.mul_add, Nat.mul_assoc]
  omega

/-! ## Interpolation -/

/-- `c₁`, `c₂` and `c₃` from `c₀`, `w₁ = c(1)`, `w₂ = c(2)`, `w₃ = c(3)` and `c₄`. -/
def toom3Interp (c₀ w₁ w₂ w₃ c₄ : UInt32Array) : UInt32Array × UInt32Array × UInt32Array :=
  let r₁ := subVal (subVal w₁ c₀) c₄
  let s₂ := divExact2 (subVal (subVal w₂ c₀) (mulRow c₄ 16))
  let s₃ := divExact3 (subVal (subVal w₃ c₀) (mulRow c₄ 81))
  let t₂ := subVal s₂ r₁
  let t₃ := divExact2 (subVal s₃ r₁)
  let c₃ := subVal t₃ t₂
  let c₂ := subVal t₂ (mulRow c₃ 3)
  (subVal (subVal r₁ c₂) c₃, c₂, c₃)

private theorem toom3Interp_spec (c₀ w₁ w₂ w₃ c₄ : UInt32Array) (C₀ C₁ C₂ C₃ C₄ : Nat)
    (h₀ : toNat c₀ = C₀) (h₄ : toNat c₄ = C₄) (h₁ : toNat w₁ = C₀ + C₁ + C₂ + C₃ + C₄)
    (h₂ : toNat w₂ = C₀ + 2 * C₁ + 4 * C₂ + 8 * C₃ + 16 * C₄)
    (h₃ : toNat w₃ = C₀ + 3 * C₁ + 9 * C₂ + 27 * C₃ + 81 * C₄) :
    toNat (toom3Interp c₀ w₁ w₂ w₃ c₄).1 = C₁ ∧ toNat (toom3Interp c₀ w₁ w₂ w₃ c₄).2.1 = C₂ ∧
      toNat (toom3Interp c₀ w₁ w₂ w₃ c₄).2.2 = C₃ := by
  simp only [toom3Interp]
  have m16 : toNat (mulRow c₄ 16) = 16 * C₄ := by
    rw [toNat_mulRow, h₄]; simp only [UInt32.reduceToNat]; omega
  have m81 : toNat (mulRow c₄ 81) = 81 * C₄ := by
    rw [toNat_mulRow, h₄]; simp only [UInt32.reduceToNat]; omega
  -- `r₁ = c₁ + c₂ + c₃`.
  have hr₁a : toNat (subVal w₁ c₀) = C₁ + C₂ + C₃ + C₄ := by
    rw [toNat_subVal _ _ (by omega)]; omega
  have hr₁ : toNat (subVal (subVal w₁ c₀) c₄) = C₁ + C₂ + C₃ := by
    rw [toNat_subVal _ _ (by omega)]; omega
  -- `s₂ = c₁ + 2 c₂ + 4 c₃` and `s₃ = c₁ + 3 c₂ + 9 c₃`.
  have hs₂a : toNat (subVal (subVal w₂ c₀) (mulRow c₄ 16)) = 2 * (C₁ + 2 * C₂ + 4 * C₃) := by
    rw [toNat_subVal _ _ (by rw [toNat_subVal _ _ (by omega)]; omega),
      toNat_subVal _ _ (by omega)]
    omega
  have hs₂ : toNat (divExact2 (subVal (subVal w₂ c₀) (mulRow c₄ 16))) = C₁ + 2 * C₂ + 4 * C₃ :=
    toNat_divExact2 _ _ hs₂a
  have hs₃a : toNat (subVal (subVal w₃ c₀) (mulRow c₄ 81)) = 3 * (C₁ + 3 * C₂ + 9 * C₃) := by
    rw [toNat_subVal _ _ (by rw [toNat_subVal _ _ (by omega)]; omega),
      toNat_subVal _ _ (by omega)]
    omega
  have hs₃ : toNat (divExact3 (subVal (subVal w₃ c₀) (mulRow c₄ 81))) = C₁ + 3 * C₂ + 9 * C₃ :=
    toNat_divExact3 _ _ hs₃a
  generalize subVal (subVal w₁ c₀) c₄ = r₁ at *
  generalize divExact2 (subVal (subVal w₂ c₀) (mulRow c₄ 16)) = s₂ at *
  generalize divExact3 (subVal (subVal w₃ c₀) (mulRow c₄ 81)) = s₃ at *
  clear hr₁a hs₂a hs₃a m16 m81 h₀ h₁ h₂ h₃ h₄
  -- `t₂ = c₂ + 3 c₃` and `t₃ = c₂ + 4 c₃`.
  have ht₂ : toNat (subVal s₂ r₁) = C₂ + 3 * C₃ := by
    rw [toNat_subVal _ _ (by omega)]; omega
  have ht₃ : toNat (divExact2 (subVal s₃ r₁)) = C₂ + 4 * C₃ :=
    toNat_divExact2 _ _ (by rw [toNat_subVal _ _ (by omega)]; omega)
  generalize subVal s₂ r₁ = t₂ at *
  generalize divExact2 (subVal s₃ r₁) = t₃ at *
  clear hs₂ hs₃
  -- `c₃ = t₃ - t₂`, `c₂ = t₂ - 3 c₃` and `c₁ = r₁ - c₂ - c₃`.
  have hc₃ : toNat (subVal t₃ t₂) = C₃ := by
    rw [toNat_subVal _ _ (by omega)]; omega
  have m3 : toNat (mulRow (subVal t₃ t₂) 3) = 3 * C₃ := by
    rw [toNat_mulRow, hc₃]; simp only [UInt32.reduceToNat]; omega
  have hc₂ : toNat (subVal t₂ (mulRow (subVal t₃ t₂) 3)) = C₂ := by
    rw [toNat_subVal _ _ (by omega)]; omega
  generalize subVal t₃ t₂ = c₃ at *
  generalize subVal t₂ (mulRow c₃ 3) = c₂ at *
  clear ht₂ ht₃ m3
  have hc₁a : toNat (subVal r₁ c₂) = C₁ + C₃ := by
    rw [toNat_subVal r₁ c₂ (by omega)]
    omega
  have hc₁ : toNat (subVal (subVal r₁ c₂) c₃) = C₁ := by
    rw [toNat_subVal (subVal r₁ c₂) c₃ (by omega)]
    omega
  exact ⟨hc₁, hc₂, hc₃⟩

/-! ## Assembly -/

/-- Adding a term `c βᵒᶠᶠ` that fits under a bound `S < βⁿ` on the whole sum. -/
private theorem addAt_term (r c : UInt32Array) (n off P C S : Nat) (hn : r.size = n)
    (hoff : off ≤ n) (hr : toNat r = P) (hc : toNat c = C) (hS : P + 2 ^ (32 * off) * C ≤ S)
    (hlt : S < 2 ^ (32 * n)) :
    (addInto r off (c.toSlice 0 (n - off))).size = n ∧
      toNat (addInto r off (c.toSlice 0 (n - off))) = P + 2 ^ (32 * off) * C := by
  have hpow : 2 ^ (32 * n) = 2 ^ (32 * off) * 2 ^ (32 * (n - off)) := by
    rw [← Nat.pow_add]; congr 1; omega
  have hC : C < 2 ^ (32 * (n - off)) := by
    have : 2 ^ (32 * off) * C < 2 ^ (32 * off) * 2 ^ (32 * (n - off)) := by omega
    exact Nat.lt_of_mul_lt_mul_left this
  have hcut : toNat (c.toSlice 0 (n - off)) = C := by
    rw [toNat_toSlice_of_lt _ _ (by rw [hc]; exact hC), hc]
  have hfit : off + (c.toSlice 0 (n - off)).size ≤ r.size := by
    rw [UInt32Array.size_toSlice]; omega
  refine ⟨by rw [size_addInto _ _ _ hfit, hn], ?_⟩
  rw [toNat_addInto_of_lt _ _ _ hfit (by rw [hr, hcut, hn]; omega), hr, hcut]

/-- `c₀ + c₁ x + c₂ x² + c₃ x³ + c₄ x⁴` as `n` limbs, where `x = βᵏ`. -/
def toom3Assemble (n k : Nat) (c₀ c₁ c₂ c₃ c₄ : UInt32Array) : UInt32Array :=
  let r₀ := addInto (.replicate n 0) 0 (c₀.toSlice 0 (n - 0))
  let r₁ := addInto r₀ k (c₁.toSlice 0 (n - k))
  let r₂ := addInto r₁ (2 * k) (c₂.toSlice 0 (n - 2 * k))
  let r₃ := addInto r₂ (3 * k) (c₃.toSlice 0 (n - 3 * k))
  addInto r₃ (4 * k) (c₄.toSlice 0 (n - 4 * k))

private theorem toom3Assemble_spec (n k : Nat) (c₀ c₁ c₂ c₃ c₄ : UInt32Array)
    (C₀ C₁ C₂ C₃ C₄ : Nat) (hk : 4 * k ≤ n) (h₀ : toNat c₀ = C₀) (h₁ : toNat c₁ = C₁)
    (h₂ : toNat c₂ = C₂) (h₃ : toNat c₃ = C₃) (h₄ : toNat c₄ = C₄)
    (hlt : C₀ + 2 ^ (32 * k) * C₁ + 2 ^ (32 * (2 * k)) * C₂ + 2 ^ (32 * (3 * k)) * C₃ +
      2 ^ (32 * (4 * k)) * C₄ < 2 ^ (32 * n)) :
    (toom3Assemble n k c₀ c₁ c₂ c₃ c₄).size = n ∧
      toNat (toom3Assemble n k c₀ c₁ c₂ c₃ c₄) = C₀ + 2 ^ (32 * k) * C₁ +
        2 ^ (32 * (2 * k)) * C₂ + 2 ^ (32 * (3 * k)) * C₃ + 2 ^ (32 * (4 * k)) * C₄ := by
  generalize hS : C₀ + 2 ^ (32 * k) * C₁ + 2 ^ (32 * (2 * k)) * C₂ + 2 ^ (32 * (3 * k)) * C₃ +
    2 ^ (32 * (4 * k)) * C₄ = S at hlt
  obtain ⟨s₀, v₀⟩ := addAt_term (.replicate n 0) c₀ n 0 0 C₀ S (by simp) (by omega)
    (by rw [toNat_toSlice]; simp) h₀ (by simp; omega) hlt
  obtain ⟨s₁, v₁⟩ := addAt_term _ c₁ n k _ C₁ S s₀ (by omega) v₀ h₁ (by
    simp only [Nat.mul_zero, Nat.pow_zero, Nat.one_mul]; omega) hlt
  obtain ⟨s₂, v₂⟩ := addAt_term _ c₂ n (2 * k) _ C₂ S s₁ (by omega) v₁ h₂ (by
    simp only [Nat.mul_zero, Nat.pow_zero, Nat.one_mul]; omega) hlt
  obtain ⟨s₃, v₃⟩ := addAt_term _ c₃ n (3 * k) _ C₃ S s₂ (by omega) v₂ h₃ (by
    simp only [Nat.mul_zero, Nat.pow_zero, Nat.one_mul]; omega) hlt
  obtain ⟨s₄, v₄⟩ := addAt_term _ c₄ n (4 * k) _ C₄ S s₃ (by omega) v₃ h₄ (by
    simp only [Nat.mul_zero, Nat.pow_zero, Nat.one_mul]; omega) hlt
  refine ⟨s₄, ?_⟩
  rw [toom3Assemble, v₄, ← hS]
  simp only [Nat.mul_zero, Nat.pow_zero, Nat.one_mul, Nat.zero_add]

/-- Interpolation and assembly: `n` limbs of `c(βᵏ)` from the five products. -/
def toom3Finish (n k : Nat) (c₀ w₁ w₂ w₃ c₄ : UInt32Array) : UInt32Array :=
  let i := toom3Interp c₀ w₁ w₂ w₃ c₄
  toom3Assemble n k c₀ i.1 i.2.1 i.2.2 c₄

private theorem toom3_w₁ (A₀ A₁ A₂ B₀ B₁ B₂ : Nat) :
    (A₀ + A₁ + A₂) * (B₀ + B₁ + B₂) = A₀ * B₀ + (A₀ * B₁ + A₁ * B₀) +
      (A₀ * B₂ + A₁ * B₁ + A₂ * B₀) + (A₁ * B₂ + A₂ * B₁) + A₂ * B₂ := by
  grind

private theorem toom3_w₂ (A₀ A₁ A₂ B₀ B₁ B₂ : Nat) :
    (A₀ + 2 * A₁ + 4 * A₂) * (B₀ + 2 * B₁ + 4 * B₂) = A₀ * B₀ + 2 * (A₀ * B₁ + A₁ * B₀) +
      4 * (A₀ * B₂ + A₁ * B₁ + A₂ * B₀) + 8 * (A₁ * B₂ + A₂ * B₁) + 16 * (A₂ * B₂) := by
  grind

private theorem toom3_w₃ (A₀ A₁ A₂ B₀ B₁ B₂ : Nat) :
    (A₀ + 3 * A₁ + 9 * A₂) * (B₀ + 3 * B₁ + 9 * B₂) = A₀ * B₀ + 3 * (A₀ * B₁ + A₁ * B₀) +
      9 * (A₀ * B₂ + A₁ * B₁ + A₂ * B₀) + 27 * (A₁ * B₂ + A₂ * B₁) + 81 * (A₂ * B₂) := by
  grind

private theorem toom3_sum (A₀ A₁ A₂ B₀ B₁ B₂ x : Nat) :
    A₀ * B₀ + x * (A₀ * B₁ + A₁ * B₀) + x * x * (A₀ * B₂ + A₁ * B₁ + A₂ * B₀) +
      x * x * x * (A₁ * B₂ + A₂ * B₁) + x * x * x * x * (A₂ * B₂) =
      (A₀ + x * A₁ + x * x * A₂) * (B₀ + x * B₁ + x * x * B₂) := by
  grind

/--
`toom3Finish` computes the product `(A₀ + x A₁ + x² A₂) (B₀ + x B₁ + x² B₂)` at `x = βᵏ` from
`c₀ = A₀ B₀`, `c₄ = A₂ B₂` and the products of the values at `1`, `2` and `3`, when it fits in
`n` limbs.
-/
private theorem toom3Finish_spec (n k : Nat) (c₀ w₁ w₂ w₃ c₄ : UInt32Array)
    (A₀ A₁ A₂ B₀ B₁ B₂ : Nat) (hk : 4 * k ≤ n) (hv₀ : toNat c₀ = A₀ * B₀)
    (hv₄ : toNat c₄ = A₂ * B₂) (hw₁ : toNat w₁ = (A₀ + A₁ + A₂) * (B₀ + B₁ + B₂))
    (hw₂ : toNat w₂ = (A₀ + 2 * A₁ + 4 * A₂) * (B₀ + 2 * B₁ + 4 * B₂))
    (hw₃ : toNat w₃ = (A₀ + 3 * A₁ + 9 * A₂) * (B₀ + 3 * B₁ + 9 * B₂))
    (hlt : (A₀ + 2 ^ (32 * k) * A₁ + 2 ^ (32 * k) * 2 ^ (32 * k) * A₂) *
      (B₀ + 2 ^ (32 * k) * B₁ + 2 ^ (32 * k) * 2 ^ (32 * k) * B₂) < 2 ^ (32 * n)) :
    (toom3Finish n k c₀ w₁ w₂ w₃ c₄).size = n ∧
      toNat (toom3Finish n k c₀ w₁ w₂ w₃ c₄) =
        (A₀ + 2 ^ (32 * k) * A₁ + 2 ^ (32 * k) * 2 ^ (32 * k) * A₂) *
          (B₀ + 2 ^ (32 * k) * B₁ + 2 ^ (32 * k) * 2 ^ (32 * k) * B₂) := by
  -- Interpolation recovers the middle coefficients.
  have hi := toom3Interp_spec _ _ _ _ _ (A₀ * B₀) (A₀ * B₁ + A₁ * B₀)
    (A₀ * B₂ + A₁ * B₁ + A₂ * B₀) (A₁ * B₂ + A₂ * B₁) (A₂ * B₂) hv₀ hv₄
    (by rw [hw₁, toom3_w₁]) (by rw [hw₂, toom3_w₂]) (by rw [hw₃, toom3_w₃])
  -- The coefficients at `x = βᵏ` give the product.
  have hx₂ : 2 ^ (32 * (2 * k)) = 2 ^ (32 * k) * 2 ^ (32 * k) := by
    rw [← Nat.pow_add]; congr 1; omega
  have hx₃ : 2 ^ (32 * (3 * k)) = 2 ^ (32 * k) * 2 ^ (32 * k) * 2 ^ (32 * k) := by
    rw [← Nat.pow_add, ← Nat.pow_add]; congr 1; omega
  have hx₄ : 2 ^ (32 * (4 * k)) = 2 ^ (32 * k) * 2 ^ (32 * k) * 2 ^ (32 * k) * 2 ^ (32 * k) := by
    rw [← Nat.pow_add, ← Nat.pow_add, ← Nat.pow_add]; congr 1; omega
  have hS : A₀ * B₀ + 2 ^ (32 * k) * (A₀ * B₁ + A₁ * B₀) +
      2 ^ (32 * (2 * k)) * (A₀ * B₂ + A₁ * B₁ + A₂ * B₀) +
      2 ^ (32 * (3 * k)) * (A₁ * B₂ + A₂ * B₁) + 2 ^ (32 * (4 * k)) * (A₂ * B₂) =
      (A₀ + 2 ^ (32 * k) * A₁ + 2 ^ (32 * k) * 2 ^ (32 * k) * A₂) *
        (B₀ + 2 ^ (32 * k) * B₁ + 2 ^ (32 * k) * 2 ^ (32 * k) * B₂) := by
    rw [hx₂, hx₃, hx₄, toom3_sum]
  have key := toom3Assemble_spec n k _ _ _ _ _ _ _ _ _ _ hk hv₀ hi.1 hi.2.1 hi.2.2 hv₄
    (by rw [hS]; exact hlt)
  rw [hS] at key
  exact key

/-! ## Toom-3 -/

/--
The product `a * b` by one step of Toom-3, splitting both at `k` limbs, for `4 ≤ k`, `2 k ≤ b.size ≤
3 k` and `b.size ≤ a.size ≤ 4 k`. It computes the five products with `mulRec`, which only receives
inputs smaller than `a` and `b` together.
-/
public def toom3At (a b : UInt32Array.Slice) (k : Nat) (hk : 4 ≤ k) (hkb : 2 * k ≤ b.size)
    (hbk : b.size ≤ 3 * k) (hab : b.size ≤ a.size) (hak : a.size ≤ 4 * k)
    (mulRec : (x y : UInt32Array.Slice) → x.size + y.size < a.size + b.size → UInt32Array) :
    UInt32Array :=
  let a₀ := a.slice 0 k
  let a₁ := a.slice k (2 * k)
  let a₂ := a.slice (2 * k) a.size
  let b₀ := b.slice 0 k
  let b₁ := b.slice k (2 * k)
  let b₂ := b.slice (2 * k) b.size
  let c₀ := mulRec a₀ b₀ (by simp only [a₀, b₀, UInt32Array.Slice.size_slice]; omega)
  let c₄ := mulRec a₂ b₂ (by simp only [a₂, b₂, UInt32Array.Slice.size_slice]; omega)
  let w₁ := mulRec (eval1 a₀ a₁ a₂) (eval1 b₀ b₁ b₂) (by
    simp only [UInt32Array.size_toSlice, size_eval1, a₀, a₁, a₂, b₀, b₁, b₂,
      UInt32Array.Slice.size_slice]
    omega)
  let w₂ := mulRec (eval2 a₀ a₁ a₂) (eval2 b₀ b₁ b₂) (by
    simp only [UInt32Array.size_toSlice, size_eval2, a₀, a₁, a₂, b₀, b₁, b₂,
      UInt32Array.Slice.size_slice]
    omega)
  let w₃ := mulRec (eval3 a₀ a₁ a₂) (eval3 b₀ b₁ b₂) (by
    simp only [UInt32Array.size_toSlice, size_eval3, a₀, a₁, a₂, b₀, b₁, b₂,
      UInt32Array.Slice.size_slice]
    omega)
  toom3Finish (a.size + b.size) k c₀ w₁ w₂ w₃ c₄

public theorem toom3At_spec (a b : UInt32Array.Slice) (k : Nat) (hk : 4 ≤ k)
    (hkb : 2 * k ≤ b.size) (hbk : b.size ≤ 3 * k) (hab : b.size ≤ a.size) (hak : a.size ≤ 4 * k)
    (mulRec : (x y : UInt32Array.Slice) → x.size + y.size < a.size + b.size → UInt32Array)
    (hrec : ∀ x y h, (mulRec x y h).size = x.size + y.size ∧
      toNat (mulRec x y h) = toNat x * toNat y) :
    (toom3At a b k hk hkb hbk hab hak mulRec).size = a.size + b.size ∧
      toNat (toom3At a b k hk hkb hbk hab hak mulRec) = toNat a * toNat b := by
  have hk₁ : 2 * k ≤ b.size := hkb
  have ha := toNat_slice_three a k (by omega)
  have hb' := toNat_slice_three b k hk₁
  have hA := toNat_lt a
  have hB := toNat_lt b
  -- The five products.
  obtain ⟨-, hv₀⟩ := hrec (a.slice 0 k) (b.slice 0 k)
    (by simp only [UInt32Array.Slice.size_slice]; omega)
  obtain ⟨-, hv₄⟩ := hrec (a.slice (2 * k) a.size)
    (b.slice (2 * k) b.size) (by simp only [UInt32Array.Slice.size_slice]; omega)
  obtain ⟨-, hw₁⟩ := hrec
    (eval1 (a.slice 0 k) (a.slice k (2 * k))
      (a.slice (2 * k) a.size))
    (eval1 (b.slice 0 k) (b.slice k (2 * k))
      (b.slice (2 * k) b.size))
    (by simp only [UInt32Array.size_toSlice, size_eval1, UInt32Array.Slice.size_slice]; omega)
  obtain ⟨-, hw₂⟩ := hrec
    (eval2 (a.slice 0 k) (a.slice k (2 * k))
      (a.slice (2 * k) a.size))
    (eval2 (b.slice 0 k) (b.slice k (2 * k))
      (b.slice (2 * k) b.size))
    (by simp only [UInt32Array.size_toSlice, size_eval2, UInt32Array.Slice.size_slice]; omega)
  obtain ⟨-, hw₃⟩ := hrec
    (eval3 (a.slice 0 k) (a.slice k (2 * k))
      (a.slice (2 * k) a.size))
    (eval3 (b.slice 0 k) (b.slice k (2 * k))
      (b.slice (2 * k) b.size))
    (by simp only [UInt32Array.size_toSlice, size_eval3, UInt32Array.Slice.size_slice]; omega)
  rw [toNat_eval1, toNat_eval1] at hw₁
  rw [toNat_eval2, toNat_eval2] at hw₂
  rw [toNat_eval3, toNat_eval3] at hw₃
  generalize toNat (a.slice 0 k) = A₀ at *
  generalize toNat (a.slice k (2 * k)) = A₁ at *
  generalize toNat (a.slice (2 * k) a.size) = A₂ at *
  generalize toNat (b.slice 0 k) = B₀ at *
  generalize toNat (b.slice k (2 * k)) = B₁ at *
  generalize toNat (b.slice (2 * k) b.size) = B₂ at *
  have hlt : toNat a * toNat b < 2 ^ (32 * (a.size + b.size)) := by
    rw [Nat.mul_add, Nat.pow_add]
    exact Nat.mul_lt_mul'' hA hB
  rw [ha, hb'] at hlt ⊢
  exact toom3Finish_spec (a.size + b.size) k _ _ _ _ _ A₀ A₁ A₂ B₀ B₁ B₂ (by omega)
    hv₀ hv₄ hw₁ hw₂ hw₃ hlt

/--
The product `a * b` by one step of Toom-3, for `12 ≤ b.size ≤ a.size < 4 b.size / 3`: it splits
both at a third of `a` when two such parts fit in `b`, so that the five products are balanced, and
at a third of `b` otherwise. Splitting at a third of `b` alone left a long top part of `a` in all
five products when `a` was longer.
-/
public def toom3 (a b : UInt32Array.Slice) (hb : 12 ≤ b.size) (hab : b.size ≤ a.size)
    (h43 : 3 * a.size < 4 * b.size)
    (mulRec : (x y : UInt32Array.Slice) → x.size + y.size < a.size + b.size → UInt32Array) :
    UInt32Array :=
  if h : 2 * ((a.size + 2) / 3) ≤ b.size then
    toom3At a b ((a.size + 2) / 3) (by lia) h (by lia) hab (by lia) mulRec
  else
    toom3At a b ((b.size + 2) / 3) (by lia) (by lia) (by lia) hab (by lia) mulRec

public theorem toom3_spec (a b : UInt32Array.Slice) (hb : 12 ≤ b.size) (hab : b.size ≤ a.size)
    (h43 : 3 * a.size < 4 * b.size)
    (mulRec : (x y : UInt32Array.Slice) → x.size + y.size < a.size + b.size → UInt32Array)
    (hrec : ∀ x y h, (mulRec x y h).size = x.size + y.size ∧
      toNat (mulRec x y h) = toNat x * toNat y) :
    (toom3 a b hb hab h43 mulRec).size = a.size + b.size ∧
      toNat (toom3 a b hb hab h43 mulRec) = toNat a * toNat b := by
  by_cases h : 2 * ((a.size + 2) / 3) ≤ b.size
  · have e : toom3 a b hb hab h43 mulRec =
        toom3At a b ((a.size + 2) / 3) (by lia) h (by lia) hab (by lia) mulRec := by
      unfold toom3
      rw [dite_eq_left h]
    rw [e]
    exact toom3At_spec _ _ _ _ _ _ _ _ _ hrec
  · have e : toom3 a b hb hab h43 mulRec =
        toom3At a b ((b.size + 2) / 3) (by lia) (by lia) (by lia) hab (by lia) mulRec := by
      unfold toom3
      rw [dite_eq_right h]
    rw [e]
    exact toom3At_spec _ _ _ _ _ _ _ _ _ hrec

/-! ## Toom-3 by 2

For `a` about one and a half times as long as `b`, `toom3` would split both at a third of `b`, which
leaves a long top part of `a` in all five products. `toom32` splits `a` in three and `b` in two at
`k = ⌈a.size / 3⌉`, like GMP's `mpn_toom32_mul`: `c(t) = (a₀ + a₁ t + a₂ t²) (b₀ + b₁ t)` has
four coefficients, from `c₀ = a₀ b₀`, `c₃ = a₂ b₁` and the values `w₁ = c(1)` and `w₂ = c(2)`:

* `r₁ = w₁ - c₀ - c₃ = c₁ + c₂`,
* `s₂ = (w₂ - c₀ - 8 c₃) / 2 = c₁ + 2 c₂`,
* `c₂ = s₂ - r₁`, `c₁ = r₁ - c₂`.
-/

/-- `x₀ + x₁`. -/
def eval1₂ (x₀ x₁ : UInt32Array.Slice) : UInt32Array := addLimbs x₀ x₁

/-- `x₀ + 2 x₁`. -/
def eval2₂ (x₀ x₁ : UInt32Array.Slice) : UInt32Array := addLimbs x₀ (mulRow x₁ 2)

private theorem size_eval1₂ (x₀ x₁ : UInt32Array.Slice) :
    (eval1₂ x₀ x₁).size = max x₀.size x₁.size + 1 := by
  simp [eval1₂]

private theorem size_eval2₂ (x₀ x₁ : UInt32Array.Slice) :
    (eval2₂ x₀ x₁).size = max x₀.size (x₁.size + 1) + 1 := by
  simp [eval2₂]

private theorem toNat_eval1₂ (x₀ x₁ : UInt32Array.Slice) :
    toNat (eval1₂ x₀ x₁) = toNat x₀ + toNat x₁ := by
  rw [eval1₂, toNat_addLimbs]

private theorem toNat_eval2₂ (x₀ x₁ : UInt32Array.Slice) :
    toNat (eval2₂ x₀ x₁) = toNat x₀ + 2 * toNat x₁ := by
  rw [eval2₂, toNat_addLimbs, toNat_mulRow]
  simp only [UInt32.reduceToNat]
  omega

/-- `c₁` and `c₂` from `c₀`, `w₁ = c(1)`, `w₂ = c(2)` and `c₃`. -/
def toom32Interp (c₀ w₁ w₂ c₃ : UInt32Array) : UInt32Array × UInt32Array :=
  let r₁ := subVal (subVal w₁ c₀) c₃
  let s₂ := divExact2 (subVal (subVal w₂ c₀) (mulRow c₃ 8))
  let c₂ := subVal s₂ r₁
  (subVal r₁ c₂, c₂)

private theorem toom32Interp_spec (c₀ w₁ w₂ c₃ : UInt32Array) (C₀ C₁ C₂ C₃ : Nat)
    (h₀ : toNat c₀ = C₀) (h₃ : toNat c₃ = C₃) (h₁ : toNat w₁ = C₀ + C₁ + C₂ + C₃)
    (h₂ : toNat w₂ = C₀ + 2 * C₁ + 4 * C₂ + 8 * C₃) :
    toNat (toom32Interp c₀ w₁ w₂ c₃).1 = C₁ ∧ toNat (toom32Interp c₀ w₁ w₂ c₃).2 = C₂ := by
  simp only [toom32Interp]
  have m8 : toNat (mulRow c₃ 8) = 8 * C₃ := by
    rw [toNat_mulRow, h₃]; simp only [UInt32.reduceToNat]; omega
  have hr₁ : toNat (subVal (subVal w₁ c₀) c₃) = C₁ + C₂ := by
    rw [toNat_subVal _ _ (by rw [toNat_subVal _ _ (by omega)]; omega),
      toNat_subVal _ _ (by omega)]
    omega
  have hs₂a : toNat (subVal (subVal w₂ c₀) (mulRow c₃ 8)) = 2 * (C₁ + 2 * C₂) := by
    rw [toNat_subVal _ _ (by rw [toNat_subVal _ _ (by omega)]; omega),
      toNat_subVal _ _ (by omega)]
    omega
  have hs₂ : toNat (divExact2 (subVal (subVal w₂ c₀) (mulRow c₃ 8))) = C₁ + 2 * C₂ :=
    toNat_divExact2 _ _ hs₂a
  generalize subVal (subVal w₁ c₀) c₃ = r₁ at *
  generalize divExact2 (subVal (subVal w₂ c₀) (mulRow c₃ 8)) = s₂ at *
  have hc₂ : toNat (subVal s₂ r₁) = C₂ := by
    rw [toNat_subVal _ _ (by omega)]; omega
  generalize subVal s₂ r₁ = c₂ at *
  refine ⟨?_, hc₂⟩
  rw [toNat_subVal _ _ (by omega)]
  omega

/-- `c₀ + c₁ x + c₂ x² + c₃ x³` as `n` limbs, where `x = βᵏ`. -/
def toom32Assemble (n k : Nat) (c₀ c₁ c₂ c₃ : UInt32Array) : UInt32Array :=
  let r₀ := addInto (.replicate n 0) 0 (c₀.toSlice 0 (n - 0))
  let r₁ := addInto r₀ k (c₁.toSlice 0 (n - k))
  let r₂ := addInto r₁ (2 * k) (c₂.toSlice 0 (n - 2 * k))
  addInto r₂ (3 * k) (c₃.toSlice 0 (n - 3 * k))

private theorem toom32Assemble_spec (n k : Nat) (c₀ c₁ c₂ c₃ : UInt32Array) (C₀ C₁ C₂ C₃ : Nat)
    (hk : 3 * k ≤ n) (h₀ : toNat c₀ = C₀) (h₁ : toNat c₁ = C₁) (h₂ : toNat c₂ = C₂)
    (h₃ : toNat c₃ = C₃)
    (hlt : C₀ + 2 ^ (32 * k) * C₁ + 2 ^ (32 * (2 * k)) * C₂ + 2 ^ (32 * (3 * k)) * C₃ <
      2 ^ (32 * n)) :
    (toom32Assemble n k c₀ c₁ c₂ c₃).size = n ∧
      toNat (toom32Assemble n k c₀ c₁ c₂ c₃) = C₀ + 2 ^ (32 * k) * C₁ +
        2 ^ (32 * (2 * k)) * C₂ + 2 ^ (32 * (3 * k)) * C₃ := by
  generalize hS : C₀ + 2 ^ (32 * k) * C₁ + 2 ^ (32 * (2 * k)) * C₂ +
    2 ^ (32 * (3 * k)) * C₃ = S at hlt
  obtain ⟨s₀, v₀⟩ := addAt_term (.replicate n 0) c₀ n 0 0 C₀ S (by simp) (by omega)
    (by rw [toNat_toSlice]; simp) h₀ (by simp; omega) hlt
  obtain ⟨s₁, v₁⟩ := addAt_term _ c₁ n k _ C₁ S s₀ (by omega) v₀ h₁ (by
    simp only [Nat.mul_zero, Nat.pow_zero, Nat.one_mul]; omega) hlt
  obtain ⟨s₂, v₂⟩ := addAt_term _ c₂ n (2 * k) _ C₂ S s₁ (by omega) v₁ h₂ (by
    simp only [Nat.mul_zero, Nat.pow_zero, Nat.one_mul]; omega) hlt
  obtain ⟨s₃, v₃⟩ := addAt_term _ c₃ n (3 * k) _ C₃ S s₂ (by omega) v₂ h₃ (by
    simp only [Nat.mul_zero, Nat.pow_zero, Nat.one_mul]; omega) hlt
  refine ⟨s₃, ?_⟩
  rw [toom32Assemble, v₃, ← hS]
  simp only [Nat.mul_zero, Nat.pow_zero, Nat.one_mul, Nat.zero_add]

private theorem toom32_sum (A₀ A₁ A₂ B₀ B₁ x : Nat) :
    A₀ * B₀ + x * (A₀ * B₁ + A₁ * B₀) + x * x * (A₁ * B₁ + A₂ * B₀) + x * x * x * (A₂ * B₁) =
      (A₀ + x * A₁ + x * x * A₂) * (B₀ + x * B₁) := by
  grind

/--
The product `a * b` by one step of Toom-3 by 2, splitting `a` in three and `b` in two at
`k = ⌈a.size / 3⌉`, for `k ≤ b.size ≤ a.size` and `12 ≤ b.size`. It computes the four products
with `mulRec`, which only receives inputs smaller than `a` and `b` together.
-/
public def toom32 (a b : UInt32Array.Slice) (hb : 12 ≤ b.size) (hab : b.size ≤ a.size)
    (hk : (a.size + 2) / 3 ≤ b.size)
    (mulRec : (x y : UInt32Array.Slice) → x.size + y.size < a.size + b.size → UInt32Array) :
    UInt32Array :=
  let k := (a.size + 2) / 3
  let a₀ := a.slice 0 k
  let a₁ := a.slice k (2 * k)
  let a₂ := a.slice (2 * k) a.size
  let b₀ := b.slice 0 k
  let b₁ := b.slice k b.size
  let c₀ := mulRec a₀ b₀ (by simp only [a₀, b₀, UInt32Array.Slice.size_slice]; omega)
  let c₃ := mulRec a₂ b₁ (by simp only [a₂, b₁, UInt32Array.Slice.size_slice]; omega)
  let w₁ := mulRec (eval1 a₀ a₁ a₂) (eval1₂ b₀ b₁) (by
    simp only [UInt32Array.size_toSlice, size_eval1, size_eval1₂, a₀, a₁, a₂, b₀, b₁,
      UInt32Array.Slice.size_slice]
    omega)
  let w₂ := mulRec (eval2 a₀ a₁ a₂) (eval2₂ b₀ b₁) (by
    simp only [UInt32Array.size_toSlice, size_eval2, size_eval2₂, a₀, a₁, a₂, b₀, b₁,
      UInt32Array.Slice.size_slice]
    omega)
  let i := toom32Interp c₀ w₁ w₂ c₃
  toom32Assemble (a.size + b.size) k c₀ i.1 i.2 c₃

public theorem toom32_spec (a b : UInt32Array.Slice) (hb : 12 ≤ b.size) (hab : b.size ≤ a.size)
    (hk : (a.size + 2) / 3 ≤ b.size)
    (mulRec : (x y : UInt32Array.Slice) → x.size + y.size < a.size + b.size → UInt32Array)
    (hrec : ∀ x y h, (mulRec x y h).size = x.size + y.size ∧
      toNat (mulRec x y h) = toNat x * toNat y) :
    (toom32 a b hb hab hk mulRec).size = a.size + b.size ∧
      toNat (toom32 a b hb hab hk mulRec) = toNat a * toNat b := by
  have ha := toNat_slice_three a ((a.size + 2) / 3) (by omega)
  have hb' := toNat_slice_add_toNat_slice b ((a.size + 2) / 3) hk
  have hA := toNat_lt a
  have hB := toNat_lt b
  -- The four products.
  obtain ⟨-, hv₀⟩ := hrec (a.slice 0 ((a.size + 2) / 3)) (b.slice 0 ((a.size + 2) / 3))
    (by simp only [UInt32Array.Slice.size_slice]; omega)
  obtain ⟨-, hv₃⟩ := hrec (a.slice (2 * ((a.size + 2) / 3)) a.size)
    (b.slice ((a.size + 2) / 3) b.size) (by simp only [UInt32Array.Slice.size_slice]; omega)
  obtain ⟨-, hw₁⟩ := hrec
    (eval1 (a.slice 0 ((a.size + 2) / 3)) (a.slice ((a.size + 2) / 3) (2 * ((a.size + 2) / 3)))
      (a.slice (2 * ((a.size + 2) / 3)) a.size))
    (eval1₂ (b.slice 0 ((a.size + 2) / 3)) (b.slice ((a.size + 2) / 3) b.size))
    (by simp only [UInt32Array.size_toSlice, size_eval1, size_eval1₂,
      UInt32Array.Slice.size_slice]; omega)
  obtain ⟨-, hw₂⟩ := hrec
    (eval2 (a.slice 0 ((a.size + 2) / 3)) (a.slice ((a.size + 2) / 3) (2 * ((a.size + 2) / 3)))
      (a.slice (2 * ((a.size + 2) / 3)) a.size))
    (eval2₂ (b.slice 0 ((a.size + 2) / 3)) (b.slice ((a.size + 2) / 3) b.size))
    (by simp only [UInt32Array.size_toSlice, size_eval2, size_eval2₂,
      UInt32Array.Slice.size_slice]; omega)
  rw [toNat_eval1, toNat_eval1₂] at hw₁
  rw [toNat_eval2, toNat_eval2₂] at hw₂
  generalize toNat (a.slice 0 ((a.size + 2) / 3)) = A₀ at *
  generalize toNat (a.slice ((a.size + 2) / 3) (2 * ((a.size + 2) / 3))) = A₁ at *
  generalize toNat (a.slice (2 * ((a.size + 2) / 3)) a.size) = A₂ at *
  generalize toNat (b.slice 0 ((a.size + 2) / 3)) = B₀ at *
  generalize toNat (b.slice ((a.size + 2) / 3) b.size) = B₁ at *
  have hlt : toNat a * toNat b < 2 ^ (32 * (a.size + b.size)) := by
    rw [Nat.mul_add, Nat.pow_add]
    exact Nat.mul_lt_mul'' hA hB
  -- Interpolation recovers the middle coefficients.
  have hi := toom32Interp_spec _ _ _ _ (A₀ * B₀) (A₀ * B₁ + A₁ * B₀) (A₁ * B₁ + A₂ * B₀)
    (A₂ * B₁) hv₀ hv₃ (by rw [hw₁]; grind) (by rw [hw₂]; grind)
  have hx₂ : 2 ^ (32 * (2 * ((a.size + 2) / 3))) =
      2 ^ (32 * ((a.size + 2) / 3)) * 2 ^ (32 * ((a.size + 2) / 3)) := by
    rw [← Nat.pow_add]; congr 1; omega
  have hx₃ : 2 ^ (32 * (3 * ((a.size + 2) / 3))) = 2 ^ (32 * ((a.size + 2) / 3)) *
      2 ^ (32 * ((a.size + 2) / 3)) * 2 ^ (32 * ((a.size + 2) / 3)) := by
    rw [← Nat.pow_add, ← Nat.pow_add]; congr 1; omega
  have hS : A₀ * B₀ + 2 ^ (32 * ((a.size + 2) / 3)) * (A₀ * B₁ + A₁ * B₀) +
      2 ^ (32 * (2 * ((a.size + 2) / 3))) * (A₁ * B₁ + A₂ * B₀) +
      2 ^ (32 * (3 * ((a.size + 2) / 3))) * (A₂ * B₁) = toNat a * toNat b := by
    rw [hx₂, hx₃, toom32_sum, ha, hb']
  simp only [toom32]
  have key := toom32Assemble_spec (a.size + b.size) ((a.size + 2) / 3) _ _ _ _ _ _ _ _
    (by omega) hv₀ hi.1 hi.2 hv₃ (by rw [hS]; exact hlt)
  rw [hS] at key
  exact key

/-! ## Toom-3 squaring -/

/--
The square `a * a` by one step of Toom-3, for `12 ≤ a.size`: the same split, evaluations,
interpolation and assembly as `toom3 a a`, but each value is computed once and the five products
are squares, which `sqrRec` computes on inputs shorter than `a`.
-/
public def toom3Sqr (a : UInt32Array.Slice) (ha : 12 ≤ a.size)
    (sqrRec : (x : UInt32Array.Slice) → x.size < a.size → UInt32Array) : UInt32Array :=
  let k := (a.size + 2) / 3
  let a₀ := a.slice 0 k
  let a₁ := a.slice k (2 * k)
  let a₂ := a.slice (2 * k) a.size
  let c₀ := sqrRec a₀ (by simp only [a₀, UInt32Array.Slice.size_slice]; omega)
  let c₄ := sqrRec a₂ (by simp only [a₂, UInt32Array.Slice.size_slice]; omega)
  let w₁ := sqrRec (eval1 a₀ a₁ a₂) (by
    simp only [UInt32Array.size_toSlice, size_eval1, a₀, a₁, a₂, UInt32Array.Slice.size_slice]
    omega)
  let w₂ := sqrRec (eval2 a₀ a₁ a₂) (by
    simp only [UInt32Array.size_toSlice, size_eval2, a₀, a₁, a₂, UInt32Array.Slice.size_slice]
    omega)
  let w₃ := sqrRec (eval3 a₀ a₁ a₂) (by
    simp only [UInt32Array.size_toSlice, size_eval3, a₀, a₁, a₂, UInt32Array.Slice.size_slice]
    omega)
  toom3Finish (a.size + a.size) k c₀ w₁ w₂ w₃ c₄

public theorem toom3Sqr_spec (a : UInt32Array.Slice) (ha : 12 ≤ a.size)
    (sqrRec : (x : UInt32Array.Slice) → x.size < a.size → UInt32Array)
    (hrec : ∀ x h, (sqrRec x h).size = x.size + x.size ∧
      toNat (sqrRec x h) = toNat x * toNat x) :
    (toom3Sqr a ha sqrRec).size = a.size + a.size ∧
      toNat (toom3Sqr a ha sqrRec) = toNat a * toNat a := by
  have hsplit := toNat_slice_three a ((a.size + 2) / 3) (by omega)
  have hA := toNat_lt a
  -- The five squares.
  obtain ⟨-, hv₀⟩ := hrec (a.slice 0 ((a.size + 2) / 3))
    (by simp only [UInt32Array.Slice.size_slice]; omega)
  obtain ⟨-, hv₄⟩ := hrec (a.slice (2 * ((a.size + 2) / 3)) a.size)
    (by simp only [UInt32Array.Slice.size_slice]; omega)
  obtain ⟨-, hw₁⟩ := hrec
    (eval1 (a.slice 0 ((a.size + 2) / 3)) (a.slice ((a.size + 2) / 3) (2 * ((a.size + 2) / 3)))
      (a.slice (2 * ((a.size + 2) / 3)) a.size))
    (by simp only [UInt32Array.size_toSlice, size_eval1, UInt32Array.Slice.size_slice]; omega)
  obtain ⟨-, hw₂⟩ := hrec
    (eval2 (a.slice 0 ((a.size + 2) / 3)) (a.slice ((a.size + 2) / 3) (2 * ((a.size + 2) / 3)))
      (a.slice (2 * ((a.size + 2) / 3)) a.size))
    (by simp only [UInt32Array.size_toSlice, size_eval2, UInt32Array.Slice.size_slice]; omega)
  obtain ⟨-, hw₃⟩ := hrec
    (eval3 (a.slice 0 ((a.size + 2) / 3)) (a.slice ((a.size + 2) / 3) (2 * ((a.size + 2) / 3)))
      (a.slice (2 * ((a.size + 2) / 3)) a.size))
    (by simp only [UInt32Array.size_toSlice, size_eval3, UInt32Array.Slice.size_slice]; omega)
  rw [toNat_eval1] at hw₁
  rw [toNat_eval2] at hw₂
  rw [toNat_eval3] at hw₃
  generalize toNat (a.slice 0 ((a.size + 2) / 3)) = A₀ at *
  generalize toNat (a.slice ((a.size + 2) / 3) (2 * ((a.size + 2) / 3))) = A₁ at *
  generalize toNat (a.slice (2 * ((a.size + 2) / 3)) a.size) = A₂ at *
  have hlt : toNat a * toNat a < 2 ^ (32 * (a.size + a.size)) := by
    rw [Nat.mul_add, Nat.pow_add]
    exact Nat.mul_lt_mul'' hA hA
  rw [hsplit] at hlt ⊢
  exact toom3Finish_spec (a.size + a.size) ((a.size + 2) / 3) _ _ _ _ _ A₀ A₁ A₂ A₀ A₁ A₂
    (by omega) hv₀ hv₄ hw₁ hw₂ hw₃ hlt

end Bignum
