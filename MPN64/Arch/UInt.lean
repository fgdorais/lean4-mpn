/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import MPN.WordH

/-!
# Double-width word operations

The high-word operations of limb arithmetic on `UInt32` and `UInt64`, each computing the high
word of a double-width result:

* `addh c x y` adds the carry out of `x + y` to `c`;
* `subh b x y` adds the borrow out of `x - y` to `b`;
* `mulh x y` is the high word of `x * y`;
* `div2 hi lo d` is the quotient of the double word `hi lo` by `d`.

The low words are the ordinary wrapping `x + y`, `x - y` and `x * y`, so a limb loop computes
the low word and the carry, borrow or high word separately, without allocating a pair.

The `UInt32` operations compute in `UInt64`. The `UInt64` operations are specified with `Nat` and
implemented by inline C with `__uint128_t`, so their generated C only compiles where the C
compiler has that type, for example, GCC 4.6 or later and Clang 3.3 or later.

Each operation comes with a `toNat_*` theorem that states its value in `Nat`.
-/

/-! ## `UInt64` -/

/-- Adds the high word of `x + y`, which is its carry out, to `c`. -/
@[extern c inline "#1 + (uint64_t)(((__uint128_t)(#2) + (__uint128_t)(#3)) >> 64)"]
public def UInt64.addh (c x y : UInt64) : UInt64 :=
  let t := x.toNat + y.toNat
  c + (t >>> 64).toUInt64

public theorem UInt64.toNat_addh (c x y : UInt64) :
    (UInt64.addh c x y).toNat = (c.toNat + (x.toNat + y.toNat) / 2 ^ 64) % 2 ^ 64 := by
  have := x.toNat_lt; have := y.toNat_lt
  simp only [UInt64.addh, UInt64.toNat_add, UInt64.toNat_ofNat', Nat.shiftRight_eq_div_pow]
  grind

/--
Subtracts the high word of `x - y`, computed in double width, from `b`. The high word is all ones
when `x - y` borrows, so this adds the borrow to `b`.
-/
@[extern c inline "#1 - (uint64_t)(((__uint128_t)(#2) - (__uint128_t)(#3)) >> 64)"]
public def UInt64.subh (b x y : UInt64) : UInt64 :=
  let t := (2 ^ 128 + x.toNat - y.toNat) % 2 ^ 128
  b - (t >>> 64).toUInt64

public theorem UInt64.toNat_subh (b x y : UInt64) :
    (UInt64.subh b x y).toNat = (b.toNat + if x.toNat < y.toNat then 1 else 0) % 2 ^ 64 := by
  have := x.toNat_lt; have := y.toNat_lt
  simp only [UInt64.subh, UInt64.toNat_sub, UInt64.toNat_ofNat', Nat.shiftRight_eq_div_pow]
  split
  · have hd : (2 ^ 128 + x.toNat - y.toNat) % 2 ^ 128 = 2 ^ 128 + x.toNat - y.toNat :=
      Nat.mod_eq_of_lt (by lia)
    have hq : (2 ^ 128 + x.toNat - y.toNat) / 2 ^ 64 = 2 ^ 64 - 1 := by lia
    rw [hd, hq]
    lia
  · have hd : (2 ^ 128 + x.toNat - y.toNat) % 2 ^ 128 = x.toNat - y.toNat := by
      rw [show 2 ^ 128 + x.toNat - y.toNat = x.toNat - y.toNat + 2 ^ 128 by lia, Nat.add_mod_right,
        Nat.mod_eq_of_lt (by lia)]
    have hq : (x.toNat - y.toNat) / 2 ^ 64 = 0 := Nat.div_eq_of_lt (by lia)
    rw [hd, hq]
    lia

/--
`subh` written in C as `b + (x < y)`: a compare and an add with carry. On the chain of a
subtraction's borrow (`subC`) the double-width form of `subh` compiles to one more operation, a
negation; inside the longer expressions of the multiply-subtract and the linear combinations of the
gcd, `subh`'s form compiles better.
-/
@[extern c inline "#1 + (uint64_t)((#2) < (#3))"]
public def UInt64.subb (b x y : UInt64) : UInt64 :=
  let t := (2 ^ 128 + x.toNat - y.toNat) % 2 ^ 128
  b - (t >>> 64).toUInt64

public theorem UInt64.toNat_subb (b x y : UInt64) :
    (UInt64.subb b x y).toNat = (b.toNat + if x.toNat < y.toNat then 1 else 0) % 2 ^ 64 :=
  UInt64.toNat_subh b x y

/-- The high word of `x * y`. -/
@[extern c inline "(uint64_t)(((__uint128_t)(#1) * (__uint128_t)(#2)) >> 64)"]
public def UInt64.mulh (x y : UInt64) : UInt64 :=
  let t := x.toNat * y.toNat
  (t >>> 64).toUInt64

public theorem UInt64.toNat_mulh (x y : UInt64) :
    (UInt64.mulh x y).toNat = x.toNat * y.toNat / 2 ^ 64 := by
  have := Nat.mul_lt_mul'' x.toNat_lt y.toNat_lt
  simp only [UInt64.mulh, UInt64.toNat_ofNat', Nat.shiftRight_eq_div_pow]
  exact Nat.mod_eq_of_lt (by simp; lia)

/--
The low word of the quotient of `hi β + lo` by `d`, where `β = 2⁶⁴`, or `0` when `d = 0`. When
`hi < d` the quotient fits in a word, and `lo - q d` is the remainder (`toNat_div2_rem`).
-/
@[extern c inline "(#3 == 0 ? (uint64_t)0 : \
  (uint64_t)((((__uint128_t)(#1) << 64) | (__uint128_t)(#2)) / (__uint128_t)(#3)))"]
public def UInt64.div2 (hi lo d : UInt64) : UInt64 :=
  ((hi.toNat * 2 ^ 64 + lo.toNat) / d.toNat).toUInt64

public theorem UInt64.toNat_div2 (hi lo d : UInt64) (h : hi.toNat < d.toNat) :
    (UInt64.div2 hi lo d).toNat = (hi.toNat * 2 ^ 64 + lo.toNat) / d.toNat := by
  have := lo.toNat_lt
  have hq : (hi.toNat * 2 ^ 64 + lo.toNat) / d.toNat < 2 ^ 64 := by
    rw [Nat.div_lt_iff_lt_mul (by lia)]
    have := Nat.mul_le_mul_right (2 ^ 64) (show hi.toNat + 1 ≤ d.toNat from h)
    rw [Nat.add_mul, Nat.one_mul] at this
    rw [Nat.mul_comm]
    lia
  simp only [UInt64.div2, UInt64.toNat_ofNat']
  exact Nat.mod_eq_of_lt hq

/-- The remainder of `hi β + lo` by `d`, for `hi < d`, from the quotient `q = div2 hi lo d`. -/
public theorem UInt64.toNat_div2_rem (hi lo d : UInt64) (h : hi.toNat < d.toNat) :
    (lo - UInt64.div2 hi lo d * d).toNat = (hi.toNat * 2 ^ 64 + lo.toNat) % d.toNat ∧
      d.toNat * (UInt64.div2 hi lo d).toNat + (lo - UInt64.div2 hi lo d * d).toNat =
        hi.toNat * 2 ^ 64 + lo.toNat := by
  have hq := UInt64.toNat_div2 hi lo d h
  have hdm := Nat.div_add_mod (hi.toNat * 2 ^ 64 + lo.toNat) d.toNat
  have hr := Nat.mod_lt (hi.toNat * 2 ^ 64 + lo.toNat) (show 0 < d.toNat by lia)
  have hd := d.toNat_lt
  -- `lo = r + q d` in words, so `lo - q d = r`.
  have e : lo = UInt64.ofNat ((hi.toNat * 2 ^ 64 + lo.toNat) % d.toNat) +
      UInt64.div2 hi lo d * d := by
    apply UInt64.toNat_inj.1
    rw [UInt64.toNat_add, UInt64.toNat_mul, UInt64.toNat_ofNat', hq, ← Nat.add_mod,
      Nat.mul_comm _ d.toNat]
    generalize (hi.toNat * 2 ^ 64 + lo.toNat) / d.toNat = q at *
    generalize (hi.toNat * 2 ^ 64 + lo.toNat) % d.toNat = r at *
    rw [Nat.add_comm r, hdm, Nat.add_comm, Nat.add_mul_mod_self_right,
      Nat.mod_eq_of_lt lo.toNat_lt]
  have e' : (lo - UInt64.div2 hi lo d * d).toNat = (hi.toNat * 2 ^ 64 + lo.toNat) % d.toNat := by
    generalize (hi.toNat * 2 ^ 64 + lo.toNat) % d.toNat = r at e hr ⊢
    generalize UInt64.div2 hi lo d = Q at e ⊢
    rw [e, UInt64.add_sub_cancel, UInt64.toNat_ofNat', Nat.mod_eq_of_lt (by lia)]
  refine ⟨e', ?_⟩
  rw [e', hq]
  exact hdm

/-! ## Karatsuba's middle term -/

/--
The high word of `v + x + c + 2⁶⁵ - 2 - y - z` in double width, which is between `0` and `3` when
`c ≤ 3`: the carry out of `v + x + (c - 2) - y - z`, plus `2`.
-/
@[extern c inline "(uint64_t)(((__uint128_t)(#1) + (__uint128_t)(#2) + (__uint128_t)(#5) + \
  ((((__uint128_t)1) << 65) - 2) - (__uint128_t)(#3) - (__uint128_t)(#4)) >> 64)"]
public def UInt64.addDiffh (v x y z c : UInt64) : UInt64 :=
  ((v.toNat + x.toNat + c.toNat + (2 ^ 65 - 2) - y.toNat - z.toNat) / 2 ^ 64).toUInt64

private theorem UInt64.sub_word (u v : UInt64) :
    ∃ k, k ≤ 1 ∧ (u - v).toNat + v.toNat = u.toNat + 2 ^ 64 * k := by
  have := u.toNat_lt; have := v.toNat_lt
  rw [UInt64.toNat_sub]
  by_cases h : v.toNat ≤ u.toNat
  · exact ⟨0, by lia, by
      rw [show 2 ^ 64 - v.toNat + u.toNat = (u.toNat - v.toNat) + 2 ^ 64 by lia, Nat.add_mod_right,
        Nat.mod_eq_of_lt (by lia)]; lia⟩
  · exact ⟨1, by lia, by rw [Nat.mod_eq_of_lt (by lia)]; lia⟩

private theorem UInt64.add_word (u v : UInt64) :
    ∃ k, k ≤ 1 ∧ (u + v).toNat + 2 ^ 64 * k = u.toNat + v.toNat := by
  have := u.toNat_lt; have := v.toNat_lt
  rw [UInt64.toNat_add]
  by_cases h : u.toNat + v.toNat < 2 ^ 64
  · exact ⟨0, by lia, by rw [Nat.mod_eq_of_lt h]; try lia⟩
  · exact ⟨1, by lia, by
      rw [show u.toNat + v.toNat = (u.toNat + v.toNat - 2 ^ 64) + 2 ^ 64 by lia, Nat.add_mod_right,
        Nat.mod_eq_of_lt (by lia)]; try lia⟩

/-- The step of the loop: limb `v + x + (c - 2) - y - z` and the next carry plus `2`. -/
public theorem UInt64.addDiff_step (v x y z c : UInt64) (hc : c.toNat ≤ 3) :
    (v + x + c - 2 - y - z).toNat + 2 ^ 64 * (UInt64.addDiffh v x y z c).toNat + y.toNat +
        z.toNat + 2 = v.toNat + x.toNat + c.toNat + 2 ^ 65 ∧
      (UInt64.addDiffh v x y z c).toNat ≤ 3 := by
  have := v.toNat_lt; have := x.toNat_lt; have := y.toNat_lt; have := z.toNat_lt
  obtain ⟨k₁, hk₁, e₁⟩ := UInt64.add_word v x
  obtain ⟨k₂, hk₂, e₂⟩ := UInt64.add_word (v + x) c
  obtain ⟨k₃, hk₃, e₃⟩ := UInt64.sub_word (v + x + c) 2
  obtain ⟨k₄, hk₄, e₄⟩ := UInt64.sub_word (v + x + c - 2) y
  obtain ⟨k₅, hk₅, e₅⟩ := UInt64.sub_word (v + x + c - 2 - y) z
  have h2 : (2 : UInt64).toNat = 2 := rfl
  rw [h2] at e₃
  have hN : (v.toNat + x.toNat + c.toNat + (2 ^ 65 - 2) - y.toNat - z.toNat) / 2 ^ 64 < 4 := by
    lia
  have hh : (UInt64.addDiffh v x y z c).toNat =
      (v.toNat + x.toNat + c.toNat + (2 ^ 65 - 2) - y.toNat - z.toNat) / 2 ^ 64 := by
    rw [UInt64.addDiffh, Nat.toUInt64_eq, UInt64.toNat_ofNat', Nat.mod_eq_of_lt (by lia)]
  rw [hh]
  have := (v + x + c - 2 - y - z).toNat_lt
  generalize (v + x).toNat = s₁ at *
  generalize (v + x + c).toNat = s₂ at *
  generalize (v + x + c - 2).toNat = s₃ at *
  generalize (v + x + c - 2 - y).toNat = s₄ at *
  generalize (v + x + c - 2 - y - z).toNat = s₅ at *
  constructor <;> lia
