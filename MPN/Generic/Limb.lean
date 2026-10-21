/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import MPN.UInt

/-!
# Limbs

`Limb ν` bundles the primitive operations on single limbs of type `ν` at a base `base`: the value
of a limb, a limb from a value below the base, addition with a carry, subtraction with a borrow,
and the double-limb product. `LawfulLimb` states their specifications on values, so that limb
arithmetic can be written and proved once for any limb type, and `Limb.uint32` provides 32-bit
limbs from the word operations of `MPN.UInt`.
-/

namespace MPN

/-- The primitive operations on limbs of type `ν` at base `base`. -/
public structure Limb (ν : Type) where
  /-- The base, `2³²` for 32-bit limbs. -/
  base : Nat
  /-- The value of a limb. -/
  toNat : ν → Nat
  /-- The limb of value `n`, for `n` below the base. -/
  ofNat : (n : Nat) → n < base → ν
  /-- `x + y + c` as its low limb and a carry out. -/
  addc : ν → ν → Bool → ν × Bool
  /-- `x - y - b` as its low limb, wrapping, and a borrow out. -/
  subb : ν → ν → Bool → ν × Bool
  /-- `x * y` as its low limb and its high limb. -/
  muld : ν → ν → ν × ν

/--
The specification of the operations of `limb` on values: limbs are the numbers below the base,
and each operation computes its result modulo the base, with the carry, borrow or high limb that
completes it.
-/
public class LawfulLimb (limb : Limb ν) : Prop where
  /-- The value of a limb is below the base. -/
  toNat_lt_base (x : ν) : limb.toNat x < limb.base
  /-- `ofNat n` has value `n`. -/
  toNat_ofNat (n) (h : n < limb.base) : limb.toNat (limb.ofNat n h) = n
  /-- A limb is determined by its value. -/
  ofNat_toNat (x : ν) : limb.ofNat (limb.toNat x) (toNat_lt_base x) = x
  /-- The low limb of `addc` is `x + y + c` modulo the base. -/
  addc_lo {x y : ν} :
    limb.toNat (limb.addc x y cy).1 = (limb.toNat x + limb.toNat y + cy.toNat) % limb.base
  /-- The carry of `addc` is set when `x + y + c` reaches the base. -/
  addc_cy {x y : ν} :
    (limb.addc x y cy).2 = decide (limb.toNat x + limb.toNat y + cy.toNat ≥ limb.base)
  /--
  The low limb of `subb` is `x - y - b` modulo the base, written `x + base - y - b` since `Nat`
  subtraction truncates at zero.
  -/
  subb_lo {x y : ν} :
    limb.toNat (limb.subb x y bw).1 =
      (limb.toNat x + limb.base - limb.toNat y - bw.toNat) % limb.base
  /-- The borrow of `subb` is set when `y + b` exceeds `x`. -/
  subb_bw {x y : ν} :
    (limb.subb x y bw).2 = decide (limb.toNat y + bw.toNat > limb.toNat x)
  /-- The low and high limbs of `muld` make up `x * y`. -/
  muld {x y : ν} :
    limb.toNat (limb.muld x y).1 + limb.toNat (limb.muld x y).2 * limb.base =
      limb.toNat x * limb.toNat y

/-- 32-bit limbs, at base `2³²`, by the word operations of `MPN.UInt`. -/
@[expose, inline]
public def Limb.uint32 : Limb UInt32 where
  base := 2 ^ 32
  toNat := UInt32.toNat
  ofNat n h := UInt32.ofNatLT n h
  addc := UInt32.addWithCarry
  subb := UInt32.subWithBorrow
  muld x y := UInt32.mulAddAdd x y 0 0

/-- 32-bit limbs meet the specification, from the specifications of the word operations. -/
public instance : LawfulLimb Limb.uint32 where
  toNat_lt_base x := x.toNat_lt
  toNat_ofNat n h := UInt32.toNat_ofNatLT (h := h)
  ofNat_toNat x := UInt32.ofNatLT_toNat x
  addc_lo {cy x y} := by
    have h := UInt32.addWithCarry_spec x y cy
    simp only [Limb.uint32]
    generalize x.addWithCarry y cy = r at *
    obtain ⟨lo, c⟩ := r
    have := lo.toNat_lt
    cases c <;> cases cy <;> simp at * <;> lia
  addc_cy {cy x y} := by
    have h := UInt32.addWithCarry_spec x y cy
    simp only [Limb.uint32]
    generalize x.addWithCarry y cy = r at *
    obtain ⟨lo, c⟩ := r
    have := lo.toNat_lt
    cases c <;> cases cy <;> simp at * <;> lia
  subb_lo {bw x y} := by
    have h := UInt32.subWithBorrow_spec x y bw
    simp only [Limb.uint32]
    generalize x.subWithBorrow y bw = r at *
    obtain ⟨lo, b⟩ := r
    have := lo.toNat_lt
    have := x.toNat_lt
    cases b <;> cases bw <;> simp at * <;> lia
  subb_bw {bw x y} := by
    have h := UInt32.subWithBorrow_spec x y bw
    simp only [Limb.uint32]
    generalize x.subWithBorrow y bw = r at *
    obtain ⟨lo, b⟩ := r
    have := lo.toNat_lt
    have := x.toNat_lt
    cases b <;> cases bw <;> simp at * <;> lia
  muld {x y} := by
    simpa [Limb.uint32] using UInt32.mulAddAdd_spec x y 0 0
