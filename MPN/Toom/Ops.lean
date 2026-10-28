/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import MPN.LimbArray

/-!
# The operations of the Karatsuba and Toom methods

The methods of `MPN.Toom` write a product into a window of the array of the result, in place, and
compute the values at their points in new arrays, changed in place by linear passes. `ToomOps`
gives those passes, the product and the square below the thresholds, and the middle term of
Karatsuba's method, with their specifications on `LimbArray.valAt`. A window is `len` limbs of an
array from limb `o` on; an operation writes one window of its first array and reads windows of the
others. `main32` and `main64` instantiate the class with their kernels on 32-bit and 64-bit limbs.

The specifications only assume that the window written is within its array. The kernels of the
branches need more, such as indices that fit in a `USize`; their instances check it and otherwise
write the value of the specification with `LimbArray.writeNat`, which never happens.
-/

namespace MPN.Toom

open LimbArray

variable {A L : Type} [LimbArray A L]

/-- `b` is `a` with only the limbs in `[o, o + len)` changed. -/
@[expose] public def Writes (b a : A) (o len : Nat) : Prop :=
  LimbArray.size b = LimbArray.size a ∧
    ∀ i, (i < o ∨ o + len ≤ i) → LimbArray.get b i = LimbArray.get a i

public theorem Writes.refl (a : A) (o len : Nat) : Writes a a o len := ⟨rfl, fun _ _ => rfl⟩

/-- Writes within a window are writes within any window that contains it. -/
public theorem Writes.mono {b a : A} {o len o' len' : Nat} (h : Writes b a o len)
    (h₁ : o' ≤ o) (h₂ : o + len ≤ o' + len') : Writes b a o' len' :=
  ⟨h.1, fun i hi => h.2 i (by lia)⟩

public theorem Writes.trans {c b a : A} {o len : Nat} (h₁ : Writes c b o len)
    (h₂ : Writes b a o len) : Writes c a o len :=
  ⟨h₁.1.trans h₂.1, fun i hi => (h₁.2 i hi).trans (h₂.2 i hi)⟩

/-- A window outside the one written keeps its value. -/
public theorem Writes.valAt_eq {b a : A} {o len : Nat} (h : Writes b a o len) {lo n : Nat}
    (hd : lo + n ≤ o ∨ o + len ≤ lo) : valAt b lo n = valAt a lo n :=
  valAt_congr _ fun i h₁ h₂ => h.2 i (by lia)

/-- The value of `writeNat`, and the limbs it writes. -/
public theorem writes_writeNat (a : A) (o len v : Nat) :
    Writes (writeNat a o len v) a o len :=
  ⟨size_writeNat .., fun i hi => get_writeNat a o len v i hi⟩

/--
The in-place operations of the Karatsuba and Toom methods on arrays of limbs, with their
specifications. `D` is the value of the window written before the operation and `S` the value of
the window read.
-/
public class ToomOps (A : Type) (L : outParam Type) [LimbArray A L] where
  /-- The limbs have at least 32 bits, for the multipliers of the interpolations, up to `9¹⁰`. -/
  w_ge : 32 ≤ LimbArray.w A
  /-- An array of `n` zero limbs. -/
  zeros : Nat → A
  size_zeros : ∀ n, LimbArray.size (zeros n) = n
  val_get_zeros : ∀ n i, LimbArray.val (A := A) (LimbArray.get (zeros n) i) = 0
  /-- `D + S`: `addInto d o len s so sl`. -/
  addInto : A → Nat → Nat → A → Nat → Nat → A
  addInto_spec : ∀ (d : A) (o len : Nat) (s : A) (so sl : Nat), o + len ≤ LimbArray.size d →
    valAt d o len + valAt s so sl < 2 ^ (LimbArray.w A * len) →
    Writes (addInto d o len s so sl) d o len ∧
      valAt (addInto d o len s so sl) o len = valAt d o len + valAt s so sl
  /-- `D - S`: `subInto d o len s so sl`. -/
  subInto : A → Nat → Nat → A → Nat → Nat → A
  subInto_spec : ∀ (d : A) (o len : Nat) (s : A) (so sl : Nat), o + len ≤ LimbArray.size d →
    valAt s so sl ≤ valAt d o len →
    Writes (subInto d o len s so sl) d o len ∧
      valAt (subInto d o len s so sl) o len = valAt d o len - valAt s so sl
  /-- `D + S v` for a limb `v`: `addMulInto d o len s so sl v`. -/
  addMulInto : A → Nat → Nat → A → Nat → Nat → Nat → A
  addMulInto_spec : ∀ (d : A) (o len : Nat) (s : A) (so sl v : Nat), o + len ≤ LimbArray.size d →
    v < 2 ^ LimbArray.w A → valAt d o len + valAt s so sl * v < 2 ^ (LimbArray.w A * len) →
    Writes (addMulInto d o len s so sl v) d o len ∧
      valAt (addMulInto d o len s so sl v) o len = valAt d o len + valAt s so sl * v
  /-- `D - S v` for a limb `v`: `subMulInto d o len s so sl v`. -/
  subMulInto : A → Nat → Nat → A → Nat → Nat → Nat → A
  subMulInto_spec : ∀ (d : A) (o len : Nat) (s : A) (so sl v : Nat), o + len ≤ LimbArray.size d →
    v < 2 ^ LimbArray.w A → valAt s so sl * v ≤ valAt d o len →
    Writes (subMulInto d o len s so sl v) d o len ∧
      valAt (subMulInto d o len s so sl v) o len = valAt d o len - valAt s so sl * v
  /--
  `D 2^(w - 1)`, wrapped: an even `D` that fits in all but the top limb ends up halved in the
  limbs from the second on.
  -/
  shlTop : A → Nat → Nat → A
  shlTop_spec : ∀ (d : A) (o len : Nat), o + len ≤ LimbArray.size d →
    Writes (shlTop d o len) d o len ∧
      valAt (shlTop d o len) o len = valAt d o len * 2 ^ (LimbArray.w A - 1) %
        2 ^ (LimbArray.w A * len)
  /-- `D / 2ˢ` for `0 < s < w`: `shr d o len s`. -/
  shr : A → Nat → Nat → Nat → A
  shr_spec : ∀ (d : A) (o len s : Nat), o + len ≤ LimbArray.size d → 0 < s →
    s < LimbArray.w A →
    Writes (shr d o len s) d o len ∧ valAt (shr d o len s) o len = valAt d o len / 2 ^ s
  /-- `D / q` for an odd limb `q` that divides `D`: `divExact d o len q`. -/
  divExact : A → Nat → Nat → Nat → A
  divExact_spec : ∀ (d : A) (o len q : Nat), o + len ≤ LimbArray.size d → q % 2 = 1 →
    q < 2 ^ LimbArray.w A → valAt d o len % q = 0 →
    Writes (divExact d o len q) d o len ∧ valAt (divExact d o len q) o len = valAt d o len / q
  /-- `0`: `zeroInto d o len`. -/
  zeroInto : A → Nat → Nat → A
  zeroInto_spec : ∀ (d : A) (o len : Nat), o + len ≤ LimbArray.size d →
    Writes (zeroInto d o len) d o len ∧ valAt (zeroInto d o len) o len = 0
  /-- `x + y` in a new array of `xl + 1` limbs: `sum x xo xl y yo yl`, for `yl ≤ xl`. -/
  sum : A → Nat → Nat → A → Nat → Nat → A
  sum_spec : ∀ (x : A) (xo xl : Nat) (y : A) (yo yl : Nat), yl ≤ xl →
    LimbArray.size (sum x xo xl y yo yl) = xl + 1 ∧
      valAt (sum x xo xl y yo yl) 0 (xl + 1) = valAt x xo xl + valAt y yo yl
  /--
  The middle term of Karatsuba's method: with `Z₀` in the `2 k` limbs of `d` from `o` on and `Z₂`
  in the `n - 2 k` limbs above, and `t = Z₀ + Z₁ + Z₂` in the `2 k + 2` limbs of `t`, writes
  `Z₀ + 2^(w k) Z₁ + 2^(2 w k) Z₂` into the `n` limbs from `o`: `mid d o k n t`.
  -/
  mid : A → Nat → Nat → Nat → A → A
  mid_spec : ∀ (d : A) (o k n : Nat) (t : A), o + n ≤ LimbArray.size d →
    Writes (mid d o k n t) d o n ∧
      ∀ Z₁, valAt t 0 (k + k + 2) = valAt d o (k + k) + Z₁ + valAt d (o + (k + k)) (n - (k + k)) →
        valAt d o (k + k) + 2 ^ (LimbArray.w A * k) * Z₁ +
            2 ^ (LimbArray.w A * (k + k)) * valAt d (o + (k + k)) (n - (k + k)) <
          2 ^ (LimbArray.w A * n) →
        valAt (mid d o k n t) o n = valAt d o (k + k) + 2 ^ (LimbArray.w A * k) * Z₁ +
          2 ^ (LimbArray.w A * (k + k)) * valAt d (o + (k + k)) (n - (k + k))
  /-- `x y` into the `xl + yl` limbs of `d` from `o` on: `mulBase d o x xo xl y yo yl`. -/
  mulBase : A → Nat → A → Nat → Nat → A → Nat → Nat → A
  mulBase_spec : ∀ (d : A) (o : Nat) (x : A) (xo xl : Nat) (y : A) (yo yl : Nat),
    o + (xl + yl) ≤ LimbArray.size d →
    Writes (mulBase d o x xo xl y yo yl) d o (xl + yl) ∧
      valAt (mulBase d o x xo xl y yo yl) o (xl + yl) = valAt x xo xl * valAt y yo yl
  /-- `x²` into the `2 xl` limbs of `d` from `o` on: `sqrBase d o x xo xl`. -/
  sqrBase : A → Nat → A → Nat → Nat → A
  sqrBase_spec : ∀ (d : A) (o : Nat) (x : A) (xo xl : Nat), o + (xl + xl) ≤ LimbArray.size d →
    Writes (sqrBase d o x xo xl) d o (xl + xl) ∧
      valAt (sqrBase d o x xo xl) o (xl + xl) = valAt x xo xl * valAt x xo xl

/--
The thresholds of the methods, in limbs. The branches' configurations extend it, with their
defaults.
-/
public structure Config where
  /-- The size of the larger operand from which multiplication uses Karatsuba. -/
  mulKaratsuba : Nat
  /-- Karatsuba needs at least `4` limbs to make its products smaller. -/
  four_le_mulKaratsuba : 4 ≤ mulKaratsuba
  /--
  The size of the smaller operand from which multiplication uses Toom-3, Toom-3 by 2 or Toom-4 by 2,
  by the shape of the operands, instead of Karatsuba.
  -/
  mulToom3 : Nat
  /-- The Toom methods need at least `12` limbs for their splits. -/
  twelve_le_mulToom3 : 12 ≤ mulToom3
  /--
  The size of the smaller operand from which multiplication uses Toom-3 by 2 when the larger one
  is between three halves and three times as long (three pieces by two).
  -/
  mulToom32 : Nat
  /-- Toom-3 by 2 needs at least `12` limbs for its split. -/
  twelve_le_mulToom32 : 12 ≤ mulToom32
  /--
  The size of the smaller operand from which multiplication uses Toom-4 by 2 when the larger one
  is between two and four times as long (four pieces by two), where Toom-3 by 2 does not apply.
  -/
  mulToom42 : Nat
  /-- Toom-4 by 2 needs at least `12` limbs for its split. -/
  twelve_le_mulToom42 : 12 ≤ mulToom42
  /--
  The size of the smaller operand from which multiplication uses Toom-4 or Toom-4 by 3, by the
  shape of the operands.
  -/
  mulToom4 : Nat
  /-- Toom-4 needs at least `32` limbs for its split. -/
  thirtytwo_le_mulToom4 : 32 ≤ mulToom4
  /--
  The size of the smaller operand from which multiplication uses Toom-4 by 3 when the larger one
  is between four thirds and twice as long (four pieces by three).
  -/
  mulToom43 : Nat
  /-- Toom-4 by 3 needs at least `32` limbs for its split. -/
  thirtytwo_le_mulToom43 : 32 ≤ mulToom43
  /--
  The size of the smaller operand from which multiplication uses Toom-6 when the larger one is less
  than six fifths as long.
  -/
  mulToom6 : Nat
  /-- Toom-6 needs at least `32` limbs for its split. -/
  thirtytwo_le_mulToom6 : 32 ≤ mulToom6
  /-- The size from which squaring uses Karatsuba instead of the schoolbook square. -/
  sqrKaratsuba : Nat
  /-- Karatsuba needs at least `4` limbs to make its squares smaller. -/
  four_le_sqrKaratsuba : 4 ≤ sqrKaratsuba
  /-- The size from which squaring uses Toom-3 instead of Karatsuba. -/
  sqrToom3 : Nat
  /-- Toom-3 needs at least `12` limbs for its split. -/
  twelve_le_sqrToom3 : 12 ≤ sqrToom3
  /-- The size from which squaring uses Toom-4 instead of Toom-3, from `sqrToom3` on. -/
  sqrToom4 : Nat
  /-- Toom-4 needs at least `32` limbs for its split. -/
  thirtytwo_le_sqrToom4 : 32 ≤ sqrToom4
  /-- The size from which squaring uses Toom-6 instead of Toom-4, from `sqrToom3` on. -/
  sqrToom6 : Nat
  /-- Toom-6 needs at least `32` limbs for its split. -/
  thirtytwo_le_sqrToom6 : 32 ≤ sqrToom6
  deriving Repr

end MPN.Toom
