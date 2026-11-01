/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import MPN32.Basic

/-!
# Comparison

`lt a b` decides `toNat a < toNat b` from the top limb down, like GMP's `mpn_cmp`, reading limbs
past the end of the shorter slice as `0`, so the slices may have any sizes.
-/

open ScalarArray

namespace MPN.W32

/--
Whether `a < b`, like GMP's `mpn_cmp`: `main`'s `WordArray.ltWin` on the windows of the slices,
from the top limb down. The slices may have different sizes.
-/
public def lt (a b : UInt32Array.Slice) : Bool :=
  WordArray.ltWin a.array a.start a.size b.array b.start b.size

/-- `lt` decides `<` on the numbers. -/
public theorem lt_iff (a b : UInt32Array.Slice) : lt a b = true ↔ toNat a < toNat b := by
  rw [lt, WordArray.ltWin_iff, toNat_eq_valAt, toNat_eq_valAt]; rfl

end MPN.W32
