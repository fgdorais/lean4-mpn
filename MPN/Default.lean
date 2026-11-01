/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import MPN64

/-!
# The default natural numbers

`MPN.Nat` is `MPN.W64.Nat`, the natural numbers on 64-bit limbs, with its functions `ofNat`,
`ofString?` and `sqrt`; the rest of its operations are `main`'s `GNat` and its instances. The
natural numbers on 32-bit limbs are `MPN.W32.Nat`, from `MPN32`. It is the library `MPNDefault`, apart
from the shared root `MPN`, which both widths import.
-/

namespace MPN

/-- The natural numbers on 64-bit limbs. -/
public abbrev Nat := W64.Nat

namespace Nat

export W64.Nat (ofNat ofString? sqrt toNat_sqrt)

end Nat

end MPN
