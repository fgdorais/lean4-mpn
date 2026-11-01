/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MPN.Default
import MPN32

/-! The default `MPN.Nat` is the one on 64-bit limbs, and both widths build in one environment. -/

#guard (MPN.Nat.ofNat (10 ^ 40) * MPN.Nat.ofNat (10 ^ 40) + 1).toNat == 10 ^ 80 + 1
#guard (MPN.Nat.sqrt (MPN.Nat.ofNat (10 ^ 80))).toNat == 10 ^ 40
#guard (MPN.Nat.ofString? "123456789012345678901234567890").map (·.toNat) ==
  some 123456789012345678901234567890
#guard ((MPN.W32.Nat.ofNat (10 ^ 40) * MPN.W32.Nat.ofNat (10 ^ 40)).toNat ==
  (MPN.Nat.ofNat (10 ^ 40) * MPN.Nat.ofNat (10 ^ 40)).toNat)
