/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import MPN.Config

/-!
# The library's thresholds

`config` is the `Config` of the library, from the `mpn.*` options set when it is compiled. It is
in a module of its own, since a module cannot read the options it registers, and the base cases of
multiplication read it too.
-/

namespace MPN

/-- The thresholds of the library, from the `mpn.*` options set when it is compiled. -/
public def config : Config := mpn_config%

end MPN
