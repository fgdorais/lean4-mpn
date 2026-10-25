import Lake
open Lake DSL

package «lean4-mpn» where
  version := v!"0.1.0"

require «lean4-scalar-arrays» from git
  "https://github.com/fgdorais/lean4-scalar-arrays" @ "main"

@[default_target]
lean_lib MPN
