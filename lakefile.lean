import Lake
open Lake DSL

package «lean4-mpn» where
  version := v!"0.1.0"
  testDriver := "MPNTest"

require «lean4-scalar-arrays» from git
  "https://github.com/fgdorais/lean4-scalar-arrays" @ "main"

@[default_target]
lean_lib MPN

@[default_target]
lean_lib MPNTest where
  precompileModules := true

/-- Times the library against `Nat`: `lake exe bench [--no-nat] [op…] [size…]`, see BENCH.md. -/
lean_exe bench where
  root := `Bench
