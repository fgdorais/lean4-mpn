import Lake
open Lake DSL

package «lean4-bignum» where
  version := v!"0.1.0"
  testDriver := "BignumTest"

-- Switch to `main` once fgdorais/lean4-scalar-arrays#9 is merged.
require «lean4-scalar-arrays» from git
  "https://github.com/fgdorais/lean4-scalar-arrays" @ "bignum-test"

/-- The native implementations of the word operations. -/
target bignum.o pkg : System.FilePath := do
  let src ← inputTextFile <| pkg.dir / "c" / "bignum.c"
  buildLeanO (pkg.buildDir / "c" / "bignum.o") src (traceArgs := #["-O3", "-fPIC"])

@[default_target]
lean_lib Bignum where
  moreLinkObjs := #[bignum.o]

@[default_target]
lean_lib BignumTest where
  precompileModules := true
