import Lake
open Lean Lake DSL

/-!
# Build configuration

A project that depends on this library can configure how it is built, which Lake otherwise does
with this package's own settings, by passing options with its `require`. In a `lakefile.toml`:

```toml
[[require]]
name = "lean4-mpn"
git = "https://github.com/fgdorais/lean4-mpn"
rev = "main"
options = { march = "native", mulKaratsuba = "48" }
```

or in a `lakefile.lean`, `require «lean4-mpn» from git "…" @ "main" with
NameMap.empty |>.insert `march "native"`. The same options work on the command line with `-K`,
for example `lake build -R -K march=native`. Lake keeps the configuration it elaborated, so after
changing the options, build once with `-R` to reconfigure.

* `march`: compiles the library's C code with `-march=<value>`, for example `native`, which lets
  the C compiler use the vector instructions of the machine (5–12% faster products on AVX2). The
  binaries then run only on processors with those instructions.
* `mulKaratsuba`, `mulToom3`, `mulToom32`, `mulToom42`, `mulUnbalanced`, `sqrBasecase`,
  `sqrKaratsuba`, `sqrToom3`, `divDC`: the thresholds, by the names of the fields of
  `MPN.Config`. The keys have no dots, since TOML passes a quoted key as one name.
-/

/--
The thresholds given as options, as the `mpn.*` options of the library. The options are typed,
so a value is passed as a number; one that is not a number is passed as a string, which the
library then rejects when it reads its options.
-/
def thresholdOptions : Array LeanOption :=
  let opt (key : Name) (val? : Option String) : Array LeanOption :=
    match val? with
    | some val =>
      #[{ name := `weak.mpn ++ key,
          value := match val.toNat? with | some n => .ofNat n | none => .ofString val }]
    | none => #[]
  opt `mul.karatsubaThreshold (get_config? mulKaratsuba) ++
    opt `mul.toom3Threshold (get_config? mulToom3) ++
    opt `mul.toom32Threshold (get_config? mulToom32) ++
    opt `mul.toom42Threshold (get_config? mulToom42) ++
    opt `mul.unbalancedThreshold (get_config? mulUnbalanced) ++
    opt `sqr.basecaseThreshold (get_config? sqrBasecase) ++
    opt `sqr.karatsubaThreshold (get_config? sqrKaratsuba) ++
    opt `sqr.toom3Threshold (get_config? sqrToom3) ++
    opt `div.dcThreshold (get_config? divDC)

/-- `-march=<value>` when the `march` option is given. -/
def marchArgs : Array String :=
  match get_config? march with
  | some m => #[s!"-march={m}"]
  | none => #[]

package «lean4-mpn» where
  version := v!"0.1.0"
  testDriver := "MPNTest"

require «lean4-scalar-arrays» from git
  "https://github.com/fgdorais/lean4-scalar-arrays" @ "main"

@[default_target]
lean_lib MPN where
  leanOptions := thresholdOptions
  moreLeancArgs := marchArgs

@[default_target]
lean_lib MPNTest where
  precompileModules := true

lean_exe tune where
  root := `Tune

lean_exe bench where
  root := `Bench
