import Lake
open Lean Lake DSL

/-!
# Build configuration

The package has three libraries: `MPN`, the code shared by both limb widths, `MPN32`, on 32-bit
limbs, and `MPN64`, on 64-bit limbs; a project imports the one it uses (`MPN.Default` gives
`MPN.Nat`, the 64-bit one). It can configure how they are built, which Lake otherwise does with
this package's own settings, by passing options with its `require`. In a `lakefile.toml`:

```toml
[[require]]
name = "lean4-mpn"
git = "https://github.com/fgdorais/lean4-mpn"
rev = "unified"
options = { march = "native", w64_mulKaratsuba = "48" }
```

or in a `lakefile.lean`, `require «lean4-mpn» from git "…" @ "unified" with
NameMap.empty |>.insert `march "native"`. The same options work on the command line with `-K`,
for example `lake build -R -K march=native`. Lake keeps the configuration it elaborated, so after
changing the options, build once with `-R` to reconfigure.

* `march`: compiles the library's C code with `-march=<value>`, for example `native`, which lets
  the C compiler use the vector instructions of the machine. The binaries then run only on
  processors with those instructions.
* The thresholds of each width, by the names of the fields of its `Config` (`MPN.W32.Config`,
  `MPN.W64.Config`) with the prefix `w32_` or `w64_`, for example `w32_mulKaratsuba`. The keys
  have no dots, since TOML passes a quoted key as one name.
  On 32-bit limbs: `mulKaratsuba`, `mulToom3`, `mulToom32`, `mulToom42`, `mulToom43`, `mulToom4`,
  `mulToom6`, `mulFFT`, `mulUnbalanced`, `mulRows`, `mulCombaW`, `sqrBasecase`, `sqrRows`,
  `sqrKaratsuba`, `sqrToom3`, `sqrToom4`, `sqrToom6`, `sqrFFT`, `divDC`, `divMu`, `div1Recip`,
  `div1Unnorm`, `div32Recip`, `sqrtZimmermann`, `sqrtBase`, `gcdHalf`, `strDC`, `parseDC`.
  On 64-bit limbs: `mulKaratsuba`, `mulToom3`, `mulToom32`, `mulToom42`, `mulToom43`, `mulToom4`,
  `mulToom6`, `mulFFT`, `mulFFTUnbal`, `mulFFTMin`, `mulUnbalanced`, `mulChunkMax`, `sqrKaratsuba`,
  `sqrToom3`, `sqrToom4`, `sqrToom6`, `sqrFFT`, `divDC`, `divMu`, `divQMu`, `div1Recip`,
  `div1Unnorm`, `div32Recip`, `sqrtZimmermann`, `sqrtBase`, `gcdHalf`, `strDC`, `parseDC`.
-/

/--
The thresholds of `MPN32` given as options, as its `mpn.w32.*` options. The options are typed, so
a value is passed as a number; one that is not a number is passed as a string, which the library
then rejects when it reads its options.
-/
def thresholdOptions32 : Array LeanOption :=
  let opt (key : Name) (val? : Option String) : Array LeanOption :=
    match val? with
    | some val =>
      #[{ name := `weak.mpn.w32 ++ key,
          value := match val.toNat? with | some n => .ofNat n | none => .ofString val }]
    | none => #[]
  opt `mul.karatsubaThreshold (get_config? w32_mulKaratsuba) ++
    opt `mul.toom3Threshold (get_config? w32_mulToom3) ++
    opt `mul.toom32Threshold (get_config? w32_mulToom32) ++
    opt `mul.toom42Threshold (get_config? w32_mulToom42) ++
    opt `mul.toom43Threshold (get_config? w32_mulToom43) ++
    opt `mul.toom4Threshold (get_config? w32_mulToom4) ++
    opt `mul.toom6Threshold (get_config? w32_mulToom6) ++
    opt `mul.fftThreshold (get_config? w32_mulFFT) ++
    opt `mul.unbalancedThreshold (get_config? w32_mulUnbalanced) ++
    opt `sqr.basecaseThreshold (get_config? w32_sqrBasecase) ++
    opt `mul.rowsThreshold (get_config? w32_mulRows) ++
    opt `mul.combaWideThreshold (get_config? w32_mulCombaW) ++
    opt `sqr.rowsThreshold (get_config? w32_sqrRows) ++
    opt `sqr.karatsubaThreshold (get_config? w32_sqrKaratsuba) ++
    opt `sqr.toom3Threshold (get_config? w32_sqrToom3) ++
    opt `sqr.toom4Threshold (get_config? w32_sqrToom4) ++
    opt `sqr.toom6Threshold (get_config? w32_sqrToom6) ++
    opt `sqr.fftThreshold (get_config? w32_sqrFFT) ++
    opt `div.dcThreshold (get_config? w32_divDC) ++
    opt `div.muThreshold (get_config? w32_divMu) ++
    opt `div.recip1Threshold (get_config? w32_div1Recip) ++
    opt `div.recip32Threshold (get_config? w32_div32Recip) ++
    opt `div.recip1UnnormThreshold (get_config? w32_div1Unnorm) ++
    opt `sqrt.zimmermannThreshold (get_config? w32_sqrtZimmermann) ++
    opt `sqrt.baseThreshold (get_config? w32_sqrtBase) ++
    opt `gcd.halfThreshold (get_config? w32_gcdHalf) ++
    opt `str.dcThreshold (get_config? w32_strDC) ++
    opt `str.parseDCThreshold (get_config? w32_parseDC)

/-- The thresholds of `MPN64` given as options, as its `mpn.w64.*` options. -/
def thresholdOptions64 : Array LeanOption :=
  let opt (key : Name) (val? : Option String) : Array LeanOption :=
    match val? with
    | some val =>
      #[{ name := `weak.mpn.w64 ++ key,
          value := match val.toNat? with | some n => .ofNat n | none => .ofString val }]
    | none => #[]
  opt `mul.karatsubaThreshold (get_config? w64_mulKaratsuba) ++
    opt `mul.toom3Threshold (get_config? w64_mulToom3) ++
    opt `mul.toom32Threshold (get_config? w64_mulToom32) ++
    opt `mul.toom42Threshold (get_config? w64_mulToom42) ++
    opt `mul.toom43Threshold (get_config? w64_mulToom43) ++
    opt `mul.toom4Threshold (get_config? w64_mulToom4) ++
    opt `mul.toom6Threshold (get_config? w64_mulToom6) ++
    opt `mul.fftThreshold (get_config? w64_mulFFT) ++
    opt `mul.fftUnbalancedThreshold (get_config? w64_mulFFTUnbal) ++
    opt `mul.fftMinThreshold (get_config? w64_mulFFTMin) ++
    opt `mul.unbalancedThreshold (get_config? w64_mulUnbalanced) ++
    opt `mul.unbalancedMaxThreshold (get_config? w64_mulChunkMax) ++
    opt `sqr.karatsubaThreshold (get_config? w64_sqrKaratsuba) ++
    opt `sqr.toom3Threshold (get_config? w64_sqrToom3) ++
    opt `sqr.toom4Threshold (get_config? w64_sqrToom4) ++
    opt `sqr.toom6Threshold (get_config? w64_sqrToom6) ++
    opt `sqr.fftThreshold (get_config? w64_sqrFFT) ++
    opt `div.dcThreshold (get_config? w64_divDC) ++
    opt `div.muThreshold (get_config? w64_divMu) ++
    opt `div.quotMuThreshold (get_config? w64_divQMu) ++
    opt `div.recip1Threshold (get_config? w64_div1Recip) ++
    opt `div.recip1UnnormThreshold (get_config? w64_div1Unnorm) ++
    opt `div.recip32Threshold (get_config? w64_div32Recip) ++
    opt `sqrt.zimmermannThreshold (get_config? w64_sqrtZimmermann) ++
    opt `sqrt.baseThreshold (get_config? w64_sqrtBase) ++
    opt `gcd.halfThreshold (get_config? w64_gcdHalf) ++
    opt `str.dcThreshold (get_config? w64_strDC) ++
    opt `str.parseDCThreshold (get_config? w64_parseDC)

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
  moreLeancArgs := marchArgs

@[default_target]
lean_lib MPN32 where
  leanOptions := thresholdOptions32
  moreLeancArgs := marchArgs

@[default_target]
lean_lib MPN64 where
  leanOptions := thresholdOptions64
  moreLeancArgs := marchArgs ++ #["-falign-loops=64"]

/-- `MPN.Nat`, the natural numbers on 64-bit limbs, for projects that use one width. -/
@[default_target]
lean_lib MPNDefault where
  roots := #[`MPN.Default]

@[default_target]
lean_lib MPNTest where
  precompileModules := true

/-- Times `MPN32` against `Nat`: `lake exe bench32 [op…] [size…]`, see `MPN32/BENCH.md`. -/
lean_exe bench32 where
  root := `Bench.W32

/-- Measures the thresholds of `MPN.W32.Config` on this machine: `lake exe tune32`. -/
lean_exe tune32 where
  root := `Tune.W32

/--
Times `MPN64` against `Nat`: `lake exe bench64 [--no-nat] [op…] [size…]`, see
`MPN64/BENCH.md`.
-/
lean_exe bench64 where
  root := `Bench.W64

/-- Measures the thresholds of `MPN.W64.Config` on this machine: `lake exe tune64 [--verbose]`. -/
lean_exe tune64 where
  root := `Tune.W64
