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
rev = "main"
options = { march = "native", w64_mulKaratsuba = "48" }
```

or in a `lakefile.lean`, `require «lean4-mpn» from git "…" @ "main" with
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
  `mulToom6`, `mulToom8`, `mulFFT`, `mulUnbalanced`, `mulRows`, `mulCombaW`, `sqrBasecase`,
  `sqrRows`, `sqrKaratsuba`, `sqrToom3`, `sqrToom4`, `sqrToom6`, `sqrToom8`, `sqrFFT`, `divDC`,
  `divMu`, `divQMu`, `div1Recip`, `div1Unnorm`, `div32Recip`, `div2Rows`, `sqrtZimmermann`,
  `sqrtBase`, `gcdHalf`, `strDC`, `parseDC`.
  On 64-bit limbs: `mulKaratsuba`, `mulToom3`, `mulToom32`, `mulToom42`, `mulToom43`, `mulToom4`,
  `mulToom6`, `mulToom8`, `mulFFT`, `mulFFTUnbal`, `mulFFTMin`, `mulUnbalanced`, `mulChunkMax`,
  `sqrKaratsuba`, `sqrToom3`, `sqrToom4`, `sqrToom6`, `sqrToom8`, `sqrFFT`, `divDC`, `divMu`,
  `divQMu`, `div1Recip`, `div1Unnorm`, `div32Recip`, `div2Rows`, `sqrtZimmermann`, `sqrtBase`,
  `sqrtRemRenorm`, `gcdHalf`, `strDC`, `parseDC`.
-/

/--
The thresholds of `MPN32` given as options, as its options `mpn.w32.f`, one for each field `f` of
`MPN.W32.Config`. The options are typed, so a value is passed as a number; one that is not a
number is passed as a string, which the library then rejects.
-/
def thresholdOptions32 : Array LeanOption :=
  let opt (key : Name) (val? : Option String) : Array LeanOption :=
    match val? with
    | some val =>
      #[{ name := `weak.mpn.w32 ++ key,
          value := match val.toNat? with | some n => .ofNat n | none => .ofString val }]
    | none => #[]
  opt `mulKaratsuba (get_config? w32_mulKaratsuba) ++
    opt `mulToom3 (get_config? w32_mulToom3) ++
    opt `mulToom32 (get_config? w32_mulToom32) ++
    opt `mulToom42 (get_config? w32_mulToom42) ++
    opt `mulToom43 (get_config? w32_mulToom43) ++
    opt `mulToom4 (get_config? w32_mulToom4) ++
    opt `mulToom6 (get_config? w32_mulToom6) ++
    opt `mulToom8 (get_config? w32_mulToom8) ++
    opt `mulFFT (get_config? w32_mulFFT) ++
    opt `mulUnbalanced (get_config? w32_mulUnbalanced) ++
    opt `sqrBasecase (get_config? w32_sqrBasecase) ++
    opt `mulRows (get_config? w32_mulRows) ++
    opt `mulCombaW (get_config? w32_mulCombaW) ++
    opt `sqrRows (get_config? w32_sqrRows) ++
    opt `sqrKaratsuba (get_config? w32_sqrKaratsuba) ++
    opt `sqrToom3 (get_config? w32_sqrToom3) ++
    opt `sqrToom4 (get_config? w32_sqrToom4) ++
    opt `sqrToom6 (get_config? w32_sqrToom6) ++
    opt `sqrToom8 (get_config? w32_sqrToom8) ++
    opt `sqrFFT (get_config? w32_sqrFFT) ++
    opt `divDC (get_config? w32_divDC) ++
    opt `divMu (get_config? w32_divMu) ++
    opt `divQMu (get_config? w32_divQMu) ++
    opt `div1Recip (get_config? w32_div1Recip) ++
    opt `div32Recip (get_config? w32_div32Recip) ++
    opt `div2Rows (get_config? w32_div2Rows) ++
    opt `div1Unnorm (get_config? w32_div1Unnorm) ++
    opt `sqrtZimmermann (get_config? w32_sqrtZimmermann) ++
    opt `sqrtBase (get_config? w32_sqrtBase) ++
    opt `gcdHalf (get_config? w32_gcdHalf) ++
    opt `strDC (get_config? w32_strDC) ++
    opt `parseDC (get_config? w32_parseDC)

/--
The thresholds of `MPN64` given as options, as its options `mpn.w64.f`, one for each field `f` of
`MPN.W64.Config`.
-/
def thresholdOptions64 : Array LeanOption :=
  let opt (key : Name) (val? : Option String) : Array LeanOption :=
    match val? with
    | some val =>
      #[{ name := `weak.mpn.w64 ++ key,
          value := match val.toNat? with | some n => .ofNat n | none => .ofString val }]
    | none => #[]
  opt `mulKaratsuba (get_config? w64_mulKaratsuba) ++
    opt `mulToom3 (get_config? w64_mulToom3) ++
    opt `mulToom32 (get_config? w64_mulToom32) ++
    opt `mulToom42 (get_config? w64_mulToom42) ++
    opt `mulToom43 (get_config? w64_mulToom43) ++
    opt `mulToom4 (get_config? w64_mulToom4) ++
    opt `mulToom6 (get_config? w64_mulToom6) ++
    opt `mulToom8 (get_config? w64_mulToom8) ++
    opt `mulFFT (get_config? w64_mulFFT) ++
    opt `mulFFTUnbal (get_config? w64_mulFFTUnbal) ++
    opt `mulFFTMin (get_config? w64_mulFFTMin) ++
    opt `mulUnbalanced (get_config? w64_mulUnbalanced) ++
    opt `mulChunkMax (get_config? w64_mulChunkMax) ++
    opt `sqrKaratsuba (get_config? w64_sqrKaratsuba) ++
    opt `sqrToom3 (get_config? w64_sqrToom3) ++
    opt `sqrToom4 (get_config? w64_sqrToom4) ++
    opt `sqrToom6 (get_config? w64_sqrToom6) ++
    opt `sqrToom8 (get_config? w64_sqrToom8) ++
    opt `sqrFFT (get_config? w64_sqrFFT) ++
    opt `divDC (get_config? w64_divDC) ++
    opt `divMu (get_config? w64_divMu) ++
    opt `divQMu (get_config? w64_divQMu) ++
    opt `div1Recip (get_config? w64_div1Recip) ++
    opt `div1Unnorm (get_config? w64_div1Unnorm) ++
    opt `div32Recip (get_config? w64_div32Recip) ++
    opt `div2Rows (get_config? w64_div2Rows) ++
    opt `sqrtZimmermann (get_config? w64_sqrtZimmermann) ++
    opt `sqrtBase (get_config? w64_sqrtBase) ++
    opt `sqrtRemRenorm (get_config? w64_sqrtRemRenorm) ++
    opt `gcdHalf (get_config? w64_gcdHalf) ++
    opt `strDC (get_config? w64_strDC) ++
    opt `parseDC (get_config? w64_parseDC)

/-- `-march=<value>` when the `march` option is given. -/
def marchArgs : Array String :=
  match get_config? march with
  | some m => #[s!"-march={m}"]
  | none => #[]

package «lean4-mpn» where
  version := v!"0.1.0"
  testDriver := "MPNTest"

require «lean4-scalar-arrays» from git
  "https://github.com/fgdorais/lean4-scalar-arrays" @ "83f89216f409c691f39810b929398018d5626a0a"

-- Loops aligned to 32 bytes in the shared code and on 32-bit limbs: at 64, the loops unrolled
-- twice of `sub` and `mul1` (about 72 bytes) put most of their instructions in one 64-byte window
-- of Zen 3's op cache, 7–14% slower; at 32 they start at most half a window in. The 64-bit
-- library keeps 64, for its square basecase.
@[default_target]
lean_lib MPN where
  moreLeancArgs := marchArgs ++ #["-falign-loops=32"]

@[default_target]
lean_lib MPN32 where
  leanOptions := thresholdOptions32
  moreLeancArgs := marchArgs ++ #["-falign-loops=32"]

-- The multiplications by a limb on 32-bit limbs and the modules below them, built without
-- unrolling: unrolled twice, the loop of `addMul1` is slower on Zen 3, while the Comba basecases of
-- the rest of `MPN32` are faster unrolled. The modules below hold no hot loops of their own (their
-- folds are specialized where they are used); they are here because a library may not import the
-- library that imports it. One root (`MPN32Base`, which imports them) makes its shared library
-- a plugin for the precompiled tests. Declared after `MPN32`: Lake gives a module to the last
-- library that contains it.
lean_lib MPN32Base where
  roots := #[`MPN32Base]
  globs := #[.one `MPN32Base, .one `MPN32.Mul.Limb, .one `MPN32.Basic, .one `MPN32.Arch.UInt,
    .one `MPN32.Arch.UIntArray, .one `MPN32.FoldInPlace]
  leanOptions := thresholdOptions32
  moreLeancArgs := marchArgs ++ #["-falign-loops=32", "-fno-unroll-loops"]

@[default_target]
lean_lib MPN64 where
  leanOptions := thresholdOptions64
  moreLeancArgs := marchArgs ++ #["-falign-loops=64"]

/--
`MPN.Nat`, the natural numbers on 64-bit limbs, for projects that use one width. The library is
named after its one root, which makes its shared library a plugin for the precompiled tests, loaded
after `MPN64`'s; under another name it is loaded before them, which Windows refuses (error 126).
-/
@[default_target]
lean_lib MPN.Default where

@[default_target]
lean_lib MPNTest where
  precompileModules := true

/-- What both widths' benches and tuners share: their harnesses and the shared searches. -/
lean_lib Harness where
  roots := #[`Tune.Harness, `Tune.Shared, `Bench.Mpn, `Bench.Harness]

/--
GMP's `mpn_*` kernels for the `mpn` column of the benches (`Bench/mpn.c`, `Bench.Mpn`), from the GMP
that Lean links into every executable for `Nat`. Only the bench executables link it.
-/
target mpnBench.o pkg : System.FilePath := do
  let oFile := pkg.buildDir / "c" / "mpn.o"
  let srcJob ← inputTextFile <| pkg.dir / "Bench" / "mpn.c"
  buildLeanO oFile srcJob #[] #["-fPIC", "-O2"]

/-- Times `MPN32` against `Nat`: `lake exe bench32 [op…] [size…]`, see `MPN32/BENCH.md`. -/
lean_exe bench32 where
  root := `Bench.W32
  moreLinkObjs := #[mpnBench.o]

/-- Measures the thresholds of `MPN.W32.Config` on this machine: `lake exe tune32`. -/
lean_exe tune32 where
  root := `Tune.W32

/--
Times `MPN64` against `Nat`: `lake exe bench64 [--no-nat] [op…] [size…]`, see
`MPN64/BENCH.md`.
-/
lean_exe bench64 where
  root := `Bench.W64
  moreLinkObjs := #[mpnBench.o]

/-- Measures the thresholds of `MPN.W64.Config` on this machine: `lake exe tune64 [--verbose]`. -/
lean_exe tune64 where
  root := `Tune.W64
