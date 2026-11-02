# MPN32: 32-bit limbs

Verified arbitrary-precision natural numbers for Lean 4, stored as `UInt32` limbs in the unboxed
arrays of [lean4-scalar-arrays](https://github.com/fgdorais/lean4-scalar-arrays). Each operation is
proved correct against `Nat`, the specification being the value of the list of limbs. Addition and
subtraction are linear. Multiplication uses schoolbook, Karatsuba, Toom-3, Toom-4 or Toom-6, or
the unbalanced variants, and Schönhage–Strassen's FFT modulo `2ᴺ + 1` for the largest numbers,
depending on the sizes, and splits very unbalanced products into nearly balanced ones; squaring uses
the same algorithms. Division is Knuth's Algorithm D, divide-and-conquer (Burnikel–Ziegler) for
large divisors, and Barrett's division with Newton's reciprocal for the largest, by `MPN`'s shared
dispatch (`MPN.Dispatch.Div`).

`MPN.W32.Nat` packages this as a `Nat`-like type, with a fast path on machine words below `2⁶⁴`
and the usual instances (`+ - * / %`, comparisons, `DecidableEq`, `Hashable`, literals, shifts,
bitwise operations, `^`, `ToString`, `Repr`), as well as `gcd`, `lcm`, `log2`, `sqrt` and
`ofString?`: every operation is proved to agree with `Nat` through `MPN.W32.Nat.toNat`, which is a
bijection, and `toString` and `ofString?` with `Nat.repr` and `String.toNat?`.

This is the library `MPN32` (namespace `MPN.W32`). The part that does not depend on the width of a
limb (finite sums, polynomials, the FFT, Karatsuba and the Toom methods, the kernels over
`WordArray` and the base-generic algorithms of `MPN.Generic`) is the shared library `MPN`, with
instances for 32-bit limbs here such as `toomBase32` (`MPN32.Mul.ToomOps`), from which `MPN`
derives `ToomOps`, and `bridge32`, the bridge from `MPN.W32.Nat` to `MPN`'s algorithms; the
hand-tuned kernels of this width are in `MPN32/Arch/`. `MPN64` is the same on `UInt64` limbs.

## Tuning

Multiplication, squaring, division, the greatest common divisor and decimal strings switch
algorithms at size thresholds collected in `MPN32.Config`. The size crossovers were measured on
one machine (Zen 3), the choices of algorithm follow GMP's; `lake exe tune32` measures them on
yours in a few minutes and prints the options that set them. A project that depends on this
library passes them with its `require`, together with `march`, which compiles the library's C code
for a given processor:

```toml
[[require]]
name = "lean4-mpn"
git = "https://github.com/fgdorais/lean4-mpn"
rev = "main"
options = { march = "native", w32_mulKaratsuba = "64", w32_mulToom3 = "480", w32_divDC = "176" }
```

The keys are the fields of `MPN32.Config`: `mulKaratsuba`, `mulToom3`, `mulToom32`, `mulToom42`,
`mulToom43`, `mulToom4`, `mulToom6`, `mulFFT`, `mulFFTUnbal`, `mulFFTMin`, `mulUnbalanced`,
`mulChunkMax`, `mulRows`, `mulCombaW`, `sqrBasecase`, `sqrRows`, `sqrKaratsuba`, `sqrToom3`,
`sqrToom4`, `sqrToom6`, `sqrFFT`, `divDC`, `divMu`, `divQMu`, `div1Recip`, `div1Unnorm`,
`div32Recip`, `sqrtZimmermann`, `sqrtBase`, `gcdHalf`, `strDC` and `parseDC`; an invalid value
stops the build. With `march = "native"` the C compiler may use the vector instructions of the
build machine (5–12% faster products with AVX2), and the program then runs only on processors that
have them. Lake keeps the configuration it elaborated, so after changing the options, build once
with `lake build -R`. In this package itself, the same options go
on the command line: `lake build -R -K march=native`.

## Programs

Write the main file of a program that uses the library as a `module`, with a `public def main`:

```lean
module

import MPN32

public def main : IO Unit := IO.println (MPN.W32.Nat.ofNat (2 ^ 100))
```

`MPN32.Config` imports `Lean` at compile time for its thresholds, and a main file that is not a
`module` initializes everything its imports use at compile time too: the executable then links
all of Lean (about 120 MB) and spends about 20 ms initializing it at startup.

## Benchmark

`lake exe bench32` times addition, subtraction, multiplication by a limb, multiplication, squaring
and division against the same operations on `Nat`, which Lean implements with GMP, from 1 to 4096
limbs; the `MPN.W32.Nat` operations, the same on both widths (`Bench.Harness`), are `badd`, `bsub`,
`bmul`, `bdiv`, `bmod`, `band`, `bor`, `bxor`, `bgcd`, `blcm`, `bsqr`, `bpow`, `bshl`, `bshr`,
`bsqrt`, `blog2`, `bcmp`, `beq`, `bhash`, `btostr`, `bofstr`, and the conversions `btonat` and
`bofnat`. Arguments select
operations and sizes: `lake exe bench32 mul div 64 256` runs only those, and `--no-nat` skips `Nat`,
which is useful under a profiler. Current results, how to read them, and the history of
performance changes are in [BENCH.md](BENCH.md).
