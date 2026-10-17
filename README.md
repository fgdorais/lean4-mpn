# Lean 4 / MPN

Verified arbitrary-precision natural numbers for Lean 4, stored as `UInt32` limbs in the unboxed
arrays of [lean4-scalar-arrays](https://github.com/fgdorais/lean4-scalar-arrays). Each operation is
proved correct against `Nat`, the specification being the value of the list of limbs. Addition and
subtraction are linear. Multiplication uses schoolbook, Karatsuba, Toom-3 or Toom-4, or their
unbalanced variants, depending on the sizes, and splits very unbalanced products into nearly
balanced ones; squaring uses schoolbook, Karatsuba or Toom-3. Division is Knuth's Algorithm D, and
divide-and-conquer (Burnikel–Ziegler) for large divisors.

`MPN.Nat` packages this as a `Nat`-like type, with a fast path on machine words below `2⁶⁴`
and the usual instances (`+ - * / %`, comparisons, `DecidableEq`, `Hashable`, literals, shifts,
bitwise operations, `^`, `ToString`, `Repr`), as well as `gcd`, `lcm`, `log2`, `sqrt` and
`ofString?`: every operation is proved to agree with `Nat` through `MPN.Nat.toNat`, which is a
bijection, and `toString` and `ofString?` with `Nat.repr` and `String.toNat?`.

## Tuning

Multiplication, squaring and division switch algorithms at size thresholds collected in
`MPN.Config`. The defaults were measured on one machine; `lake exe tune` measures them on yours
in a few minutes and prints the options that set them. A project that depends on this library
passes them with its `require`, together with `march`, which compiles the library's C code for a
given processor:

```toml
[[require]]
name = "lean4-mpn"
git = "https://github.com/fgdorais/lean4-mpn"
rev = "main"
options = { march = "native", mulKaratsuba = "64", mulToom3 = "480", divDC = "176" }
```

The keys are the fields of `MPN.Config`: `mulKaratsuba`, `mulToom3`, `mulToom32`, `mulToom42`,
`mulToom43`, `mulToom4`, `mulUnbalanced`, `sqrBasecase`, `sqrKaratsuba`, `sqrToom3` and `divDC`; an
invalid value stops the build. With `march = "native"` the C compiler may use the vector
instructions of the build machine (5–12% faster products with AVX2), and the program then runs only
on processors that have them. Lake keeps the configuration it elaborated, so after changing the
options, build once with `lake build -R`. In this package itself, the same options go on the command
line: `lake build -R -K march=native`.

## Programs

Write the main file of a program that uses the library as a `module`, with a `public def main`:

```lean
module

import MPN

public def main : IO Unit := IO.println (MPN.Nat.ofNat (2 ^ 100))
```

`MPN.Config` imports `Lean` at compile time for its thresholds, and a main file that is not a
`module` initializes everything its imports use at compile time too: the executable then links
all of Lean (about 120 MB) and spends about 20 ms initializing it at startup.

## Benchmark

`lake exe bench` times addition, subtraction, multiplication by a limb, multiplication, squaring
and division against the same operations on `Nat`, which Lean implements with GMP, from 1 to 4096
limbs; the `MPN.Nat` operations are `badd`, `bsub`, `bmul`, `bdiv`, `bgcd`, `bshl`, `bshr`,
`bsqrt`, `btostr`, `bofstr`, and the conversions `btonat` and `bofnat`. Arguments select
operations and sizes: `lake exe bench mul div 64 256` runs only those, and `--no-nat` skips `Nat`,
which is useful under a profiler. Current results, how to read them, and the history of
performance changes are in [BENCH.md](BENCH.md).
