# Lean 4 / Bignum

Verified arbitrary-precision natural numbers for Lean 4, stored as `UInt32` limbs in the unboxed
arrays of [lean4-scalar-arrays](https://github.com/fgdorais/lean4-scalar-arrays). Each operation is
proved correct against `Nat`, the specification being the value of the list of limbs. Addition and
subtraction are linear. Multiplication uses schoolbook, Karatsuba or Toom-3 depending on the sizes,
and splits very unbalanced products into nearly balanced ones; squaring uses schoolbook,
Karatsuba or Toom-3. Division is Knuth's Algorithm D, and divide-and-conquer (Burnikel–Ziegler)
for large divisors.

`Bignum.BigNat` packages this as a `Nat`-like type, with a fast path on machine words below `2⁶⁴`
and the usual instances (`+ - * / %`, comparisons, `DecidableEq`, `Hashable`, literals, shifts,
bitwise operations, `^`, `ToString`, `Repr`), as well as `gcd`, `lcm`, `log2`, `sqrt` and
`ofString?`: every operation is proved to agree with `Nat` through `BigNat.toNat`, which is a
bijection, and `toString` and `ofString?` with `Nat.repr` and `String.toNat?`.

## Tuning

Multiplication and squaring switch algorithms at size thresholds collected in `Bignum.Config`. The
defaults were measured on one machine; `lake exe tune` measures them on yours in about a minute and
prints the line to add to the `Bignum` library in `lakefile.toml`, for example:

```toml
leanOptions = {
  weak.bignum.mul.karatsubaThreshold = 64,
  weak.bignum.mul.toom3Threshold = 480,
  weak.bignum.mul.unbalancedThreshold = 96,
  weak.bignum.sqr.basecaseThreshold = 2, weak.bignum.sqr.karatsubaThreshold = 96,
  weak.bignum.sqr.toom3Threshold = 720,
  weak.bignum.div.dcThreshold = 128}
```

## Programs

Write the main file of a program that uses the library as a `module`, with a `public def main`:

```lean
module

import Bignum

public def main : IO Unit := IO.println (Bignum.BigNat.ofNat (2 ^ 100))
```

`Bignum.Config` imports `Lean` at compile time for its thresholds, and a main file that is not a
`module` initializes everything its imports use at compile time too: the executable then links
all of Lean (about 120 MB) and spends about 20 ms initializing it at startup.

## Benchmark

`lake exe bench` times addition, subtraction, multiplication by a limb, multiplication, squaring
and division against the same operations on `Nat`, which Lean implements with GMP, from 1 to 4096
limbs; the `BigNat` operations are `badd`, `bsub`, `bmul`, `bdiv`, `bgcd`, `bshl`, `bshr`,
`bsqrt`, `btostr`, `bofstr`, and the conversions `btonat` and `bofnat`. Arguments select operations and sizes: `lake exe bench mul div 64
256` runs only those, and `--no-nat` skips `Nat`, which is useful under a profiler. Current
results, how to read them, and the history of performance changes are in [BENCH.md](BENCH.md).
