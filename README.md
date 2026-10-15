# Lean 4 / Bignum

Verified arbitrary-precision natural numbers for Lean 4, stored as `UInt32` limbs in the unboxed
arrays of [lean4-scalar-arrays](https://github.com/fgdorais/lean4-scalar-arrays). Each operation is
proved correct against `Nat`, the specification being the value of the list of limbs. Addition and
subtraction are linear. Multiplication uses schoolbook, Karatsuba or Toom-3 depending on the sizes,
and splits very unbalanced products into nearly balanced ones; squaring uses schoolbook or
Karatsuba. Division is Knuth's Algorithm D.

## Tuning

Multiplication and squaring switch algorithms at size thresholds collected in `Bignum.Config`. The
defaults were measured on one machine; `lake exe tune` measures them on yours in about a minute and
prints the line to add to the `Bignum` library in `lakefile.toml`, for example:

```toml
leanOptions = { weak.bignum.mul.karatsubaThreshold = 88, weak.bignum.mul.toom3Threshold = 552, weak.bignum.mul.unbalancedThreshold = 152, weak.bignum.sqr.basecaseThreshold = 58, weak.bignum.sqr.karatsubaThreshold = 224 }
```

## Benchmark

`lake exe bench` times addition, subtraction, multiplication by a limb, multiplication, squaring
and division against the same operations on `Nat`, which Lean implements with GMP, from 1 to 4096
limbs. `lake exe bench mul div` runs only the operations named.
