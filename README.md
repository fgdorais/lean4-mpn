# Lean 4 / Bignum

Verified arbitrary-precision natural numbers for Lean 4, stored as `UInt32` limbs in the unboxed
arrays of [lean4-scalar-arrays](https://github.com/fgdorais/lean4-scalar-arrays). Each operation is
proved correct against `Nat`, the specification being the value of the list of limbs. Addition and
subtraction are linear; multiplication and squaring use schoolbook or Karatsuba depending on the
sizes, and very unbalanced products are split into nearly balanced ones.

## Tuning

Multiplication and squaring switch algorithms at size thresholds collected in `Bignum.Config`. The
defaults were measured on one machine; `lake exe tune` measures them on yours in about a minute and
prints the line to add to the `Bignum` library in `lakefile.toml`, for example:

```toml
leanOptions = { weak.bignum.mul.karatsubaThreshold = 68, weak.bignum.mul.unbalancedThreshold = 160, weak.bignum.sqr.basecaseThreshold = 62, weak.bignum.sqr.karatsubaThreshold = 272 }
```
