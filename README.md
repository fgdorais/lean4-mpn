# Lean 4 / Bignum

Arbitrary-precision natural numbers for Lean 4, stored as `UInt32` limbs in the unboxed arrays of
[lean4-scalar-arrays](https://github.com/fgdorais/lean4-scalar-arrays). Addition and
multiplication are the schoolbook algorithms, and the tests check them against `Nat`.
