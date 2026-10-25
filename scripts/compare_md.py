#!/usr/bin/env python3
# Copyright © 2026 François G. Dorais. All rights reserved.
# Released under Apache 2.0 license as described in the file LICENSE.
"""
Turns the benchmark output of `main32` and `main64` into the comparison tables of BENCH.md.

    scripts/compare_md.py bench/main32.txt bench/main64.txt

Each file is the output of that branch's `lake exe bench`, several runs concatenated (see
BENCH.md); a row that appears more than once keeps the fastest time of each column. The rows of
the two branches are matched by operation (`OPS`) and by size in bits: `n` limbs of 32 bits on
`main32` are `n / 2` limbs of 64 bits, except `bsqrt`, whose operand already has `2 n` limbs.
Prints three tables: the ratio to `Nat` (GMP) of each branch, and the speed-up of `main64` over
`main32`, the quotient of those ratios. Each library is compared with `Nat` in its own process,
since the same `Nat` operation can run up to a third faster in one benchmark binary than in the
other at small sizes, from where the code lands.
"""

import sys

UNITS = {'ns': 1.0, 'µs': 1e3, 'ms': 1e6, 's': 1e9}

# Common name: (main32 op, main64 op).
OPS = {
    'add': ('add', 'add'),
    'sub': ('sub', 'sub'),
    'mul1': ('mul1', 'mul1'),
    'mul': ('mul', 'auto'),
    'sqr': ('sqr', 'autosqr'),
    'shr': ('shr', 'shr'),
    'div': ('div', 'div'),
    'gcd': ('bgcd', 'gcd'),
    'sqrt': ('bsqrt', 'sqrt'),
    'str': ('btostr', 'str'),
    'parse': ('bofstr', 'parse'),
}

# main32 ops whose size is already in 64-bit limbs.
SAME_SIZE = {'bsqrt'}


def parse(path):
    """The fastest (mpn ns, nat ns) of each (op, limbs) in the file."""
    best = {}
    for line in open(path, encoding='utf-8'):
        f = line.split()
        if len(f) < 6 or f[0] == 'op' or not f[1].isdigit():
            continue
        try:
            mpn = float(f[2]) * UNITS[f[3]]
            nat = float(f[4]) * UNITS[f[5]]
        except (ValueError, KeyError):
            continue
        key = (f[0], int(f[1]))
        if key in best:
            mpn, nat = min(mpn, best[key][0]), min(nat, best[key][1])
        best[key] = (mpn, nat)
    return best


def table(cell, sizes):
    out = ['| op | ' + ' | '.join(str(k) for k in sizes) + ' |',
           '|---|' + '---:|' * len(sizes)]
    for name in OPS:
        out.append(f'| `{name}` | ' + ' | '.join(cell(name, k) for k in sizes) + ' |')
    return '\n'.join(out)


def main():
    b32, b64 = parse(sys.argv[1]), parse(sys.argv[2])

    def r32(name, k):
        op = OPS[name][0]
        return b32.get((op, k if op in SAME_SIZE else 2 * k))

    def r64(name, k):
        return b64.get((OPS[name][1], k))

    sizes = sorted({k for (_, k) in b64})
    ratio = lambda r: f'{r[0] / r[1]:.2f}' if r else ''
    print('Ratio to `Nat`, `main32`:\n')
    print(table(lambda n, k: ratio(r32(n, k)), sizes))
    print('\nRatio to `Nat`, `main64`:\n')
    print(table(lambda n, k: ratio(r64(n, k)), sizes))

    def speedup(name, k):
        a, b = r32(name, k), r64(name, k)
        return f'{(a[0] / a[1]) / (b[0] / b[1]):.2f}' if a and b else ''
    print('\nSpeed-up of `main64` over `main32` (ratio of `main32` / ratio of `main64`):\n')
    print(table(speedup, sizes))


if __name__ == '__main__':
    main()
