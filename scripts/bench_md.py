#!/usr/bin/env python3
# Copyright © 2026 François G. Dorais. All rights reserved.
# Released under Apache 2.0 license as described in the file LICENSE.
"""
Turns the output of `lake exe bench` into the Markdown tables of BENCH.md.

    taskset -c 2 .lake/build/bin/bench > bench.txt
    scripts/bench_md.py bench.txt

prints two tables, operations by size: the ratio MPN / Nat, and the time of MPN. Lines that
are not rows of the benchmark (the header, other output) are ignored, so the output of several
runs can be concatenated. A row that appears more than once keeps the fastest time of each
column: some processes run every trial of an operation slower than others, and the fastest of a
few runs is the time without that.
"""

import sys

UNITS = {'ns': 1.0, 'µs': 1e3, 'ms': 1e6, 's': 1e9}


def parse(lines):
    """Rows (op, limbs, mpn ns, nat ns or None), in the order they appear."""
    rows = []
    for line in lines:
        f = line.split()
        if len(f) < 4 or f[0] == 'op' or not f[1].isdigit():
            continue
        try:
            mpn = float(f[2]) * UNITS[f[3]]
        except (ValueError, KeyError):
            continue
        nat = None
        if len(f) >= 6 and f[5] in UNITS:
            nat = float(f[4]) * UNITS[f[5]]
        rows.append((f[0], int(f[1]), mpn, nat))
    return rows


def merge(rows):
    """One row per (op, limbs), with the fastest time of each column, in first-seen order."""
    best = {}
    for op, n, mpn, nat in rows:
        if (op, n) in best:
            _, _, m, t = best[(op, n)]
            mpn = min(mpn, m)
            nat = t if nat is None else nat if t is None else min(nat, t)
        best[(op, n)] = (op, n, mpn, nat)
    return list(best.values())


def fmt_time(ns):
    for unit, scale in (('s', 1e9), ('ms', 1e6), ('µs', 1e3)):
        if ns >= scale:
            return f'{ns / scale:.3g} {unit}'
    return f'{ns:.3g} ns'


def table(rows, cell):
    ops = list(dict.fromkeys(r[0] for r in rows))
    sizes = sorted({r[1] for r in rows})
    data = {(r[0], r[1]): r for r in rows}
    out = ['| op | ' + ' | '.join(str(n) for n in sizes) + ' |',
           '|---|' + '---:|' * len(sizes)]
    for op in ops:
        cells = [cell(data[(op, n)]) if (op, n) in data else '' for n in sizes]
        out.append(f'| `{op}` | ' + ' | '.join(cells) + ' |')
    return '\n'.join(out)


def main():
    rows = merge(parse(open(sys.argv[1], encoding='utf-8') if len(sys.argv) > 1 else sys.stdin))
    print('Ratio MPN / Nat (below 1 is faster than Nat):\n')
    print(table(rows, lambda r: f'{r[2] / r[3]:.2f}' if r[3] else ''))
    print('\nTime of MPN:\n')
    print(table(rows, lambda r: fmt_time(r[2])))


if __name__ == '__main__':
    main()
