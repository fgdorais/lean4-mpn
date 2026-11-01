#!/usr/bin/env python3
"""Generates `interp10` and `interp10_spec` in MPN/Mul/Toom.lean: the interpolation of Toom-6.

usage: scripts/toom6_interp.py MPN/Mul/Toom.lean

The values `w_j = P(j)`, `j = 1, …, 9`, of `P = c₀ + c₁ x + ⋯ + c₁₀ x¹⁰` become the coefficients
`c₁, …, c₉` in place:

1. `h(j) = w_j - j¹⁰ c₁₀` (`subMulInto` by the top coefficient), with `h(0) = c₀`;
2. the forward differences of `h` at `0, …, 9`, no division: afterwards `w_l = Δˡ h(0)`;
3. the Newton coefficients `Δˡ h(0) / l!`, by the odd part of `l!` (`divExactInto`) and a shift;
4. the change from the Newton basis on `0, 1, …, 8` to the monomials (Horner's rule, the passes
   of the existing definition, kept), and the recombination into the result (kept).

Every intermediate value is a combination of the coefficients with nonnegative integer
multipliers, which the script checks, so each pass is one step of the proof, with its value
checked by `lia`. The script replaces the definition and the theorem between their docstrings and
the next section.
"""
import re, sys
from fractions import Fraction
from math import factorial

SUB = str.maketrans('0123456789', '₀₁₂₃₄₅₆₇₈₉')
def sub(n): return str(n).translate(SUB)
def unsub(s): return int(s.translate(str.maketrans('₀₁₂₃₄₅₆₇₈₉', '0123456789')))

path = sys.argv[1]
src = open(path).read()
d0 = src.index('/--\nThe interpolation of degree 10 at `0, 1, …, 9, ∞`')
t0 = src.index('set_option maxHeartbeats 4000000 in\nprivate theorem interp10_spec')
t1 = src.index('/-! ## The three methods -/')
old_def = src[d0:t0]
old_thm = src[t0:t1]

# The old passes, to keep the Horner stage and to name the final buffers of the old proof.
pass_re = re.compile(r'^  let w(\S) := (.*)$')
old_lines = old_def.split('\n')
old_passes = []
for l in old_lines:
    m = pass_re.match(l)
    if m:
        old_passes.append((unsub(m.group(1)), m.group(2)))
horner_start = next(i for i, (j, e) in enumerate(old_passes)
                    if e.startswith('(subMulInto w₈.toUSlice w₉.toUSlice 8)'))
horner = old_passes[horner_start:]
old_final = {}
for i, (j, _) in enumerate(old_passes):
    old_final[j] = i + 1
for j in range(1, 10):
    old_final.setdefault(j, None)

# Symbolic values: dicts from coefficient index to multiplier.
def val_w(j): return {m: Fraction(j ** m) for m in range(11)}
def add(a, b, s=1):
    r = dict(a)
    for k, v in b.items():
        r[k] = r.get(k, 0) + s * v
    return {k: v for k, v in r.items() if v != 0}
def scale(a, s): return {k: v * s for k, v in a.items()}
def check(a, what):
    for k, v in a.items():
        assert v.denominator == 1 and v >= 0, (what, a)
def expr(a):
    terms = []
    for k in sorted(a):
        v = int(a[k])
        terms.append(f'c{sub(k)}' if v == 1 else f'{v} * c{sub(k)}')
    return ' + '.join(terms) if terms else '0'

X0 = {0: Fraction(1)}
XD = {10: Fraction(1)}

# The new passes: (kind, target, source or parameter).
passes = []
for j in range(1, 10):
    passes.append(('subXd', j, j ** 10))
for j in range(9, 1, -1):
    passes.append(('subW', j, j - 1))
passes.append(('subX0', 1, None))
for l in range(2, 10):
    for j in range(9, l - 1, -1):
        passes.append(('subW', j, j - 1))
for l in range(2, 10):
    f = factorial(l)
    s = (f & -f).bit_length() - 1
    odd = f >> s
    if odd > 1:
        passes.append(('div', l, odd))
    passes.append(('shr', l, s))
for j, e in horner:
    m = re.match(r'\(subMulInto w(\S)\.toUSlice w(\S)\.toUSlice (\d+)\)\.1$', e)
    if m:
        assert unsub(m.group(1)) == j
        passes.append(('subMulW', j, (unsub(m.group(2)), int(m.group(3)))))
        continue
    m = re.match(r'\(subInto w(\S)\.toUSlice w(\S)\.toUSlice\)\.1$', e)
    assert m and unsub(m.group(1)) == j, e
    passes.append(('subW', j, unsub(m.group(2))))

def inverse(d): return pow(d, -1, 2 ** 64)

# Emit the definition and the proof steps.
cur = {j: (f'w{sub(j)}', f'hw{sub(j)}', f'hv{sub(j)}') for j in range(1, 10)}
vals = {j: val_w(j) for j in range(1, 10)}
code = []
proof = []
q = 0
for kind, j, p in passes:
    name, sh, vh = cur[j]
    q += 1
    qn, sn, en = f'q{sub(q)}', f's{sub(q)}', f'e{sub(q)}'
    if kind == 'subXd':
        new = add(vals[j], scale(XD, p), -1)
        if p == 1:
            code.append(f'  let w{sub(j)} := (subInto w{sub(j)}.toUSlice Xd).1')
            step = (f'subSl hL {name} {sh} Xd (by rw [xd₃]; exact hXd)\n      (R := {expr(new)}) '
                    f'{vh} xd₄ (by lia)')
            show = f'(subInto {name}.toUSlice Xd 0).1'
        else:
            code.append(f'  let w{sub(j)} := (subMulInto w{sub(j)}.toUSlice Xd {p}).1')
            step = (f'subMulSl hL {name} {sh} Xd (by rw [xd₃]; exact hXd) {p}\n      '
                    f'(R := {expr(new)}) {vh} xd₄ rfl (by lia)')
            show = f'(subMulInto {name}.toUSlice Xd {p}).1'
    elif kind == 'subX0':
        new = add(vals[j], X0, -1)
        code.append(f'  let w{sub(j)} := (subInto w{sub(j)}.toUSlice X₀).1')
        step = (f'subSl hL {name} {sh} X₀ (by rw [x₀₃]; exact hX₀)\n      (R := {expr(new)}) '
                f'{vh} x₀₄ (by lia)')
        show = f'(subInto {name}.toUSlice X₀ 0).1'
    elif kind == 'subW':
        bn, bs, bv = cur[p]
        new = add(vals[j], vals[p], -1)
        code.append(f'  let w{sub(j)} := (subInto w{sub(j)}.toUSlice w{sub(p)}.toUSlice).1')
        step = f'subW hL {name} {bn} {sh} {bs}\n      (R := {expr(new)}) {vh} {bv} (by lia)'
        show = f'(subInto {name}.toUSlice {bn}.toUSlice 0).1'
    elif kind == 'subMulW':
        b, m = p
        bn, bs, bv = cur[b]
        new = add(vals[j], scale(vals[b], m), -1)
        code.append(f'  let w{sub(j)} := (subMulInto w{sub(j)}.toUSlice w{sub(b)}.toUSlice {m}).1')
        step = (f'subMulW hL {name} {bn} {sh} {bs} {m}\n      (R := {expr(new)}) {vh} {bv} rfl '
                f'(by lia)')
        show = f'(subMulInto {name}.toUSlice {bn}.toUSlice {m}).1'
    elif kind == 'div':
        new = scale(vals[j], Fraction(1, p))
        dinv = inverse(p)
        code.append(f'  let w{sub(j)} := (divExactInto w{sub(j)}.toUSlice {p} {dinv}).1')
        step = (f'divW hL {name} {sh} {p} {dinv} (by decide) (by decide) rfl\n      '
                f'(R := {expr(new)}) {vh} (by lia)')
        show = f'(divExactInto {name}.toUSlice {p} {dinv}).1'
    elif kind == 'shr':
        new = scale(vals[j], Fraction(1, 2 ** p))
        code.append(f'  let w{sub(j)} := rshiftInto w{sub(j)}.toUSlice {p}')
        step = (f'shrW hL {name} {sh} {p} (by decide) (by decide)\n      (R := {expr(new)}) rfl '
                f'{vh} (by lia)')
        show = f'(rshiftInto {name}.toUSlice {p})'
    check(new, (kind, j, p))
    vals[j] = new
    cur[j] = (qn, sn, en)
    proof.append(f'  obtain ⟨{sn}, {en}⟩ := {step}')
    proof.append(f'  rw [← (show {qn} = {show} from rfl)] at {sn} {en}')
for j in range(1, 10):
    assert vals[j] == {j: 1}, (j, vals[j])
nq = q

# The definition: the header and the recombination of the old one, the new passes.
head = old_def[:old_def.index('  let w₁ :=')]
head = head.replace('''`c_10` from limb `r.start + 10 k` to `r.start + n`, with `w₁, …, w_9` the values at `1, …, 9`,
writes `c₀ + c₁ x + ⋯ + c_10 x^10` into the `n` limbs from `r.start`, `x = 2^(64 k)`. The values
`(w_j - c₀ - j^10 c_10) / j`, their divided differences and Horner's rule are all in place on the
    `w`.''', '''`c_10` from limb `r.start + 10 k` to `r.start + n`, with `w₁, …, w_9` the values at `1, …, 9`,
writes `c₀ + c₁ x + ⋯ + c_10 x^10` into the `n` limbs from `r.start`, `x = 2^(64 k)`. The values
`h(j) = w_j - j^10 c_10`, their forward differences, the Newton coefficients `Δˡ h(0) / l!` and
Horner's rule are all in place on the `w`: eight exact divisions, one for each coefficient, where
divided differences take one at every step. Generated by `scripts/toom6_interp.py`.''')
tail = old_def[old_def.index('  -- The recombination.'):]
new_def = head + '\n'.join(code) + '\n' + tail

# The theorem: the old head up to the first pass and the old tail with the final names renamed.
th_head = old_thm[:old_thm.index('  obtain ⟨s₁, e₁⟩')]
lets = ' '.join(f'q{sub(i)}' for i in range(1, nq + 1))
words = ('R X₀ Xd ' + lets).split()
lines, line = [], '  extract_lets'
for w in words:
    if len(line) + 1 + len(w) > 100:
        lines.append(line); line = '     '
    line += ' ' + w
lines.append(line)
lines.append('    A₀ A₁ A₂ A₃ A₄ A₅ A₆ A₇ A₈')
th_head = re.sub(r'  extract_lets .*?\n    A₀ A₁ A₂ A₃ A₄ A₅ A₆ A₇ A₈\n', '\n'.join(lines) + '\n', th_head,
                 flags=re.S)
th_tail = old_thm[old_thm.index('  -- The recombination'):]
remap = {}
for j in range(1, 10):
    o = old_final[j]
    nf = unsub(cur[j][0][1:])
    remap[o] = nf
def ren(m):
    kind, num = m.group(1), unsub(m.group(2))
    return kind + sub(remap[num]) if num in remap else m.group(0)
th_tail = re.sub(r'(?<![\w])([qse])([₀₁₂₃₄₅₆₇₈₉]+)(?![\w₀₁₂₃₄₅₆₇₈₉])', ren, th_tail)
def wrap(line, indent='      '):
    """Breaks a line of the proof before column 100, at a space, with a continuation indent."""
    out = []
    while len(line) > 100:
        cut = line.rfind(' ', 0, 100)
        out.append(line[:cut])
        line = indent + line[cut + 1:]
    out.append(line)
    return '\n'.join(out)
proof = [wrap(l) for chunk in proof for l in chunk.split('\n')]
new_thm = th_head + '\n'.join(proof) + '\n' + th_tail

open(path, 'w').write(src[:d0] + new_def + new_thm + src[t1:])
print(f'{nq} passes ({sum(1 for p in passes if p[0] in ("div", "shr"))} divisions and shifts)')
