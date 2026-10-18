"""Generate the interpolation of Toom-(d/2+1) with natural points 0..d-1, ∞ (degree d) as Lean:
a definition with lets and a proof by step lemmas, each step checked by lia."""
import sys
from fractions import Fraction

d = int(sys.argv[1])          # degree, 10 for Toom-6
name = sys.argv[2]            # e.g. toom6Interp
SUB = '₀₁₂₃₄₅₆₇₈₉'
def sub(n): return ''.join(SUB[int(c)] for c in str(n))
C = [f'C{sub(i)}' for i in range(d + 1)]
npts = d - 1                  # points 1..d-1
unk = list(range(1, d))       # unknowns C1..C(d-1)

def expr(vec):
    """vec: dict i -> int coefficient of C_i."""
    parts = []
    for i in sorted(vec):
        c = vec[i]
        if c == 0: continue
        assert c > 0 and c == int(c), (vec)
        c = int(c)
        parts.append(C[i] if c == 1 else f'{c} * {C[i]}')
    return ' + '.join(parts) if parts else '0'

def lin(a, b, ca=1, cb=1):  # ca*a + cb*b
    out = {}
    for k in set(a) | set(b):
        out[k] = ca * a.get(k, 0) + cb * b.get(k, 0)
    return out

def div(a, l):
    out = {}
    for k, v in a.items():
        q = Fraction(v, l)
        assert q.denominator == 1, ('inexact', a, l)
        out[k] = int(q)
    return out

lets = []      # (name, lean term, kind, args)
proof = []
vals = {}

w = [None] + [f'w{sub(j)}' for j in range(1, npts + 1)]
# r_j
for j in range(1, npts + 1):
    v = {i: j ** (i - 1) for i in unk}
    nm = f'r{sub(j)}'
    if j == 1:
        term = f'subVal (subVal {w[j]} c₀) c{sub(d)}'
        full = lin(v, {d: 1})
        proof.append(f'  have h{nm} : toNat {nm} = {expr(v)} := toNat_sStep _ _ _ _ ({expr(v)})\n'
                     f'    (toNat_sStep _ _ _ _ ({expr(full)}) hw{sub(j)} h₀ (by lia)) h{sub(d)} (by lia)')
    else:
        jd = j ** d
        assert jd < 2 ** 32, ('multiplier', j, d)
        term = f'divExact{j} (subMulVal (subVal {w[j]} c₀) c{sub(d)} {jd})'
        proof.append(f'  have h{nm} : toNat {nm} = {expr(v)} := toNat_rStep {w[j]} c₀ c{sub(d)} {jd} divExact{j} {j} toNat_divExact{j}'
                     f' C₀ C{sub(d)}\n    ({expr(v)}) h₀ h{sub(d)}\n'
                     f'    (by rw [hw{sub(j)}]; simp only [UInt32.reduceToNat]; lia)')
    lets.append((nm, term)); vals[nm] = v
# divided differences
level = [f'r{sub(j)}' for j in range(1, npts + 1)]
nc = [level[0]]
for l in range(1, npts):
    nxt = []
    for i in range(len(level) - 1):
        a, b = level[i + 1], level[i]
        v = div(lin(vals[a], vals[b], 1, -1), l)
        nm = f'd{sub(l)}_{sub(i)}'
        if l == 1:
            term = f'subVal {a} {b}'
            proof.append(f'  have h{nm} : toNat {nm} = {expr(v)} := toNat_sStep {a} {b} _ _ ({expr(v)}) h{a} h{b} (by lia)')
        else:
            term = f'divExact{l} (subVal {a} {b})'
            proof.append(f'  have h{nm} : toNat {nm} = {expr(v)} := toNat_ddStep {a} {b} divExact{l} {l} toNat_divExact{l} _ _\n'
                         f'    ({expr(v)}) h{a} h{b} (by lia)')
        lets.append((nm, term)); vals[nm] = v
        nxt.append(nm)
    level = nxt
    nc.append(level[0])
# Horner: nodes x = i + 1 for i = top-1 .. 0
top = len(nc) - 1
q = [nc[top]]
for ii in range(top):
    i = top - 1 - ii
    x = i + 1
    newq = []
    srcs = [(nc[i], q[0])] + [(q[t - 1], q[t]) for t in range(1, len(q))]
    for t, (y, z) in enumerate(srcs):
        v = lin(vals[y], vals[z], 1, -x)
        nm = f'q{sub(i)}_{sub(t)}'
        if x == 1:
            term = f'subVal {y} {z}'
            proof.append(f'  have h{nm} : toNat {nm} = {expr(v)} := toNat_sStep {y} {z} _ _ ({expr(v)}) h{y} h{z} (by lia)')
        else:
            term = f'subMulVal {y} {z} {x}'
            proof.append(f'  have h{nm} : toNat {nm} = {expr(v)} := toNat_hStep {y} {z} {x} _ _ ({expr(v)}) h{y} h{z}\n'
                         f'    (by simp only [UInt32.reduceToNat]; lia)')
        lets.append((nm, term)); vals[nm] = v
        newq.append(nm)
    newq.append(q[-1])
    q = newq
for t, nm in enumerate(q):
    assert vals[nm] == {k: (1 if k == t + 1 else 0) for k in vals[nm]} or \
        {k: c for k, c in vals[nm].items() if c} == {t + 1: 1}, (nm, vals[nm])

ws = ' '.join(w[1:])
out = []
out.append(f'/--\nThe coefficients `c₀, …, c{sub(d)}` from `c₀`, `c{sub(d)}` and the values `w_j = c(j)`, '
           f'`j = 1, …, {npts}`:\nthe values `r_j`, their divided differences and Horner\'s rule '
           f'(generated).\n-/')
out.append(f'public def {name} (c₀ {ws} c{sub(d)} : UInt32Array) : List UInt32Array :=')
for nm, term in lets:
    out.append(f'  let {nm} := {term}')
out.append(f'  [c₀, {", ".join(q)}, c{sub(d)}]')
out.append('')
hyps = []
for j in range(1, npts + 1):
    terms = ' + '.join(['C₀'] + [(f'{j ** i} * {C[i]}' if j ** i != 1 else C[i]) for i in range(1, d + 1)])
    hyps.append(f'    (hw{sub(j)} : toNat {w[j]} = {terms})')
out.append(f'public theorem {name}_spec (c₀ {ws} c{sub(d)} : UInt32Array)\n'
           f'    ({" ".join(C)} : Nat) (h₀ : toNat c₀ = C₀) (h{sub(d)} : toNat c{sub(d)} = C{sub(d)})\n'
           + '\n'.join(hyps) + ' :\n'
           f'    ({name} c₀ {ws} c{sub(d)}).map (fun x : UInt32Array => toNat x) =\n'
           f'      [{", ".join(C)}] := by')
out.append(f'  unfold {name}')
names = [nm for nm, _ in lets]
chunks = []
line = '  extract_lets'
for nm in names:
    if len(line) + len(nm) + 1 > 98:
        chunks.append(line); line = '    ' + nm
    else:
        line += ' ' + nm
chunks.append(line)
out += chunks
out += proof
out.append(f'  simp only [List.map_cons, List.map_nil, h₀, h{sub(d)}, {", ".join("h" + nm for nm in q)}]')
def wrap(text):
    res = []
    for l in text.split('\n'):
        while len(l) > 100:
            ind = len(l) - len(l.lstrip())
            cut = max(l.rfind(' + ', 0, 97), l.rfind(' := ', 0, 97))
            if cut <= ind + 8:
                cut = l.rfind(' ', 0, 99)
            if l[cut:cut + 4] == ' := ':
                res.append(l[:cut + 3]); l = ' ' * (ind + 4) + l[cut + 4:]
            elif l[cut:cut + 3] == ' + ':
                res.append(l[:cut] + ' +'); l = ' ' * (ind + 4) + l[cut + 3:]
            else:
                res.append(l[:cut]); l = ' ' * (ind + 4) + l[cut + 1:]
        res.append(l)
    return '\n'.join(res)
print(wrap('\n'.join(out)))
