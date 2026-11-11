#!/usr/bin/env python3
"""Generates MPN/Toom/Interp.lean: the interpolations of the Toom methods and their proofs.

usage: scripts/toom_interp.py > MPN/Toom/Interp.lean

Each interpolation of degree `D` takes `c₀` and `c_D` in their windows of the result and the
values `w_j = P(j)`, `j = 1, …, D - 1`, of `P = c₀ + c₁ x + ⋯ + c_D x^D`, and turns the `w_j` into
`c₁, …, c_{D-1}` in place by the passes of its schedule. The value of each array lives in a window,
from limb `0` or, after a halving by `shlTop`, from limb `1`. The script tracks every intermediate
value as a combination of the coefficients, checks that its multipliers are nonnegative integers,
and emits each pass as one step of the proof, checked by `lia`. Then the recombination clears the
middle of the result and adds each coefficient at its place.

Schedule passes: `j - S`, `j - m*S` (subtract from `w_j` the source `S`, times `m`), where `S` is
`X0` (`c₀`), `Xd` (`c_D`), `i` (the window of `w_i`) or `i.low` (the low `L - 1` limbs of `w_i`);
`j / q` (an exact division by an odd `q`); `j >> s` (a shift); `j half` (`shlTop`).
"""
import re
from fractions import Fraction
re_names = re.compile(r'q[₀₁₂₃₄₅₆₇₈₉]+')

SCHEDULES = {
    3: ("Toom-3 by 2", "1 - X0; 1 - Xd; 2 - X0; 2 - 8*Xd; 2 half; 2 - 1.low; 1 - 2"),
    4: ("Toom-3", "1 - X0; 1 - Xd; 2 - X0; 2 - 16*Xd; 2 half; 3 - X0; 3 - 81*Xd; 3 / 3; "
        "2 - 1.low; 3 - 1; 3 half; 3 - 2; 2 - 3*3; 1 - 2; 1 - 3"),
    5: ("Toom-4 by 3", "1 - X0; 1 - Xd; 2 - X0; 2 - 32*Xd; 2 >> 1; 3 - X0; 3 - 243*Xd; 3 / 3; "
        "4 - X0; 4 - 1024*Xd; 4 >> 2; 4 - 3; 3 - 2; 2 - 1; 4 - 3; 4 >> 1; 3 - 2; 3 >> 1; 4 - 3; "
        "4 / 3; 3 - 3*4; 2 - 2*3; 3 - 2*4; 1 - 2; 2 - 3; 3 - 4"),
    6: ("Toom-4", "1 - X0; 1 - Xd; 2 - X0; 2 - 64*Xd; 2 >> 1; 3 - X0; 3 - 729*Xd; 3 / 3; 4 - X0; "
        "4 - 4096*Xd; 4 >> 2; 5 - X0; 5 - 15625*Xd; 5 / 5; 5 - 4; 4 - 3; 3 - 2; 2 - 1; 5 - 4; "
        "5 >> 1; 4 - 3; 4 >> 1; 3 - 2; 3 >> 1; 5 - 4; 5 / 3; 4 - 3; 4 / 3; 5 - 4; 5 >> 2; "
        "4 - 4*5; 3 - 3*4; 4 - 3*5; 2 - 2*3; 3 - 2*4; 4 - 2*5; 1 - 2; 2 - 3; 3 - 4; 4 - 5"),
    10: ("Toom-6", "1 - Xd; 2 - 1024*Xd; 3 - 59049*Xd; 4 - 1048576*Xd; 5 - 9765625*Xd; "
         "6 - 60466176*Xd; 7 - 282475249*Xd; 8 - 1073741824*Xd; 9 - 3486784401*Xd; "
         "9 - 8; 8 - 7; 7 - 6; 6 - 5; 5 - 4; 4 - 3; 3 - 2; 2 - 1; 1 - X0; "
         "9 - 8; 8 - 7; 7 - 6; 6 - 5; 5 - 4; 4 - 3; 3 - 2; 2 - 1; "
         "9 - 8; 8 - 7; 7 - 6; 6 - 5; 5 - 4; 4 - 3; 3 - 2; 9 - 8; 8 - 7; 7 - 6; 6 - 5; 5 - 4; "
         "4 - 3; 9 - 8; 8 - 7; 7 - 6; 6 - 5; 5 - 4; 9 - 8; 8 - 7; 7 - 6; 6 - 5; 9 - 8; 8 - 7; "
         "7 - 6; 9 - 8; 8 - 7; 9 - 8; 2 >> 1; 3 / 3; 3 >> 1; 4 / 3; 4 >> 3; 5 / 15; 5 >> 3; "
         "6 / 45; 6 >> 4; 7 / 315; 7 >> 4; 8 / 315; 8 >> 7; 9 / 2835; 9 >> 7; "
         "8 - 8*9; 7 - 7*8; 8 - 7*9; 6 - 6*7; 7 - 6*8; 8 - 6*9; 5 - 5*6; 6 - 5*7; 7 - 5*8; "
         "8 - 5*9; 4 - 4*5; 5 - 4*6; 6 - 4*7; 7 - 4*8; 8 - 4*9; 3 - 3*4; 4 - 3*5; 5 - 3*6; "
         "6 - 3*7; 7 - 3*8; 8 - 3*9; 2 - 2*3; 3 - 2*4; 4 - 2*5; 5 - 2*6; 6 - 2*7; 7 - 2*8; "
         "8 - 2*9; 1 - 2; 2 - 3; 3 - 4; 4 - 5; 5 - 6; 6 - 7; 7 - 8; 8 - 9"),
}
HEARTBEATS = {3: None, 4: None, 5: 1000000, 6: 1000000, 10: 8000000, 14: 8000000}


def newton_schedule(D):
    """The schedule of the falling factorials `x (x - 1) ⋯ (x - i + 1)`, which vanish at `0, …, i - 1`:
    differences level by level give `i!` times the coefficients in that basis, the divisions by the
    `i!` give them, and multiplying out the factors `x - i` from the top gives the coefficients in
    powers of `x`. The multipliers stay below `D`, and `c_D` is never subtracted with `D^D`."""
    p = []
    for l in range(1, D):
        for j in range(D - 1, l - 1, -1):
            p.append(f"{j} - {'X0' if j == 1 else j - 1}")
    for j in range(2, D):
        f = 1
        for i in range(2, j + 1):
            f *= i
        s = 0
        while f % 2 == 0:
            f //= 2
            s += 1
        if f > 1:
            p.append(f"{j} / {f}")
        if s:
            p.append(f"{j} >> {s}")
    for i in range(D - 1, 0, -1):
        for j in range(i, D):
            src = 'Xd' if j + 1 == D else str(j + 1)
            p.append(f"{j} - {src}" if i == 1 else f"{j} - {i}*{src}")
    return '; '.join(p)


SCHEDULES[14] = ("Toom-8", newton_schedule(14))

SUB = str.maketrans('0123456789', '₀₁₂₃₄₅₆₇₈₉')
def sub(n): return str(n).translate(SUB)

def addv(a, b, s=1):
    r = dict(a)
    for k, v in b.items():
        r[k] = r.get(k, 0) + s * v
    return {k: v for k, v in r.items() if v != 0}
def scale(a, s): return {k: v * s for k, v in a.items()}
def check(a, what):
    for v in a.values():
        assert v.denominator == 1 and v >= 0, (what, a)
def expr(a):
    terms = []
    for k in sorted(a):
        v = int(a[k])
        terms.append(f'c{sub(k)}' if v == 1 else f'{v} * c{sub(k)}')
    return ' + '.join(terms) if terms else '0'
def wrap(words, indent, first, width=100):
    lines, line = [], first
    for w in words:
        if len(line) + 1 + len(w) > width:
            lines.append(line)
            line = indent + w
        else:
            line += ' ' + w
    lines.append(line)
    return '\n'.join(lines)
def off(i): return 'k' if i == 1 else f'({i} * k)'
def offo(i): return 'k' if i == 1 else f'{i} * k'
def pw(i): return f'2 ^ (LA.w * {off(i)})'
def total(D):
    return ' + '.join(['c₀'] + [f'{pw(i)} * c{sub(i)}' for i in range(1, D + 1)])
def win(o): return ('0', 'L') if o == 0 else ('1', '(L - 1)')

def gen(D):
    title, sched = SCHEDULES[D]
    passes = [p.strip() for p in sched.split(';')]
    ws = list(range(1, D))
    # Per array: current name, size hypothesis, value hypothesis, window offset, value.
    cur = {j: [f'w{sub(j)}', f'hw{sub(j)}', f'hv{sub(j)}', 0,
               {m: Fraction(j ** m) for m in range(D + 1)}] for j in ws}
    top = {m: Fraction((D - 1) ** m) for m in range(D + 1)}
    needs_hb = any(('half' in p) or ('.low' in p) for p in passes)
    code, proof, names = [], [], []
    wname = {f'w{sub(j)}': f'w{sub(j)}' for j in ws}
    q = 0
    for p in passes:
        q += 1
        qn, sn, en = f'q{sub(q)}', f's{sub(q)}', f'e{sub(q)}'
        names.append(qn)
        toks = p.split()
        j = int(toks[0])
        name, sh, vh, o, val = cur[j]
        do, dl = win(o)
        h = f'(by rw [{sh}]; lia)'
        if toks[1] == '-':
            s = toks[2]
            m = 1
            if '*' in s:
                ms, s = s.split('*')
                m = int(ms)
            if s == 'X0':
                sa, so, sl, hs, sv = 'd', 'o', '(k + k)', 'hc₀', {0: Fraction(1)}
            elif s == 'Xd':
                sa, so, sl, hs, sv = 'd', f'(o + {offo(D)})', f'(n - {offo(D)})', f'hc{sub(D)}', \
                    {D: Fraction(1)}
            elif s.endswith('.low'):
                i = int(s[:-4])
                iname, _, ivh, io, ival = cur[i]
                assert io == 0
                for k, v in ival.items():
                    assert v <= top.get(k, 0)
                sa, so, sl, sv = iname, '0', '(L - 1)', ival
                hs = f'l{sub(q)}'
                proof.append(f'  have {hs} := low_val (by lia) {ivh} (by lia)')
            else:
                i = int(s)
                iname, _, ivh, io, ival = cur[i]
                sa, (so, sl), hs, sv = iname, win(io), ivh, ival
            new = addv(val, scale(sv, m), -1)
            if m == 1:
                call = f'R.subInto {name} {do} {dl} {sa} {so} {sl}'
                step = f'sub_val (q := {name}) (o := {do}) (len := {dl}) {h} {sa} {so} {sl}'
                step += f'\n      (V := {expr(new)}) {vh} {hs} (by lia)'
            else:
                call = f'R.subMulInto {name} {do} {dl} {sa} {so} {sl} {m}'
                step = (f'subMul_val (q := {name}) (o := {do}) (len := {dl}) {h} {sa} {so} {sl} '
                        f'{m} (by decide)\n      (V := {expr(new)}) {vh} {hs} (by lia)')
        elif toks[1] == '/':
            d = int(toks[2])
            new = scale(val, Fraction(1, d))
            call = f'R.divExact {name} {do} {dl} {d}'
            step = (f'div_val (q := {name}) (o := {do}) (len := {dl}) {h} {d} (by decide) '
                    f'(by decide)\n      (V := {expr(new)}) {vh} (by lia)')
        elif toks[1] == '>>':
            s = int(toks[2])
            new = scale(val, Fraction(1, 2 ** s))
            call = f'R.shr {name} {do} {dl} {s}'
            step = (f'shr_val (q := {name}) (o := {do}) (len := {dl}) {h} {s} (by decide) '
                    f'(by decide)\n      (V := {expr(new)}) {vh} (by lia)')
        elif toks[1] == 'half':
            assert o == 0
            for k, v in val.items():
                assert v <= top.get(k, 0)
            new = scale(val, Fraction(1, 2))
            call = f'R.shlTop {name} 0 L'
            step = (f'half_val (q := {name}) (len := L) {h} (by lia)\n      (V := {expr(new)}) '
                    f'{vh} (by lia) (by lia)')
            o = 1
        else:
            raise ValueError(p)
        check(new, p)
        dcall = call
        for t in sorted(set(re_names.findall(call)), key=len, reverse=True):
            dcall = re.sub(rf'\b{t}\b', wname[t], dcall)
        code.append(f'  let w{sub(j)} := {dcall}')
        wname[qn] = f'w{sub(j)}'
        proof.append(f'  obtain ⟨{sn}, {en}⟩ := {step}')
        proof.append(f'  rw [← (show {qn} = {call} from rfl)] at {sn} {en}')
        proof.append(f'  rw [{sh}] at {sn}')
        cur[j] = [qn, sn, en, o, new]
    for j in ws:
        assert cur[j][4] == {j: 1}, (D, j, cur[j][4])
    # The recombination.
    rec = [f'  let d := R.zeroInto d (o + (k + k)) ({offo(D)} - (k + k))']
    for i in ws:
        name, _, _, o, _ = cur[i]
        so, sl = win(o)
        line = f'R.addInto d (o + {off(i)}) (n - {off(i)}) w{sub(i)} {so} (min (n - {off(i)}) {sl})'
        rec.append(f'  let d := {line}' if i < D - 1 else f'  {line}')
    rnames = [f'A{sub(i)}' for i in range(D - 1)]
    gens = '\n'.join(f'    generalize {pw(i)} * c{sub(i)} = T{sub(i)} at htot ⊢'
                     for i in range(1, D + 1))
    rproof = []
    rproof.append(f'  obtain ⟨z₁, z₂⟩ := zero_mid d o n (k + k) ({offo(D)}) hd (by lia) (by lia)')
    rproof.append(f'  rw [hc₀, hc{sub(D)}] at z₂')
    rproof.append(f'  rw [← (show A₀ = R.zeroInto d (o + (k + k)) ({offo(D)} - (k + k)) from rfl)]'
                  ' at z₁ z₂')
    prev, prevw, prevv = 'A₀', 'z₁', 'z₂'
    chain = []
    for i in ws:
        name, _, ve, o, _ = cur[i]
        so, sl = win(o)
        tgt = f'A{sub(i)}' if i < D - 1 else None
        aw, av = f'a{sub(i)}w', f'a{sub(i)}v'
        rproof.append(f'  obtain ⟨{aw}, {av}⟩ := add_coef {prev} o n {off(i)} '
                      f'(by rw [{prevw}.1]; exact hd) (by lia)\n      {name} {so} {sl} c{sub(i)} '
                      f'{ve} (by\n    rw [{prevv}]\n{gens}\n    lia)')
        rproof.append(f'  rw [{prevv}] at {av}')
        if tgt:
            rproof.append(f'  rw [← (show {tgt} = R.addInto {prev} (o + {off(i)}) (n - {off(i)}) '
                          f'{name} {so} (min (n - {off(i)}) {sl}) from rfl)] at {aw} {av}')
            rproof.append(f'  have {aw}' + "' := " + f'{aw}.mono (o\' := o) (len\' := n) (by lia) (by lia) |>.trans '
                          f'{prevw}')
            prev, prevw, prevv = tgt, f"{aw}'", av
        else:
            rproof.append(f'  refine ⟨({aw}.mono (o\' := o) (len\' := n) (by lia) (by lia)).trans '
                          f'{prevw}, ?_⟩')
            rproof.append(f'  rw [{av}]')
            rproof.append(gens.replace('    generalize', '  generalize'))
            rproof.append('  lia')
    # The zero step's writes, within the window of the result.
    rproof.insert(3, "  replace z₁ := z₁.mono (o' := o) (len' := n) (by lia) (by lia)")
    wsig = ' '.join(f'w{sub(j)}' for j in ws)
    cs = ' '.join(f'c{sub(i)}' for i in range(D + 1))
    hws = ' '.join(f'(hw{sub(j)} : LA.size w{sub(j)} = L)' for j in ws)
    hvs = []
    for j in ws:
        e = expr({m: Fraction(j ** m) for m in range(D + 1)})
        hvs.append(wrap(f'(hv{sub(j)} : valAt w{sub(j)} 0 L = {e})'.split(' '), '        ', '   '))
    out = []
    points = ', '.join(str(i) for i in range(D)) + ', ∞'
    out.append(f'''/--
The interpolation of degree {D} at `{points}`, of {title}: from `c₀` in the `2 k` limbs of `d`
from `o` and `c_{D}` from limb `o + {D} k` to `o + n`, with `w₁, …, w_{D - 1}` the values at
`1, …, {D - 1}` in `L` limbs each, writes `c₀ + c₁ x + ⋯ + c_{D} x^{D}` into the `n` limbs from `o`,
`x = 2^(w k)`.
-/
@[expose, specialize] public def interp{D} (d : A) (o n k L : Nat) ({wsig} : A) : A :=''')
    out.append('\n'.join(code))
    out.append('  -- The recombination.')
    out.append('\n'.join(rec))
    out.append('')
    if HEARTBEATS[D]:
        out.append(f'set_option maxHeartbeats {HEARTBEATS[D]} in')
    hb = (f'\n    (hb : {expr(top)} < 2 ^ (LA.w * (L - 1)))' if needs_hb else '')
    stmt = f'interp{D} d o n k L {wsig}'
    out.append(f'''public theorem interp{D}_spec (d : A) (o n k L : Nat) ({wsig} : A) ({cs} : Nat)
    (hd : o + n ≤ LA.size d) (hk : {offo(D)} ≤ n) ({'' if needs_hb else '_'}hL : 2 ≤ L)
{wrap(hws.replace(') (', ')|(').split('|'), '    ', '   ')}
    (hc₀ : valAt d o (k + k) = c₀) (hc{sub(D)} : valAt d (o + {offo(D)}) (n - {offo(D)}) = c{sub(D)})
''' + '\n'.join(hvs) + hb + f'''
{wrap(f'(htot : {total(D)} < 2 ^ (LA.w * n)) :'.split(' '), '        ', '   ')}
    Writes ({stmt}) d o n ∧
{wrap(f'valAt ({stmt}) o n = {total(D)} := by'.split(' '), '          ', '     ')}
  unfold interp{D}
{wrap(names + rnames, '     ', '  extract_lets')}''')
    out.append('\n'.join(proof))
    out.append('  -- The recombination.')
    out.append('\n'.join(rproof))
    out.append('')
    return '\n'.join(out)

def base(j): return '0' if j == 1 else ('L' if j == 2 else f'{j - 1} * L')
def at(j, o):
    b = base(j)
    if o == 0: return b if b in ('0', 'L') else f'({b})'
    return '1' if b == '0' else f'({b} + 1)'
def ln(o): return 'L' if o == 0 else '(L - 1)'

# The one-array interpolations whose first stage is fused into one pass of `sub3Lin`.
FUSE = {4}

def first_pass(p):
    toks = p.split()
    return toks[1] == '-' and (toks[2] == 'X0' or toks[2].endswith('Xd'))

def fuse_first(passes, ws):
    """The multipliers `m` of the passes `j - X0` and `j - m*Xd` of the three windows, when these
    are the first passes on each window: they read `d`, not the other windows, so that they run
    first and together."""
    if len(ws) != 3:
        return None
    ms, done = {}, set()
    for p in passes:
        toks = p.split()
        j = int(toks[0])
        if first_pass(p):
            assert j not in done, p
            if toks[2] != 'X0':
                ms[j] = int(toks[2].split('*')[0]) if '*' in toks[2] else 1
        else:
            done.add(j)
    assert sorted(ms) == ws
    assert all(sum(1 for p in passes if first_pass(p) and int(p.split()[0]) == j) == 2 for j in ws)
    return ms

def genW(D):
    """`interp{D}` on one array `W`, the value at `j` in the window of `L` limbs at `(j - 1) L`: the
    same passes, a window of `W` minus another by `subMulWin`, and in the proof the values of the
    windows not written carried over each pass."""
    title, sched = SCHEDULES[D]
    passes = [p.strip() for p in sched.split(';')]
    ws = list(range(1, D))
    st = {j: [0, f'hv{sub(j)}', {m: Fraction(j ** m) for m in range(D + 1)}] for j in ws}
    top = {m: Fraction((D - 1) ** m) for m in range(D + 1)}
    needs_hb = any(('half' in p) or ('.low' in p) for p in passes)
    ms = fuse_first(passes, ws) if D in FUSE else None
    if ms:
        passes = ['fuse'] + [p for p in passes if not first_pass(p)]
    code, proof, names = [], [], []
    curW, sz = 'W', 'hW'
    q = 0
    for p in passes:
        q += 1
        qn = f'q{sub(q)}'
        names.append(qn)
        if p == 'fuse':
            # The first stage in one pass: each window minus `X0 + m Xd`, by `sub3Lin`.
            new = {}
            for j in ws:
                assert st[j][0] == 0
                new[j] = addv(addv(st[j][2], {0: Fraction(1)}, -1), {D: Fraction(ms[j])}, -1)
                check(new[j], p)
            m1, m2, m3 = (ms[j] for j in ws)
            src = f'd o (k + k) (o + {offo(D)}) (n - {offo(D)}) {m1} {m2} {m3}'
            call = f'R.sub3Lin {curW} {at(1, 0)} {at(2, 0)} {at(3, 0)} L {src}'
            vs = ' '.join(f'(V{sub(i + 1)} := {expr(new[j])})' for i, j in enumerate(ws))
            hvs_ = ' '.join(st[j][1] for j in ws)
            wn, sn = f'w{sub(q)}', f's{sub(q)}'
            ens = [f'e{sub(q)}{"abc"[i]}' for i in range(3)]
            proof.append(f'  obtain ⟨{wn}, {", ".join(ens)}⟩ := sub3W_val (q := {curW}) '
                         f'(o₁ := {at(1, 0)}) (o₂ := {at(2, 0)})\n      (o₃ := {at(3, 0)}) '
                         f'(len := L) (by rw [{sz}]; lia) (by lia) (by lia)\n      {src}\n      {vs}\n'
                         f'      {hvs_} hc₀ hc{sub(D)} (by lia) (by lia) (by lia)')
            proof.append(f'  rw [← (show {qn} = {call} from rfl)] at {wn} {" ".join(ens)}')
            proof.append(f'  have {sn} := {wn}.1.trans {sz}')
            for i, j in enumerate(ws):
                st[j] = [0, ens[i], new[j]]
            code.append('  let W := ' + re.sub(rf'\b{curW}\b', 'W', call))
            curW, sz = qn, sn
            continue
        toks = p.split()
        j = int(toks[0])
        o, vh, val = st[j]
        do, dl = at(j, o), ln(o)
        h = f'(by rw [{sz}]; lia)'
        no = o
        pre = []
        if toks[1] == '-':
            src = toks[2]
            m = 1
            if '*' in src:
                ms, src = src.split('*')
                m = int(ms)
            if src in ('X0', 'Xd'):
                if src == 'X0':
                    so, sl, hs, sv = 'o', '(k + k)', 'hc₀', {0: Fraction(1)}
                else:
                    so, sl, hs, sv = f'(o + {offo(D)})', f'(n - {offo(D)})', f'hc{sub(D)}', \
                        {D: Fraction(1)}
                new = addv(val, scale(sv, m), -1)
                if m == 1:
                    call = f'R.subInto {curW} {do} {dl} d {so} {sl}'
                    step = (f'subW_val (q := {curW}) (o := {do}) (len := {dl}) {h} d {so} {sl}'
                            f'\n      (V := {expr(new)}) {vh} {hs} (by lia)')
                else:
                    call = f'R.subMulInto {curW} {do} {dl} d {so} {sl} {m}'
                    step = (f'subMulW_val (q := {curW}) (o := {do}) (len := {dl}) {h} d {so} {sl} '
                            f'{m} (by decide)\n      (V := {expr(new)}) {vh} {hs} (by lia)')
            else:
                low = src.endswith('.low')
                i = int(src[:-4] if low else src)
                io, ivh, ival = st[i]
                if low:
                    assert io == 0
                    for k, v in ival.items():
                        assert v <= top.get(k, 0)
                    so, sl, hs = at(i, 0), '(L - 1)', f'l{sub(q)}'
                    pre.append(f'  have {hs} := lowW_val (b := {at(i, 0)}) (by lia) {ivh} (by lia)')
                else:
                    so, sl, hs = at(i, io), ln(io), ivh
                assert not (o == 1 and sl == 'L'), p
                new = addv(val, scale(ival, m), -1)
                call = f'R.subMulWin {curW} {do} {dl} {so} {sl} {m}'
                step = (f'subMulWin_val (q := {curW}) (o := {do}) (len := {dl}) {h} {so} {sl} {m}'
                        f'\n      (by rw [{sz}]; lia) (by lia) (by lia) (by decide)'
                        f'\n      (V := {expr(new)}) {vh} {hs} (by lia)')
        elif toks[1] == '/':
            dv = int(toks[2])
            new = scale(val, Fraction(1, dv))
            call = f'R.divExact {curW} {do} {dl} {dv}'
            step = (f'divW_val (q := {curW}) (o := {do}) (len := {dl}) {h} {dv} (by decide) '
                    f'(by decide)\n      (V := {expr(new)}) {vh} (by lia)')
        elif toks[1] == '>>':
            sh = int(toks[2])
            new = scale(val, Fraction(1, 2 ** sh))
            call = f'R.shr {curW} {do} {dl} {sh}'
            step = (f'shrW_val (q := {curW}) (o := {do}) (len := {dl}) {h} {sh} (by decide) '
                    f'(by decide)\n      (V := {expr(new)}) {vh} (by lia)')
        elif toks[1] == 'half':
            assert o == 0
            for k, v in val.items():
                assert v <= top.get(k, 0)
            new = scale(val, Fraction(1, 2))
            call = f'R.shlTop {curW} {do} L'
            step = (f'halfW_val (q := {curW}) (b := {do}) (len := L) {h} (by lia)\n'
                    f'      (V := {expr(new)}) {vh} (by lia) (by lia)')
            no = 1
        else:
            raise ValueError(p)
        check(new, p)
        code.append('  let W := ' + re.sub(rf'\b{curW}\b', 'W', call))
        wn, en, sn = f'w{sub(q)}', f'e{sub(q)}', f's{sub(q)}'
        proof.extend(pre)
        proof.append(f'  obtain ⟨{wn}, {en}⟩ := {step}')
        proof.append(f'  rw [← (show {qn} = {call} from rfl)] at {wn} {en}')
        proof.append(f'  have {sn} := {wn}.1.trans {sz}')
        for i in ws:
            if i == j:
                continue
            io, ivh, ival = st[i]
            nv = f'v{sub(i)}q{sub(q)}'
            proof.append(f'  have {nv} := ({wn}.valAt_eq (lo := {at(i, io)}) (n := {ln(io)}) '
                         f'(by lia)).trans {ivh}')
            st[i][1] = nv
        st[j] = [no, en, new]
        curW, sz = qn, sn
    for j in ws:
        assert st[j][2] == {j: 1}, (D, j, st[j][2])
    rec = [f'  let d := R.zeroInto d (o + (k + k)) ({offo(D)} - (k + k))']
    for i in ws:
        o = st[i][0]
        line = (f'R.addInto d (o + {off(i)}) (n - {off(i)}) W {at(i, o)} '
                f'(min (n - {off(i)}) {ln(o)})')
        rec.append(f'  let d := {line}' if i < D - 1 else f'  {line}')
    rnames = [f'A{sub(i)}' for i in range(D - 1)]
    gens = '\n'.join(f'    generalize {pw(i)} * c{sub(i)} = T{sub(i)} at htot ⊢'
                     for i in range(1, D + 1))
    rproof = []
    rproof.append(f'  obtain ⟨z₁, z₂⟩ := zero_mid d o n (k + k) ({offo(D)}) hd (by lia) (by lia)')
    rproof.append(f'  rw [hc₀, hc{sub(D)}] at z₂')
    rproof.append(f'  rw [← (show A₀ = R.zeroInto d (o + (k + k)) ({offo(D)} - (k + k)) from rfl)]'
                  ' at z₁ z₂')
    rproof.append("  replace z₁ := z₁.mono (o' := o) (len' := n) (by lia) (by lia)")
    prev, prevw, prevv = 'A₀', 'z₁', 'z₂'
    for i in ws:
        o, ve, _ = st[i]
        so, sl = at(i, o), ln(o)
        tgt = f'A{sub(i)}' if i < D - 1 else None
        aw, av = f'a{sub(i)}w', f'a{sub(i)}v'
        rproof.append(f'  obtain ⟨{aw}, {av}⟩ := add_coef {prev} o n {off(i)} '
                      f'(by rw [{prevw}.1]; exact hd) (by lia)\n      {curW} {so} {sl} c{sub(i)} '
                      f'{ve} (by\n    rw [{prevv}]\n{gens}\n    lia)')
        rproof.append(f'  rw [{prevv}] at {av}')
        if tgt:
            rproof.append(f'  rw [← (show {tgt} = R.addInto {prev} (o + {off(i)}) (n - {off(i)}) '
                          f'{curW} {so} (min (n - {off(i)}) {sl}) from rfl)] at {aw} {av}')
            rproof.append(f"  have {aw}' := {aw}.mono (o' := o) (len' := n) (by lia) (by lia) "
                          f'|>.trans {prevw}')
            prev, prevw, prevv = tgt, f"{aw}'", av
        else:
            rproof.append(f"  refine ⟨({aw}.mono (o' := o) (len' := n) (by lia) (by lia)).trans "
                          f'{prevw}, ?_⟩')
            rproof.append(f'  rw [{av}]')
            rproof.append(gens.replace('    generalize', '  generalize'))
            rproof.append('  lia')
    cs = ' '.join(f'c{sub(i)}' for i in range(D + 1))
    hvs = []
    for j in ws:
        e = expr({m: Fraction(j ** m) for m in range(D + 1)})
        hvs.append(wrap(f'(hv{sub(j)} : valAt W {at(j, 0)} L = {e})'.split(' '), '        ', '   '))
    out = []
    out.append(f'/--\n`interp{D}` on one array: the values at `1, …, {D - 1}` in the windows of `L` '
               f'limbs of `W`\nat `0, L, …, {D - 2} L`, and the passes between two of them by '
               f'`subMulWin`.\n-/\n@[expose, specialize] public def interp{D}W (d : A) (o n k L : Nat) '
               f'(W : A) : A :=')
    out.append('\n'.join(code))
    out.append('  -- The recombination.')
    out.append('\n'.join(rec))
    out.append('')
    if HEARTBEATS[D]:
        out.append(f'set_option maxHeartbeats {HEARTBEATS[D]} in')
    hb = (f'\n    (hb : {expr(top)} < 2 ^ (LA.w * (L - 1)))' if needs_hb else '')
    stmt = f'interp{D}W d o n k L W'
    hl = '' if needs_hb else '_'
    head = (f'public theorem interp{D}W_spec (d : A) (o n k L : Nat) (W : A) ({cs} : Nat)\n'
            f'    (hd : o + n ≤ LA.size d) (hk : {offo(D)} ≤ n) ({hl}hL : 2 ≤ L)\n'
            f'    (hW : LA.size W = {D - 1} * L)\n'
            f'    (hc₀ : valAt d o (k + k) = c₀) (hc{sub(D)} : valAt d (o + {offo(D)}) '
            f'(n - {offo(D)}) = c{sub(D)})\n')
    head += '\n'.join(hvs) + hb + '\n'
    head += wrap(f'(htot : {total(D)} < 2 ^ (LA.w * n)) :'.split(' '), '        ', '   ') + '\n'
    head += f'    Writes ({stmt}) d o n ∧\n'
    head += wrap(f'valAt ({stmt}) o n = {total(D)} := by'.split(' '), '          ', '     ') + '\n'
    head += f'  unfold interp{D}W\n'
    head += wrap(names + rnames, '     ', '  extract_lets')
    out.append(head)
    out.append('\n'.join(proof))
    out.append('  -- The recombination.')
    out.append('\n'.join(rproof))
    out.append('')
    return '\n'.join(out)

HEADER = '''/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import MPN.Toom.Steps

/-!
# The interpolations of the Toom methods

Generated by `scripts/toom_interp.py`; do not edit. Each interpolation of degree `D` takes `c₀`
and `c_D`, the products of the low pieces and of the top pieces, in their windows of the result,
and the values `w_j` of the product at the points `j = 1, …, D - 1` in arrays of `L` limbs, turns
the `w_j` into the coefficients `c_j` in place, and adds them into the result. The points are
natural numbers, so every intermediate value is a natural number: each subtraction takes away a
part of the value it subtracts from, and each division is exact.
-/

namespace MPN.Toom

open LimbArray

variable {A L : Type} [LA : LimbArray A L] [R : ToomOps A L]
'''

if __name__ == '__main__':
    print(HEADER)
    for D in (3, 4, 5, 6, 10, 14):
        print(gen(D))
    for D in (4,):
        print(genW(D))
    print('end MPN.Toom')
