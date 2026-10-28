#!/usr/bin/env python3
"""Generates MPN/Toom/Methods.lean: the Toom methods and their proofs.

usage: scripts/toom_methods.py > MPN/Toom/Methods.lean

A method splits `a` into `p` pieces of `k` limbs and `b` into `q` (or squares `a`), writes the
product of the low pieces and the product of the top pieces into the window of the result, the
products of the values at `1, …, D - 1`, `D = p + q - 2`, into new arrays of `2 k + 2` limbs, and
interpolates with `interpD` of `MPN.Toom.Interp`. The proof names the pieces, expands the values
as polynomials in them, and checks the identities of the coefficients with `grind`.
"""

SUB = str.maketrans('0123456789', '₀₁₂₃₄₅₆₇₈₉')
def sub(n): return str(n).translate(SUB)
def mk(i): return 'k' if i == 1 else f'{i} * k'
def pmk(i): return 'k' if i == 1 else f'({i} * k)'
def Xp(i): return ' * '.join(['X'] * i)

MUL = [('toom33', 'Toom-3', 3, 3), ('toom42', 'Toom-4 by 2', 4, 2), ('toom32', 'Toom-3 by 2', 3, 2),
       ('toom44', 'Toom-4', 4, 4), ('toom43', 'Toom-4 by 3', 4, 3), ('toom66', 'Toom-6', 6, 6)]
SQR = [('toom3Sqr', 'The Toom-3 square', 3), ('toom4Sqr', 'The Toom-4 square', 4),
       ('toom6Sqr', 'The Toom-6 square', 6)]
HEART = {4: None, 3: None, 5: 2000000, 6: 2000000, 10: 8000000}

def coeffs(p, q, sym_a='A', sym_b='B'):
    cs = []
    for m in range(p + q - 1):
        ts = [f'{sym_a}{sub(i)} * {sym_b}{sub(m - i)}' for i in range(p) if 0 <= m - i < q]
        cs.append(' + '.join(ts))
    return cs

def evalexpr(sym, n, j):
    ts = [f'{sym}₀'] + [f'{sym}{sub(i)} * {j}' if i == 1 else f'{sym}{sub(i)} * {j} ^ {i}'
                        for i in range(1, n)]
    return ' + '.join(ts)

def method(name, title, p, q, square):
    D = p + q - 2
    n = 'al + al' if square else 'al + bl'
    out = []
    shape = f'Shape{name[4:]}' if not square else f'Shape{p}S'
    nh = 3 if square else 5
    pat = '⟨' + ', '.join(['_'] * nh) + '⟩'
    if square:
        out.append(f'''/-- The shape of {title.lower()}: {p} pieces of `k` limbs, at most, the top one nonempty. -/
public abbrev {shape} (al k : Nat) : Prop :=
  1 ≤ k ∧ {mk(p - 1)} < al ∧ al ≤ {mk(p)}
''')
    else:
        last = 'bl ≤ al' if p == q else f'bl ≤ {mk(q)}'
        out.append(f'''/--
The shape of {title}: {p} pieces of `k` limbs of `a` and {q} of `b`, at most, the top ones
nonempty.
-/
public abbrev {shape} (al bl k : Nat) : Prop :=
  1 ≤ k ∧ {mk(p - 1)} < al ∧ al ≤ {mk(p)} ∧ {mk(q - 1)} < bl ∧ {last}
''')
    ws = ' '.join(f'(w {j})' for j in range(1, D))
    if square:
        out.append(f'''/-- {title}: `a` in {p} pieces of `k` limbs, at most, the top one nonempty. -/
@[expose, specialize] public def {name} (d : A) (o : Nat) (a : A) (ao al k : Nat)
    (hk : {shape} al k) (sq : SqrFn A al) : A :=
  let d := sq d o a ao k (by obtain {pat} := hk; lia)
  let d := sq d (o + {mk(D)}) a (ao + {mk(p - 1)}) (al - {mk(p - 1)}) (by obtain {pat} := hk; lia)
  let w (j : Nat) := sq (R.zeros (k + k + 2)) 0 (evalAt a ao al k {p} j (k + 1)) 0 (k + 1)
    (by obtain {pat} := hk; lia)
  interp{D} d o ({n}) k (k + k + 2) {ws}
''')
    else:
        out.append(f'''/-- {title}: `a` in {p} pieces of `k` limbs and `b` in {q}, at most, the top ones nonempty. -/
@[expose, specialize] public def {name} (d : A) (o : Nat) (a : A) (ao al : Nat) (b : A)
    (bo bl k : Nat) (hk : {shape} al bl k) (mul : MulFn A (al + bl)) : A :=
  let d := mul d o a ao k b bo k (by obtain {pat} := hk; lia)
  let d := mul d (o + {mk(D)}) a (ao + {mk(p - 1)}) (al - {mk(p - 1)}) b (bo + {mk(q - 1)})
    (bl - {mk(q - 1)}) (by obtain {pat} := hk; lia)
  let w (j : Nat) := mul (R.zeros (k + k + 2)) 0 (evalAt a ao al k {p} j (k + 1)) 0 (k + 1)
    (evalAt b bo bl k {q} j (k + 1)) 0 (k + 1) (by obtain {pat} := hk; lia)
  interp{D} d o ({n}) k (k + k + 2) {ws}
''')
    # The proof.
    B = 'A' if square else 'B'
    qq = p if square else q
    pr = []
    if HEART[D]:
        pr.append(f'set_option maxHeartbeats {HEART[D]} in')
    if square:
        pr.append(f'''public theorem {name}_spec (d : A) (o : Nat) (a : A) (ao al k : Nat) (hk : {shape} al k)
    (sq : SqrFn A al) (hsq : IsSqr sq) (hd : o + (al + al) ≤ LA.size d) :
    Writes ({name} d o a ao al k hk sq) d o (al + al) ∧
      valAt ({name} d o a ao al k hk sq) o (al + al) = valAt a ao al * valAt a ao al := by
  obtain ⟨hk₁, ha₁, ha₂⟩ := hk
  dsimp only [{name}]
  have hab := mul_lt a a ao al ao al
  have hA := valAt_eq_pieces a k {p} ao al (by lia)
  have pA (j : Nat) (hj : 1 ≤ j) := point_sqr_spec sq hsq a ao al k {p} j (by decide) hj
  simp only [sumRange_succ, sumRange_zero, Nat.zero_add, Nat.pow_zero, Nat.mul_one,
    Nat.pow_one] at hA pA
  have a₀ := piece_full a ao al k 0 (by lia)
  have aT := piece_top a ao al k {p - 1} (by lia)
  simp only [Nat.zero_mul, Nat.add_zero] at a₀ aT''')
        for i in range(p):
            pr.append(f'  have lA{sub(i)} := piece_lt a ao al k {i}')
        for i in range(p):
            pr.append(f'  generalize piece a ao al k {i} = A{sub(i)} at *')
        pr.append(f'''  -- The squares of the low piece and of the top piece.
  have p₁ : k < al := by lia
  obtain ⟨w₁, v₁⟩ := hsq d o a ao k p₁ (by lia)
  rw [← a₀] at v₁
  generalize sq d o a ao k p₁ = d₁ at *
  have p₂ : al - {mk(p - 1)} < al := by lia
  obtain ⟨w₂, v₂⟩ := hsq d₁ (o + {mk(D)}) a (ao + {mk(p - 1)}) (al - {mk(p - 1)}) p₂
    (by rw [w₁.1]; lia)
  rw [← aT, show al - {mk(p - 1)} + (al - {mk(p - 1)}) = al + al - {mk(D)} by lia] at v₂
  rw [show al - {mk(p - 1)} + (al - {mk(p - 1)}) = al + al - {mk(D)} by lia] at w₂
  generalize sq d₁ (o + {mk(D)}) a (ao + {mk(p - 1)}) (al - {mk(p - 1)}) p₂ = d₂ at *
  have hc₀ : valAt d₂ o (k + k) = A₀ * A₀ := by rw [← v₁]; exact w₂.valAt_eq (by lia)
  -- The values at the points.
  have p₃ : k + 1 < al := by lia''')
        for j in range(1, D):
            pr.append(f'  obtain ⟨s{sub(j)}, e{sub(j)}⟩ := pA {j} (by decide) (by decide) p₃')
    else:
        pr.append(f'''public theorem {name}_spec (d : A) (o : Nat) (a : A) (ao al : Nat) (b : A) (bo bl k : Nat)
    (hk : {shape} al bl k) (mul : MulFn A (al + bl)) (hmul : IsMul mul)
    (hd : o + (al + bl) ≤ LA.size d) :
    Writes ({name} d o a ao al b bo bl k hk mul) d o (al + bl) ∧
      valAt ({name} d o a ao al b bo bl k hk mul) o (al + bl) = valAt a ao al * valAt b bo bl := by
  obtain ⟨hk₁, ha₁, ha₂, hb₁, hb₂⟩ := hk
  dsimp only [{name}]
  have hab := mul_lt a b ao al bo bl
  have hA := valAt_eq_pieces a k {p} ao al (by lia)
  have hB := valAt_eq_pieces b k {q} bo bl (by lia)
  have pA (j : Nat) (hj : 1 ≤ j) := point_spec mul hmul a ao al b bo bl k {p} {q} j (by decide)
    (by decide) hj
  simp only [sumRange_succ, sumRange_zero, Nat.zero_add, Nat.pow_zero, Nat.mul_one,
    Nat.pow_one] at hA hB pA
  have a₀ := piece_full a ao al k 0 (by lia)
  have aT := piece_top a ao al k {p - 1} (by lia)
  have b₀ := piece_full b bo bl k 0 (by lia)
  have bT := piece_top b bo bl k {q - 1} (by lia)
  simp only [Nat.zero_mul, Nat.add_zero{", Nat.one_mul" if q == 2 else ""}] at a₀ aT b₀ bT''')
        for i in range(p):
            pr.append(f'  have lA{sub(i)} := piece_lt a ao al k {i}')
        for i in range(q):
            pr.append(f'  have lB{sub(i)} := piece_lt b bo bl k {i}')
        for i in range(p):
            pr.append(f'  generalize piece a ao al k {i} = A{sub(i)} at *')
        for i in range(q):
            pr.append(f'  generalize piece b bo bl k {i} = B{sub(i)} at *')
        pr.append(f'''  -- The products of the low pieces and of the top pieces.
  have p₁ : k + k < al + bl := by lia
  obtain ⟨w₁, v₁⟩ := hmul d o a ao k b bo k p₁ (by lia)
  rw [← a₀, ← b₀] at v₁
  generalize mul d o a ao k b bo k p₁ = d₁ at *
  have p₂ : al - {mk(p - 1)} + (bl - {mk(q - 1)}) < al + bl := by lia
  obtain ⟨w₂, v₂⟩ := hmul d₁ (o + {mk(D)}) a (ao + {mk(p - 1)}) (al - {mk(p - 1)}) b (bo + {mk(q - 1)})
    (bl - {mk(q - 1)}) p₂ (by rw [w₁.1]; lia)
  rw [← aT, ← bT, show al - {mk(p - 1)} + (bl - {mk(q - 1)}) = al + bl - {mk(D)} by lia] at v₂
  rw [show al - {mk(p - 1)} + (bl - {mk(q - 1)}) = al + bl - {mk(D)} by lia] at w₂
  generalize mul d₁ (o + {mk(D)}) a (ao + {mk(p - 1)}) (al - {mk(p - 1)}) b (bo + {mk(q - 1)})
    (bl - {mk(q - 1)}) p₂ = d₂ at *
  have hc₀ : valAt d₂ o (k + k) = A₀ * B₀ := by rw [← v₁]; exact w₂.valAt_eq (by lia)
  -- The values at the points.
  have p₃ : k + 1 + (k + 1) < al + bl := by lia''')
        for j in range(1, D):
            pr.append(f'  obtain ⟨s{sub(j)}, e{sub(j)}⟩ := pA {j} (by decide) (by decide) (by decide) p₃')
    cs = coeffs(p, qq, 'A', B)
    pr.append('  -- The interpolation.')
    pr.append('  generalize hX : 2 ^ (LA.w * k) = X at *')
    for i in range(2, D + 1):
        pr.append(f'  have hX{i} : 2 ^ (LA.w * ({i} * k)) = {Xp(i)} := by rw [pow_mul_k, hX]; grind')
    val = ' + '.join([f'({cs[0]})'] + [f'{Xp(m)} * ({cs[m]})' for m in range(1, D + 1)])
    rhs = f'valAt a ao al * valAt a ao al' if square else 'valAt a ao al * valAt b bo bl'
    pr.append(f'  have hval : {rhs} =\n      {val} := by\n    rw [{"hA" if square else "hA, hB"}]; grind')
    hbm = ''
    if D in (3, 4):
        j = D - 1
        sa = sum(j ** i for i in range(p))
        sb = sum(j ** i for i in range(qq))
        ea, eb = evalexpr('A', p, j), evalexpr(B, qq, j)
        pr.append(f'''  have hbm : ({ea}) * ({eb}) < 2 ^ (LA.w * (k + k + 2 - 1)) := by
    have h32 : 2 ^ 32 ≤ 2 ^ LA.w := Nat.pow_le_pow_right (by decide) R.w_ge
    rw [show 2 ^ (LA.w * (k + k + 2 - 1)) = X * X * 2 ^ LA.w by
      rw [← hX, ← Nat.pow_add, ← Nat.pow_add]; congr 1; lia]
    have := Nat.mul_lt_mul_of_lt_of_lt (show {ea} < {sa} * X by lia)
      (show {eb} < {sb} * X by lia)
    rw [show {sa} * X * ({sb} * X) = {sa * sb} * (X * X) by grind] at this
    have := Nat.mul_le_mul_left (X * X) h32
    lia''')
        hbm = '\n    (by refine Nat.lt_of_le_of_lt (Nat.le_of_eq ?_) hbm; grind)'
    ss = ' '.join(f's{sub(j)}' for j in range(1, D))
    es = '\n    '.join(f'(by rw [e{sub(j)}]; grind)' for j in range(1, D))
    cargs = ' '.join(f'({c})' for c in cs)
    hxs = ', '.join(['hX'] + [f'hX{i}' for i in range(2, D + 1)])
    wa = '_ ' * (D - 1)
    pr.append(f'''  obtain ⟨f₁, f₂⟩ := interp{D}_spec d₂ o ({n}) k (k + k + 2) {wa}
    {cargs}
    (by rw [w₂.1, w₁.1]; exact hd) (by lia) (by lia) {ss} hc₀ v₂
    {es}{hbm}
    (by rw [{hxs}, ← hval]; exact hab)
  rw [{hxs}, ← hval] at f₂
  exact ⟨f₁.trans ((w₂.mono (by lia) (by lia)).trans (w₁.mono (by lia) (by lia))), f₂⟩
''')
    return '\n'.join(out) + '\n' + '\n'.join(pr)

HEADER = '''/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import MPN.Toom.Toom

/-!
# The Toom methods

Generated by `scripts/toom_methods.py`; do not edit. Each method splits `a` into `p` pieces of `k`
limbs and `b` into `q`, or squares `a`, writes the product of the low pieces and the product of
the top pieces into the window of the result and the products of the values at `1, …, D - 1`,
`D = p + q - 2`, into new arrays of `2 k + 2` limbs, and interpolates. The products are those of a
multiplier `mul` given as an argument, which `mulToom` makes recursive.
-/

namespace MPN.Toom

open LimbArray

variable {A L : Type} [LA : LimbArray A L] [R : ToomOps A L]
'''

if __name__ == '__main__':
    print(HEADER)
    for name, title, p, q in MUL:
        print(method(name, title, p, q, False))
    for name, title, p in SQR:
        print(method(name, title, p, p, True))
    print('end MPN.Toom')
