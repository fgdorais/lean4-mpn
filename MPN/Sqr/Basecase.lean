/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import MPN.Mul.Basecase

/-!
# Schoolbook squaring

`sqrBasecase r a` writes the `2 a.size` limbs of `a * a` into the slice `r`, like GMP's
`mpn_sqr_basecase`. It computes each cross product `aᵢ aⱼ` with `i < j` once, by rows into `r`,
then doubles them and adds the squares `aᵢ²` of the diagonal in one pass, since
`a² = Σ aᵢ² 2^(128 i) + 2 Σ_{i < j} aᵢ aⱼ 2^(64 (i + j))`. It requires `0 < a.size` and
`2 a.size ≤ r.size`, and leaves `r` unchanged otherwise.
-/

open ScalarArray UInt64Array

namespace MPN

/-! ## The square by parts -/

/-- Limb `i` of `a`, as a number. -/
private def sqLimb (a : USlice) (i : Nat) : Nat := a.array[a.start.toNat + i]!.toNat

/-- The value of the limbs of `a` from `i` on. -/
private def sqTail (a : USlice) (i : Nat) : Nat :=
  a.array.valAt (a.start.toNat + i) (a.size.toNat - i)

/--
`Σ_{t < m} a_{i+t} · tail_{i+t+1} · 2^(128 t)`: the cross products of rows `i` to `i + m - 1`.
-/
private def crossSum (a : USlice) (i : Nat) : Nat → Nat
  | 0 => 0
  | m + 1 => sqLimb a i * sqTail a (i + 1) + 2 ^ 128 * crossSum a (i + 1) m

/-- `Σ_{t < m} a_{i+t}² 2^(128 t)`: the squares of the diagonal from `i` on. -/
private def diagSum (a : USlice) (i : Nat) : Nat → Nat
  | 0 => 0
  | m + 1 => sqLimb a i * sqLimb a i + 2 ^ 128 * diagSum a (i + 1) m

private theorem sqTail_succ (a : USlice) (i : Nat) (h : i < a.size.toNat) :
    sqTail a i = sqLimb a i + 2 ^ 64 * sqTail a (i + 1) := by
  rw [sqTail, sqTail, show a.size.toNat - i = a.size.toNat - (i + 1) + 1 by lia, valAt_succ,
    sqLimb, Nat.add_assoc]

private theorem sqTail_size (a : USlice) : sqTail a a.size.toNat = 0 := by
  simp [sqTail]

/-- The square of the limbs from `i` on: the diagonal, and twice the cross products. -/
private theorem sqTail_sq (a : USlice) (i : Nat) (h : i ≤ a.size.toNat) :
    sqTail a i * sqTail a i =
      diagSum a i (a.size.toNat - i) + 2 * 2 ^ 64 * crossSum a i (a.size.toNat - i) := by
  induction h : a.size.toNat - i generalizing i with
  | zero =>
    rw [show i = a.size.toNat by lia, sqTail_size]
    simp [diagSum, crossSum]
  | succ m ih =>
    rw [sqTail_succ a i (by lia), diagSum, crossSum]
    have := ih (i + 1) (by lia) (by lia)
    generalize sqTail a (i + 1) = Q at *
    generalize sqLimb a i = x
    generalize diagSum a (i + 1) m = D at *
    generalize crossSum a (i + 1) m = S at *
    grind

/-! ## Doubling and the diagonal -/

/-- Limb `k` of the diagonal `Σ aᵢ² 2^(128 i)`: the low word of `a_{k/2}²` for even `k`, else the
high word. -/
private def diagLimb (a : USlice) (k : Nat) : Nat :=
  if k % 2 = 0 then sqLimb a (k / 2) * sqLimb a (k / 2) % 2 ^ 64
  else sqLimb a (k / 2) * sqLimb a (k / 2) / 2 ^ 64

/-- The value of the diagonal limbs `k` to `k + m - 1`. -/
private def diagTail (a : USlice) (k : Nat) : Nat → Nat
  | 0 => 0
  | m + 1 => diagLimb a k + 2 ^ 64 * diagTail a (k + 1) m

private theorem diagTail_pair (a : USlice) (i m : Nat) :
    diagTail a (2 * i) (2 * m) = diagSum a i m := by
  induction m generalizing i with
  | zero => rfl
  | succ m ih =>
    rw [show 2 * (m + 1) = 2 * m + 1 + 1 by lia, diagTail, diagTail,
      show 2 * i + 1 + 1 = 2 * (i + 1) by lia, ih, diagSum, diagLimb, diagLimb]
    simp only [show 2 * i % 2 = 0 by lia, show (2 * i + 1) % 2 ≠ 0 by lia, ↓reduceIte,
      show 2 * i / 2 = i by lia, show (2 * i + 1) / 2 = i by lia]
    have := Nat.mod_add_div (sqLimb a i * sqLimb a i) (2 ^ 64)
    generalize sqLimb a i * sqLimb a i = X at *
    generalize diagSum a (i + 1) m = D
    grind

/--
The step of the diagonal pass: limb `x` of the cross products, doubled, plus limb `k` of the
diagonal and the carry `c`, and the carry out.
-/
@[inline, expose] public def sqrDiagStep (a : USlice) (n : USize)
    (hn : n.toNat ≤ a.size.toNat + a.size.toNat) (k : USize) (h : k < n) (x c : UInt64) :
    UInt64 × UInt64 :=
  let y := a[k / 2]'(by
    have := USize.lt_iff_toNat_lt.1 h
    have : 4294967296 ≤ USize.size := by cases USize.size_eq <;> lia
    rw [USize.lt_iff_toNat_lt, USize.toNat_div, USize.toNat_ofNat,
      Nat.mod_eq_of_lt (by simp only [USize.size] at this; lia)]
    lia)
  let d := if k % 2 = 0 then y * y else y.mulh y
  let p := x + x
  let q := p + d
  (q + c, UInt64.addh (UInt64.addh (x >>> 63) p d) q c)

private theorem toNat_two : (2 : USize).toNat = 2 := by
  have : 4294967296 ≤ USize.size := by cases USize.size_eq <;> lia
  rw [USize.toNat_ofNat, Nat.mod_eq_of_lt (by simp only [USize.size] at this; lia)]

private theorem sqrDiagStep_spec (a : USlice) (n : USize)
    (hn : n.toNat ≤ a.size.toNat + a.size.toNat) (k : USize) (h : k < n) (x c : UInt64) :
    (sqrDiagStep a n hn k h x c).1.toNat + 2 ^ 64 * (sqrDiagStep a n hn k h x c).2.toNat =
      2 * x.toNat + diagLimb a k.toNat + c.toNat := by
  have hk := USize.lt_iff_toNat_lt.1 h
  have hk2 : (k / 2).toNat = k.toNat / 2 := by rw [USize.toNat_div, toNat_two]
  have hy : (a[k / 2]'(by rw [USize.lt_iff_toNat_lt, hk2]; lia)).toNat =
      sqLimb a (k.toNat / 2) := by
    rw [USlice.getElem_eq_getElem!, hk2, sqLimb]
  have hpar : (k % 2 = 0) ↔ k.toNat % 2 = 0 := by
    rw [← USize.toNat_inj, USize.toNat_mod, toNat_two, USize.toNat_zero]
  have hd : (if k % 2 = 0 then a[k / 2]'(by rw [USize.lt_iff_toNat_lt, hk2]; lia) *
      a[k / 2]'(by rw [USize.lt_iff_toNat_lt, hk2]; lia) else
      (a[k / 2]'(by rw [USize.lt_iff_toNat_lt, hk2]; lia)).mulh
        (a[k / 2]'(by rw [USize.lt_iff_toNat_lt, hk2]; lia))).toNat = diagLimb a k.toNat := by
    rw [diagLimb]
    by_cases hp : k % 2 = 0
    · simp only [hp, ↓reduceIte, hpar.1 hp, UInt64.toNat_mul, hy]
    · simp only [hp, ↓reduceIte, show ¬k.toNat % 2 = 0 from fun h' => hp (hpar.2 h'),
        UInt64.toNat_mulh, hy]
  simp only [sqrDiagStep]
  rw [← hd]
  generalize (if k % 2 = 0 then _ else _ : UInt64) = d
  have := x.toNat_lt; have := c.toNat_lt; have := d.toNat_lt
  simp only [UInt64.toNat_addh, UInt64.toNat_add, UInt64.toNat_shiftRight, UInt64.reduceToNat,
    Nat.reduceMod, Nat.shiftRight_eq_div_pow]
  generalize x.toNat = x at *
  generalize c.toNat = c at *
  generalize d.toNat = d at *
  lia

/-- The diagonal pass from limb `j` on, by `foldUInPlace`. -/
private theorem diag_spec (a : USlice) (n : USize) (hn : n.toNat ≤ a.size.toNat + a.size.toNat)
    (arr : UInt64Array) (rs : USize) (hr : LoopBound arr rs n) (j : USize) (c : UInt64) :
    (foldUInPlace n (sqrDiagStep a n hn) arr rs hr j c).1.size = arr.size ∧
      (∀ i, (i < rs.toNat + j.toNat ∨ rs.toNat + n.toNat ≤ i) →
        (foldUInPlace n (sqrDiagStep a n hn) arr rs hr j c).1[i]! = arr[i]!) ∧
      (foldUInPlace n (sqrDiagStep a n hn) arr rs hr j c).1.valAt (rs.toNat + j.toNat)
          (n.toNat - j.toNat) +
          2 ^ (64 * (n.toNat - j.toNat)) *
            (foldUInPlace n (sqrDiagStep a n hn) arr rs hr j c).2.toNat =
        2 * arr.valAt (rs.toNat + j.toNat) (n.toNat - j.toNat) +
          diagTail a j.toNat (n.toNat - j.toNat) + c.toNat := by
  induction arr, hr, j, c using foldUInPlace.induct n (sqrDiagStep a n hn) rs with
  | case1 arr hr j c h p ih =>
    rw [foldUInPlace_lt _ _ _ _ _ _ _ h]
    have hj := USize.lt_iff_toNat_lt.1 h
    have hj₁ := USize.toNat_add_one_of_lt h
    have hidx := hr.toNat_add h
    obtain ⟨ih₁, ih₂, ih₃⟩ := ih
    simp only [p] at ih₁ ih₂ ih₃
    rw [hj₁] at ih₂ ih₃
    simp only [UInt64Array.size_uset] at ih₁
    have hv := ih₂ (rs.toNat + j.toNat) (.inl (by lia))
    rw [getElem!_uset, hidx] at hv
    simp only [↓reduceIte] at hv
    have hr' : (arr.uset (rs + j) (sqrDiagStep a n hn j h (arr.uget (rs + j) (hr.uset_bound h)) c).1
        (hr.uset_bound h)).valAt (rs.toNat + (j.toNat + 1))
        (n.toNat - (j.toNat + 1)) =
          arr.valAt (rs.toNat + (j.toNat + 1)) (n.toNat - (j.toNat + 1)) :=
      UInt64Array.valAt_congr _ fun i hi _ => by rw [getElem!_uset]; simp only [hidx]; split <;> lia
    have hx : arr.uget (rs + j) (hr.uset_bound h) = arr[rs.toNat + j.toNat]! := by
      rw [uget_eq_getElem!, hidx]
    refine ⟨ih₁, fun i hi => ?_, ?_⟩
    · rw [ih₂ i (by lia), getElem!_uset]
      simp only [hidx]
      split <;> lia
    · rw [hr'] at ih₃
      obtain ⟨k, hk⟩ : ∃ k, n.toNat - j.toNat = k + 1 := ⟨n.toNat - j.toNat - 1, by lia⟩
      rw [show n.toNat - (j.toNat + 1) = k by lia, ← Nat.add_assoc] at ih₃
      rw [hk, UInt64Array.valAt_succ, UInt64Array.valAt_succ, hv, diagTail, ← hx,
        Nat.mul_succ, Nat.pow_add]
      have := sqrDiagStep_spec a n hn j h (arr.uget (rs + j) (hr.uset_bound h)) c
      generalize (foldUInPlace (β := UInt64) _ _ _ _ _ _ _).1.valAt _ _ = R at *
      generalize (foldUInPlace (β := UInt64) _ _ _ _ _ _ _).2.toNat = c' at *
      generalize (sqrDiagStep a n hn j h _ c).2.toNat = c₁ at *
      generalize (sqrDiagStep a n hn j h _ c).1.toNat = s at *
      generalize arr.valAt _ k = R₀ at *
      generalize diagTail a _ k = D at *
      generalize 2 ^ (64 * k) = P at *
      grind
  | case2 arr hr j c h =>
    rw [foldUInPlace_ge _ _ _ _ _ _ _ h]
    have : n.toNat - j.toNat = 0 := by have := USize.lt_iff_toNat_lt (a := j) (b := n); lia
    simp [this, diagTail]

/-! ## The cross products -/

private theorem MulBound.toNat_add {arr : UInt64Array} {rs : USize} {n : Nat}
    (hr : MulBound arr rs n n) {i : USize} (hi : i.toNat ≤ n) :
    (rs + i).toNat = rs.toNat + i.toNat :=
  USize.toNat_add_of_lt (by lia)

private theorem MulBound.toNat_one {arr : UInt64Array} {rs : USize} {n : Nat}
    (hr : MulBound arr rs n n) {i : USize} (hi : i.toNat < n) : (i + 1).toNat = i.toNat + 1 := by
  rw [USize.toNat_add_of_lt (by rw [USize.toNat_one]; lia), USize.toNat_one]

/--
Row `i` of `sqrRowsLoop` by `addMul1LoopK`: the carry goes to its limb inside the continuation,
so that it is never boxed, and the row returns the array with its size.
-/
@[inline] def sqrRowK (arr : UInt64Array) (rs : USize) (a : USlice)
    (hr : MulBound arr rs a.size.toNat a.size.toNat) (i : USize) (hi : i.toNat ≤ a.size.toNat)
    (h : i + 1 < a.size) (hi' : i.toNat < a.size.toNat) : {arr' : UInt64Array // arr'.size = arr.size} :=
  addMul1LoopK arr.size arr rfl (rs + i) a a.size (USize.le_iff_toNat_le.2 (Nat.le_refl _))
    (by rw [LoopBound, hr.toNat_add hi]; constructor <;> lia)
    (a[i]'(USize.lt_iff_toNat_lt.2 hi')) (i + 1) 0 fun arr' h' c =>
      ⟨arr'.uset (rs + i + a.size) c (by
          rw [h', USize.toNat_add_of_lt (by rw [hr.toNat_add hi]; lia), hr.toNat_add hi]
          have := USize.lt_iff_toNat_lt.1 h
          rw [hr.toNat_one hi'] at this
          lia), by rw [size_uset, h']⟩

private theorem sqrRowK_eq (arr : UInt64Array) (rs : USize) (a : USlice)
    (hr : MulBound arr rs a.size.toNat a.size.toNat) (i : USize) (hi : i.toNat ≤ a.size.toNat)
    (h : i + 1 < a.size) (hi' : i.toNat < a.size.toNat) (hb) (hu) :
    (sqrRowK arr rs a hr i hi h hi').1 =
      (addMul1Loop arr (rs + i) a a.size (USize.le_iff_toNat_le.2 (Nat.le_refl _)) hb
        (a[i]'(USize.lt_iff_toNat_lt.2 hi')) (i + 1) 0).1.uset (rs + i + a.size)
        (addMul1Loop arr (rs + i) a a.size (USize.le_iff_toNat_le.2 (Nat.le_refl _)) hb
          (a[i]'(USize.lt_iff_toNat_lt.2 hi')) (i + 1) 0).2 hu := by
  rw [sqrRowK, addMul1LoopK_eq (hk := size_addMul1Loop ..)]

/--
Adds rows `i` to `a.size - 2` of the cross products to the limbs of `arr`: row `i` is `aᵢ` times
the limbs of `a` above `i`, from limb `rs + 2 i + 1` on, and its carry goes to limb
`rs + i + a.size`.
-/
def sqrRowsLoop (arr : UInt64Array) (rs : USize) (a : USlice)
    (hr : MulBound arr rs a.size.toNat a.size.toNat) (i : USize) (hi : i.toNat ≤ a.size.toNat) :
    UInt64Array :=
  if h : i + 1 < a.size then
    have hi' : i.toNat < a.size.toNat := by
      have := USize.lt_iff_toNat_lt.1 h
      rw [USize.toNat_add_of_lt (by rw [USize.toNat_one]; lia), USize.toNat_one] at this
      lia
    let p := sqrRowK arr rs a hr i hi h hi'
    sqrRowsLoop p.1 rs a (by simp only [MulBound, p.2]; exact hr) (i + 1)
      (by rw [hr.toNat_one hi']; lia)
  else
    arr
termination_by a.size.toNat - i.toNat
decreasing_by
  rw [hr.toNat_one hi']
  lia

private theorem sqrRowsLoop_spec (arr : UInt64Array) (rs : USize) (a : USlice)
    (hr : MulBound arr rs a.size.toNat a.size.toNat) (i : USize) (hi : i.toNat ≤ a.size.toNat) :
    (sqrRowsLoop arr rs a hr i hi).size = arr.size ∧
      (∀ k, (k < rs.toNat + 2 * i.toNat + 1 ∨ rs.toNat + 2 * a.size.toNat ≤ k) →
        (sqrRowsLoop arr rs a hr i hi)[k]! = arr[k]!) ∧
      (i.toNat + 1 ≤ a.size.toNat →
        (sqrRowsLoop arr rs a hr i hi).valAt rs.toNat (2 * a.size.toNat - 1) =
          arr.valAt rs.toNat (a.size.toNat + i.toNat) +
            2 ^ (64 * (2 * i.toNat + 1)) * crossSum a i.toNat (a.size.toNat - i.toNat)) := by
  induction arr, hr, i, hi using sqrRowsLoop.induct rs a with
  | case1 arr hr i hi h hi' p ih =>
    rw [sqrRowsLoop]
    simp only [h, ↓reduceDIte]
    have hI₁ := hr.toNat_one hi'
    have hrow := hr.toNat_add hi
    have hI₂ := USize.lt_iff_toNat_lt.1 h
    rw [hI₁] at hI₂
    have htop : (rs + i + a.size).toNat = rs.toNat + i.toNat + a.size.toNat := by
      rw [USize.toNat_add_of_lt (by rw [hrow]; lia), hrow]
    obtain ⟨hp₁, hp₂, hp₃⟩ := addMul1Loop_spec arr (rs + i) a a.size
      (USize.le_iff_toNat_le.2 (Nat.le_refl _))
      (by rw [LoopBound, hrow]; constructor <;> lia) (a[i]'(USize.lt_iff_toNat_lt.2 hi')) (i + 1) 0
    simp only [hrow, hI₁, UInt64.toNat_zero, Nat.add_zero] at hp₂ hp₃
    have e := sqrRowK_eq arr rs a hr i hi h hi' (by rw [LoopBound, hrow]; constructor <;> lia)
      (by rw [hp₁, htop]; lia)
    simp only [show p = sqrRowK arr rs a hr i hi h hi' from rfl] at ih
    obtain ⟨ih₁, ih₂, ih₃⟩ := ih
    generalize sqrRowsLoop (sqrRowK arr rs a hr i hi h hi').1 rs a _ (i + 1) _ = X at ih₁ ih₂ ih₃ ⊢
    rw [e] at ih₁ ih₂ ih₃
    simp only [size_uset] at ih₁
    rw [hI₁] at ih₂ ih₃
    refine ⟨ih₁.trans hp₁, fun k hk => ?_, fun _ => ?_⟩
    · rw [ih₂ k (by lia), getElem!_uset, htop]
      simp only [show ¬(rs.toNat + i.toNat + a.size.toNat = k) by lia, ↓reduceIte]
      exact hp₂ k (by lia)
    · rw [ih₃ (by lia)]
      generalize hp : addMul1Loop arr (rs + i) a a.size _ _ _ (i + 1) 0 = p at *
      -- The new row: the limbs below it, the row itself, and its carry.
      have hlow : (p.1.uset (rs + i + a.size) p.2 (by rw [hp₁, htop]; lia)).valAt rs.toNat
          (2 * i.toNat + 1) = arr.valAt rs.toNat (2 * i.toNat + 1) :=
        UInt64Array.valAt_congr _ fun k _ hk => by
          rw [getElem!_uset, htop]
          simp only [show ¬(rs.toNat + i.toNat + a.size.toNat = k) by lia, ↓reduceIte]
          exact hp₂ k (by lia)
      have hrow' : (p.1.uset (rs + i + a.size) p.2 (by rw [hp₁, htop]; lia)).valAt
          (rs.toNat + i.toNat + (i.toNat + 1)) (a.size.toNat - (i.toNat + 1)) =
          p.1.valAt (rs.toNat + i.toNat + (i.toNat + 1)) (a.size.toNat - (i.toNat + 1)) :=
        UInt64Array.valAt_congr _ fun k _ hk => by
          rw [getElem!_uset, htop]
          simp only [show ¬(rs.toNat + i.toNat + a.size.toNat = k) by lia, ↓reduceIte]
      have htop' : (p.1.uset (rs + i + a.size) p.2 (by rw [hp₁, htop]; lia))[rs.toNat + i.toNat +
          a.size.toNat]! = p.2 := by
        rw [getElem!_uset, htop]
        simp
      have hsplit : ∀ arr' : UInt64Array, arr'.valAt rs.toNat (a.size.toNat + (i.toNat + 1)) =
          arr'.valAt rs.toNat (2 * i.toNat + 1) + 2 ^ (64 * (2 * i.toNat + 1)) *
            (arr'.valAt (rs.toNat + i.toNat + (i.toNat + 1)) (a.size.toNat - (i.toNat + 1)) +
              2 ^ (64 * (a.size.toNat - (i.toNat + 1))) *
                arr'[rs.toNat + i.toNat + a.size.toNat]!.toNat) := by
        intro arr'
        rw [show a.size.toNat + (i.toNat + 1) = 2 * i.toNat + 1 +
            (a.size.toNat - (i.toNat + 1) + 1) by lia,
          UInt64Array.valAt_add arr' rs.toNat (2 * i.toNat + 1),
          UInt64Array.valAt_add arr' (rs.toNat + (2 * i.toNat + 1))
            (a.size.toNat - (i.toNat + 1)) 1,
          UInt64Array.valAt_one,
          show rs.toNat + (2 * i.toNat + 1) = rs.toNat + i.toNat + (i.toNat + 1) by lia,
          show rs.toNat + i.toNat + (i.toNat + 1) + (a.size.toNat - (i.toNat + 1)) =
            rs.toNat + i.toNat + a.size.toNat by lia]
      have hsplit₀ : arr.valAt rs.toNat (a.size.toNat + i.toNat) =
          arr.valAt rs.toNat (2 * i.toNat + 1) + 2 ^ (64 * (2 * i.toNat + 1)) *
            arr.valAt (rs.toNat + i.toNat + (i.toNat + 1)) (a.size.toNat - (i.toNat + 1)) := by
        rw [show a.size.toNat + i.toNat = 2 * i.toNat + 1 + (a.size.toNat - (i.toNat + 1)) by lia,
          UInt64Array.valAt_add, show rs.toNat + (2 * i.toNat + 1) =
            rs.toNat + i.toNat + (i.toNat + 1) by lia]
      rw [hsplit, hlow, hrow', htop', hsplit₀]
      have hc : crossSum a i.toNat (a.size.toNat - i.toNat) =
          sqLimb a i.toNat * sqTail a (i.toNat + 1) +
            2 ^ 128 * crossSum a (i.toNat + 1) (a.size.toNat - (i.toNat + 1)) := by
        rw [show a.size.toNat - i.toNat = a.size.toNat - (i.toNat + 1) + 1 by lia, crossSum]
      have hx : (a[i]'(USize.lt_iff_toNat_lt.2 hi')).toNat = sqLimb a i.toNat := by
        rw [USlice.getElem_eq_getElem!, sqLimb]
      rw [hx, ← sqTail] at hp₃
      rw [hc, show 2 * (i.toNat + 1) + 1 = 2 * i.toNat + 1 + 2 by lia, Nat.mul_add 64 _ 2,
        Nat.pow_add]
      generalize p.1.valAt _ _ = R at *
      generalize p.2.toNat = c at *
      generalize arr.valAt _ (a.size.toNat - (i.toNat + 1)) = R₀ at *
      generalize arr.valAt rs.toNat (2 * i.toNat + 1) = L at *
      generalize sqLimb a i.toNat = x at *
      generalize sqTail a (i.toNat + 1) = T at *
      generalize crossSum a (i.toNat + 1) _ = C at *
      generalize 2 ^ (64 * (2 * i.toNat + 1)) = P at *
      generalize 2 ^ (64 * (a.size.toNat - (i.toNat + 1))) = Q at *
      grind
  | case2 arr hr i hi h =>
    rw [sqrRowsLoop]
    simp only [h, ↓reduceDIte]
    refine ⟨by simp, by simp, fun hI => ?_⟩
    have hI' : i.toNat + 1 = a.size.toNat := by
      have hI₁ := hr.toNat_one (i := i) (by lia)
      have := mt (USize.lt_iff_toNat_lt (a := i + 1) (b := a.size)).2 h
      rw [hI₁] at this
      lia
    rw [show a.size.toNat - i.toNat = 1 by lia, crossSum, crossSum,
      show i.toNat + 1 = a.size.toNat by lia, sqTail_size,
      show a.size.toNat + i.toNat = 2 * a.size.toNat - 1 by lia]
    simp

/-! ## The square -/

/-! ### Row 0 -/

/-- Limb `rs` cleared, then row 0, `a₀` times the limbs of `a` above it, from limb `rs + 1` on. -/
def sqrRow0 (arr : UInt64Array) (rs : USize) (a : USlice)
    (hb : MulBound arr rs a.size.toNat a.size.toNat) (ha : 0 < a.size) : UInt64Array :=
  let arr₀ := arr.uset rs 0 (by rw [MulBound] at hb; have := USize.lt_iff_toNat_lt.1 ha; lia)
  let p := mul1Loop arr₀ rs a a.size (USize.le_iff_toNat_le.2 (Nat.le_refl _))
    (by simp only [arr₀, LoopBound, size_uset]; rw [MulBound] at hb; constructor <;> lia)
    (a[(0 : USize)]'ha) 1 0
  p.1.uset (rs + a.size) p.2 (by
    simp only [p, size_mul1Loop, arr₀, size_uset]
    rw [hb.toNat_add (Nat.le_refl _)]
    rw [MulBound] at hb
    have := USize.lt_iff_toNat_lt.1 ha
    rw [USize.toNat_zero] at this
    lia)

private theorem sqrRow0_spec (arr : UInt64Array) (rs : USize) (a : USlice)
    (hb : MulBound arr rs a.size.toNat a.size.toNat) (ha : 0 < a.size) :
    (sqrRow0 arr rs a hb ha).size = arr.size ∧
      (∀ k, (k < rs.toNat ∨ rs.toNat + a.size.toNat < k) → (sqrRow0 arr rs a hb ha)[k]! = arr[k]!) ∧
      (sqrRow0 arr rs a hb ha).valAt rs.toNat (a.size.toNat + 1) =
        2 ^ 64 * (sqLimb a 0 * sqTail a 1) := by
  have hn := USize.lt_iff_toNat_lt.1 ha
  rw [USize.toNat_zero] at hn
  have hm := hb
  rw [MulBound] at hm
  have hi := hb.toNat_add (i := a.size) (Nat.le_refl _)
  obtain ⟨hp₁, hp₂, hp₃⟩ := mul1Loop_spec (arr.uset rs 0 (by lia)) rs a a.size
    (USize.le_iff_toNat_le.2 (Nat.le_refl _))
    (by simp only [LoopBound, size_uset]; constructor <;> lia)
    (a[(0 : USize)]'ha) 1 0
  simp only [USize.toNat_one, UInt64.toNat_zero, Nat.add_zero, size_uset] at hp₁ hp₂ hp₃
  have hx : (a[(0 : USize)]'ha).toNat = sqLimb a 0 := by
    rw [USlice.getElem_eq_getElem!, USize.toNat_zero, sqLimb]
  rw [hx, ← sqTail] at hp₃
  refine ⟨by simp [sqrRow0, hp₁], fun k hk => ?_, ?_⟩
  · simp only [sqrRow0]
    rw [getElem!_uset, hi]
    simp only [show ¬(rs.toNat + a.size.toNat = k) by lia, ↓reduceIte]
    rw [hp₂ k (by lia), getElem!_uset]
    simp only [show ¬(rs.toNat = k) by lia, ↓reduceIte]
  · simp only [sqrRow0]
    rw [show a.size.toNat + 1 = 1 + ((a.size.toNat - 1) + 1) by lia, UInt64Array.valAt_add,
      UInt64Array.valAt_add, UInt64Array.valAt_one, UInt64Array.valAt_one, getElem!_uset,
      getElem!_uset, hi]
    simp only [show ¬(rs.toNat + a.size.toNat = rs.toNat) by lia,
      show rs.toNat + 1 + (a.size.toNat - 1) = rs.toNat + a.size.toNat by lia, ↓reduceIte]
    rw [hp₂ _ (.inl (by lia)), getElem!_uset]
    simp only [↓reduceIte, UInt64.toNat_zero, Nat.zero_add]
    rw [valAt_uset_of _ _ _ _ _ _ (.inr (by rw [hi]; lia))]
    rw [Nat.mul_one, Nat.mul_comm (sqLimb a 0), ← hp₃]

/-! ### The other rows -/

private theorem sqr_top {arr : UInt64Array} {rs : USize} {a : USlice}
    (hb : MulBound arr rs a.size.toNat a.size.toNat) (ha : 0 < a.size) :
    (rs + (a.size + a.size - 1)).toNat = rs.toNat + (2 * a.size.toNat - 1) := by
  have hn := USize.lt_iff_toNat_lt.1 ha
  rw [USize.toNat_zero] at hn
  rw [MulBound] at hb
  have hs : (a.size + a.size).toNat = a.size.toNat + a.size.toNat := USize.toNat_add_of_lt (by lia)
  have h₁ : (a.size + a.size - 1).toNat = 2 * a.size.toNat - 1 := by
    rw [USize.toNat_sub_of_le _ _ (USize.le_iff_toNat_le.2 (by rw [hs, USize.toNat_one]; lia)), hs,
      USize.toNat_one]
    lia
  rw [USize.toNat_add_of_lt (by rw [h₁]; lia), h₁]

/-- Rows 1 on, and the top limb cleared: the cross products, from row 0's. -/
def sqrCross (arr : UInt64Array) (rs : USize) (a : USlice)
    (hb : MulBound arr rs a.size.toNat a.size.toNat) (ha : 0 < a.size) : UInt64Array :=
  (sqrRowsLoop arr rs a hb 1 (by
      have := USize.lt_iff_toNat_lt.1 ha
      rw [USize.toNat_zero] at this; rw [USize.toNat_one]; lia)).uset
    (rs + (a.size + a.size - 1)) 0 (by
      rw [(sqrRowsLoop_spec ..).1, sqr_top hb ha]
      rw [MulBound] at hb
      have := USize.lt_iff_toNat_lt.1 ha; rw [USize.toNat_zero] at this
      lia)

private theorem sqrCross_spec (arr : UInt64Array) (rs : USize) (a : USlice)
    (hb : MulBound arr rs a.size.toNat a.size.toNat) (ha : 0 < a.size) :
    (sqrCross arr rs a hb ha).size = arr.size ∧
      (∀ k, (k < rs.toNat + 1 ∨ rs.toNat + 2 * a.size.toNat ≤ k) →
        (sqrCross arr rs a hb ha)[k]! = arr[k]!) ∧
      (arr.valAt rs.toNat (a.size.toNat + 1) = 2 ^ 64 * (sqLimb a 0 * sqTail a 1) →
        (sqrCross arr rs a hb ha).valAt rs.toNat (2 * a.size.toNat) =
          2 ^ 64 * crossSum a 0 a.size.toNat) := by
  have hn := USize.lt_iff_toNat_lt.1 ha
  rw [USize.toNat_zero] at hn
  have ht := sqr_top hb ha
  obtain ⟨h2s, h2u, h2v⟩ := sqrRowsLoop_spec arr rs a hb 1 (by rw [USize.toNat_one]; lia)
  simp only [USize.toNat_one] at h2u h2v
  refine ⟨by simp [sqrCross, h2s], fun k hk => ?_, fun hpre => ?_⟩
  · simp only [sqrCross]
    rw [getElem!_uset, ht]
    simp only [show ¬(rs.toNat + (2 * a.size.toNat - 1) = k) by lia, ↓reduceIte]
    exact h2u k (by lia)
  · simp only [sqrCross]
    rw [show 2 * a.size.toNat = (2 * a.size.toNat - 1) + 1 by lia, UInt64Array.valAt_add,
      UInt64Array.valAt_one, getElem!_uset, ht]
    simp only [↓reduceIte, UInt64.toNat_zero, Nat.mul_zero, Nat.add_zero]
    rw [valAt_uset_of _ _ _ _ _ _ (.inr (by rw [ht]; lia))]
    rcases Nat.lt_or_ge 1 a.size.toNat with h₂ | h₂
    · rw [h2v (by lia), hpre, show a.size.toNat = (a.size.toNat - 1) + 1 by lia, crossSum,
        show a.size.toNat - 1 + 1 - 1 = a.size.toNat - 1 by lia,
        show 64 * (2 * 1 + 1) = 64 + 128 by lia, Nat.pow_add, Nat.zero_add]
      generalize sqTail a 1 = T
      generalize sqLimb a 0 = x
      generalize crossSum a 1 _ = C
      grind
    · -- One limb: no other rows, and no cross products.
      have h1 : a.size.toNat = 1 := by lia
      have hT1 : sqTail a 1 = 0 := by rw [← h1]; exact sqTail_size a
      rw [hT1, Nat.mul_zero, Nat.mul_zero, h1, UInt64Array.valAt_succ,
        UInt64Array.valAt_one] at hpre
      rw [h1, show 2 * 1 - 1 = 1 by rfl, UInt64Array.valAt_one, h2u _ (.inl (by lia))]
      simp only [crossSum, hT1, Nat.mul_zero, Nat.zero_add, Nat.add_zero]
      lia

/-! ### The diagonal pass -/

/-- The diagonal pass on `arr`, which holds the cross products. -/
def sqrFinish (arr : UInt64Array) (rs : USize) (a : USlice)
    (hs : (a.size + a.size).toNat = a.size.toNat + a.size.toNat)
    (hr : LoopBound arr rs (a.size + a.size)) : UInt64Array :=
  foldUInPlaceThen (a.size + a.size) (sqrDiagStep a (a.size + a.size) (Nat.le_of_eq hs)) arr rs hr
    0 0 fun arr _ _ => arr

private theorem sqrFinish_spec (arr : UInt64Array) (rs : USize) (a : USlice)
    (hs : (a.size + a.size).toNat = a.size.toNat + a.size.toNat)
    (hr : LoopBound arr rs (a.size + a.size)) :
    (sqrFinish arr rs a hs hr).size = arr.size ∧
      (∀ k, (k < rs.toNat ∨ rs.toNat + 2 * a.size.toNat ≤ k) →
        (sqrFinish arr rs a hs hr)[k]! = arr[k]!) ∧
      (arr.valAt rs.toNat (2 * a.size.toNat) = 2 ^ 64 * crossSum a 0 a.size.toNat →
        (sqrFinish arr rs a hs hr).valAt rs.toNat (2 * a.size.toNat) = a.toNat * a.toNat) := by
  obtain ⟨h3s, h3u, h3v⟩ := diag_spec a (a.size + a.size) (Nat.le_of_eq hs) arr rs hr 0 0
  simp only [USize.toNat_zero, Nat.add_zero, Nat.sub_zero, UInt64.toNat_zero, hs] at h3u h3v
  simp only [sqrFinish, foldUInPlaceThen_eq]
  refine ⟨h3s, fun k hk => h3u k (by lia), fun hT => ?_⟩
  rw [show 2 * a.size.toNat = a.size.toNat + a.size.toNat by lia] at hT ⊢
  have hD := diagTail_pair a 0 a.size.toNat
  simp only [Nat.mul_zero, show 2 * a.size.toNat = a.size.toNat + a.size.toNat by lia] at hD
  rw [hT, hD] at h3v
  have hsq := sqTail_sq a 0 (Nat.zero_le _)
  rw [Nat.sub_zero] at hsq
  have hA : sqTail a 0 = a.toNat := by
    rw [sqTail, Nat.add_zero, Nat.sub_zero, USlice.toNat_eq_valAt]
  rw [hA] at hsq
  have hlt : a.toNat * a.toNat < 2 ^ (64 * (a.size.toNat + a.size.toNat)) := by
    have := valAt_lt a.array a.start.toNat a.size.toNat
    rw [← USlice.toNat_eq_valAt] at this
    rw [Nat.mul_add, Nat.pow_add]
    exact Nat.mul_lt_mul_of_lt_of_lt this this
  generalize (foldUInPlace (β := UInt64) _ _ _ _ _ 0 0).2.toNat = c at *
  generalize (foldUInPlace (β := UInt64) _ _ _ _ _ 0 0).1.valAt _ _ = V at *
  generalize 2 ^ (64 * (a.size.toNat + a.size.toNat)) = P at *
  generalize a.toNat * a.toNat = S at *
  rcases Nat.eq_zero_or_pos c with hc | hc
  · subst hc; lia
  · have := Nat.le_mul_of_pos_right P hc
    generalize P * c = Pc at *
    lia

/-! ### The square -/

private theorem sqr_bound (r a : USlice) (h : a.size ≤ r.size ∧ a.size ≤ r.size - a.size) :
    MulBound r.array r.start a.size.toNat a.size.toNat ∧
      (a.size + a.size).toNat = a.size.toNat + a.size.toNat := by
  have hr := r.loopBound (USize.le_iff_toNat_le.2 (Nat.le_refl r.size.toNat))
  have h₁ := USize.le_iff_toNat_le.1 h.1
  have h₂ := USize.le_iff_toNat_le.1 h.2
  rw [USize.toNat_sub_of_le _ _ h.1] at h₂
  simp only [LoopBound] at hr
  exact ⟨⟨by lia, by lia⟩, USize.toNat_add_of_lt (by lia)⟩

private theorem sqr_loopBound {arr : UInt64Array} {rs : USize} {a : USlice}
    (hb : MulBound arr rs a.size.toNat a.size.toNat)
    (hs : (a.size + a.size).toNat = a.size.toNat + a.size.toNat) :
    LoopBound arr rs (a.size + a.size) := by
  rw [MulBound] at hb
  rw [LoopBound, hs]
  constructor <;> lia

/--
Writes the `2 a.size` limbs of `a * a` into `r`, like GMP's `mpn_sqr_basecase`. It requires
`0 < a.size` and `2 a.size ≤ r.size`, and leaves `r` unchanged otherwise.
-/
public def sqrBasecase (r a : USlice) : UInt64Array :=
  if h : 0 < a.size ∧ a.size ≤ r.size ∧ a.size ≤ r.size - a.size then
    have hb := sqr_bound r a h.2
    sqrFinish (sqrCross (sqrRow0 r.array r.start a hb.1 h.1) r.start a
        (by simp only [MulBound, (sqrRow0_spec ..).1]; exact hb.1) h.1) r.start a hb.2
      (sqr_loopBound
        (by simp only [MulBound, (sqrCross_spec ..).1, (sqrRow0_spec ..).1]; exact hb.1)
        hb.2)
  else
    r.array

@[simp] public theorem size_sqrBasecase (r a : USlice) :
    (sqrBasecase r a).size = r.array.size := by
  rw [sqrBasecase]
  split
  · rw [(sqrFinish_spec ..).1, (sqrCross_spec ..).1, (sqrRow0_spec ..).1]
  · rfl

/-- `sqrBasecase` leaves the limbs of `r` outside the ones it writes unchanged. -/
public theorem getElem!_sqrBasecase (r a : USlice) (k : Nat)
    (hk : k < r.start.toNat ∨ r.start.toNat + 2 * a.size.toNat ≤ k) :
    (sqrBasecase r a)[k]! = r.array[k]! := by
  rw [sqrBasecase]
  split
  · rw [(sqrFinish_spec ..).2.1 k hk, (sqrCross_spec ..).2.1 k (by lia),
      (sqrRow0_spec ..).2.1 k (by lia)]
  · rfl

public theorem valAt_sqrBasecase (r a : USlice) (ha : 0 < a.size)
    (hr : 2 * a.size.toNat ≤ r.size.toNat) :
    (sqrBasecase r a).valAt r.start.toNat (2 * a.size.toNat) = a.toNat * a.toNat := by
  have h : 0 < a.size ∧ a.size ≤ r.size ∧ a.size ≤ r.size - a.size := by
    refine ⟨ha, USize.le_iff_toNat_le.2 (by lia), USize.le_iff_toNat_le.2 ?_⟩
    rw [USize.toNat_sub_of_le _ _ (USize.le_iff_toNat_le.2 (by lia))]
    lia
  rw [sqrBasecase]
  simp only [h, and_self, ↓reduceDIte]
  exact (sqrFinish_spec ..).2.2 ((sqrCross_spec ..).2.2 (sqrRow0_spec ..).2.2)

end MPN
