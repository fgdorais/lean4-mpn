/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import MPN.Add
public import MPN.Mul.Limb
public import MPN.Mul.Comba

/-!
# Schoolbook squaring

`sqrBasecase a` is the schoolbook square, after GMP's `mpn_sqr_basecase`. Squaring needs each
product `aᵢ aⱼ` with `i ≠ j` only once, since it appears twice: `a² = D + 2 S` where `D` holds the
squares `aᵢ²` on the diagonal and `S` is the sum of the products `aᵢ aⱼ` with `j < i`. That is about
half the limb products of `mulBasecase a a`.

`S` is built one row at a time: row `i` adds `aᵢ * a[0...i]` at limb `i` and stores the carry,
with `addMul1SetPre`, which reads the first `i` limbs of `a` without a slice. After `i` rows,
`2 S + D` is the square of the first `i` limbs, since adding the limb `aᵢ` adds
`2 βⁱ Aᵢ aᵢ + β²ⁱ aᵢ²` to the square of `Aᵢ`. A last pass, `sqrAddDiag`, computes `2 S + D` in
place, like GMP's `mpn_sqr_diag_addlsh1`.
-/

open ScalarArray

namespace MPN

/-- The value of the squares of the limbs of `l`, the square of limb `i` at limb `2 i`. -/
@[expose] public def sqDiag : List UInt32 → Nat
  | [] => 0
  | d :: l => d.toNat * d.toNat + 2 ^ 64 * sqDiag l

public theorem sqDiag_append (l₁ l₂ : List UInt32) :
    sqDiag (l₁ ++ l₂) = sqDiag l₁ + 2 ^ (64 * l₁.length) * sqDiag l₂ := by
  induction l₁ with
  | nil => simp [sqDiag]
  | cons d l ih =>
    simp only [List.cons_append, sqDiag, ih, List.length_cons, Nat.mul_add, Nat.mul_one,
      Nat.pow_add]
    grind

/-- Adds the rows `a[i] * a[0...i]` from `i` on into `r` at limb `i`, one `addMul1` per row. -/
def sqrRowsLoop (a : UInt32Array.Slice) (r : UInt32Array) (i : Nat) (h : r.size = 2 * a.size) :
    UInt32Array :=
  if hi : i < a.size then
    sqrRowsLoop a (addMul1SetPre r i a i a[i] (by lia) (by lia)) (i + 1)
      (by simp [addMul1SetPre_eq, h])
  else
    r
termination_by a.size - i

private theorem sqrRowsLoop_spec (a : UInt32Array.Slice) (r : UInt32Array) (i : Nat)
    (h : r.size = 2 * a.size) (hi : i ≤ a.size)
    (hr : 2 * ofLimbs r.toList + sqDiag (a.copy.toList.take i) =
      ofLimbs (a.copy.toList.take i) * ofLimbs (a.copy.toList.take i)) :
    (sqrRowsLoop a r i h).size = 2 * a.size ∧
      2 * ofLimbs (sqrRowsLoop a r i h).toList + sqDiag a.copy.toList = toNat a * toNat a := by
  induction r, i, h using sqrRowsLoop.induct a with
  | case1 r i h hi' ih =>
    rw [sqrRowsLoop]
    simp only [hi', ↓reduceDIte]
    apply ih (by lia)
    rw [addMul1SetPre_eq]
    have hsl : (a.slice 0 i).size = i := by simp; lia
    have hsl' : toNat (a.slice 0 i) = ofLimbs (a.copy.toList.take i) := by
      simp [toNat, UInt32Array.Slice.copy_slice, List.extract_eq_take_drop]
    -- The limb at `i + i` is zero, since the rows so far are below `2^(32 (i + i))`.
    have hA := ofLimbs_lt (a.copy.toList.take i)
    simp only [List.length_take, UInt32Array.length_toList, UInt32Array.Slice.size_copy,
      Nat.min_eq_left (Nat.le_of_lt hi')] at hA
    have hlt : ofLimbs r.toList < 2 ^ (32 * (i + i)) := by
      have : ofLimbs (a.copy.toList.take i) * ofLimbs (a.copy.toList.take i) <
          2 ^ (32 * i) * 2 ^ (32 * i) := Nat.mul_lt_mul'' hA hA
      rw [Nat.mul_add, Nat.pow_add]
      lia
    have hk : i + i < r.toList.length := by simp; lia
    have hz : r.toList[i + i] = 0 := getElem_eq_zero_of_ofLimbs_lt hk hlt
    simp only [UInt32Array.getElem_toList] at hz
    have hadd := toNat_addMul1Set r i (a.slice 0 i) a[i] (by simp; lia) (by simpa [hsl] using hz)
    simp only [toNat_toSlice, hsl'] at hadd
    rw [hadd]
    have hai : (a.copy.toList)[i]'(by simpa using hi') = a[i] := by simp
    rw [ofLimbs_take_add_one _ _ (by simpa using hi'), hai,
      List.take_add_one, List.getElem?_eq_getElem (by simpa using hi'), Option.toList_some, hai,
      sqDiag_append, List.length_take_of_le (by simpa using Nat.le_of_lt hi')]
    simp only [sqDiag, Nat.mul_zero, Nat.add_zero]
    have hpow : 2 ^ (64 * i) = 2 ^ (32 * i) * 2 ^ (32 * i) := by
      rw [← Nat.pow_add]
      congr 1
      lia
    rw [hpow] at *
    generalize ofLimbs r.toList = R at *
    generalize ofLimbs (a.copy.toList.take i) = A at *
    generalize sqDiag (a.copy.toList.take i) = D at *
    generalize 2 ^ (32 * i) = P at *
    generalize a[i].toNat = x at *
    grind
  | case2 r i h hi' =>
    rw [sqrRowsLoop]
    simp only [hi', ↓reduceDIte]
    refine ⟨h, ?_⟩
    have : i = a.size := by lia
    rw [this, List.take_of_length_le (by simp)] at hr
    rw [hr]
    rfl

/-! ## Doubling and adding the diagonal

The last pass computes `2 S + D` in place over `S`, like GMP's `mpn_sqr_diag_addlsh1`: limb `k`
becomes `2 sₖ + dₖ` plus the carry, where `dₖ` is the low or the high word of `a[k / 2]²`.
-/

/-- The limbs of the squares of the limbs of `l`, two limbs each. -/
@[expose] public def diagLimbs : List UInt32 → List UInt32
  | [] => []
  | x :: l => (x.mulAddAdd x 0 0).1 :: (x.mulAddAdd x 0 0).2 :: diagLimbs l

@[simp] public theorem length_diagLimbs (l : List UInt32) :
    (diagLimbs l).length = 2 * l.length := by
  induction l with
  | nil => rfl
  | cons x l ih => simp only [diagLimbs, List.length_cons, ih]; lia

public theorem ofLimbs_diagLimbs (l : List UInt32) : ofLimbs (diagLimbs l) = sqDiag l := by
  induction l with
  | nil => rfl
  | cons x l ih =>
    have := UInt32.mulAddAdd_spec x x 0 0
    simp only [UInt32.toNat_zero, Nat.add_zero] at this
    simp only [diagLimbs, ofLimbs_cons, ih, sqDiag]
    rw [show (2 : Nat) ^ 64 = 2 ^ 32 * 2 ^ 32 by decide]
    generalize (x.mulAddAdd x 0 0).1.toNat = lo at *
    generalize (x.mulAddAdd x 0 0).2.toNat = hi at *
    generalize sqDiag l = D
    rw [← this]
    grind

/-- Limb `k` of the diagonal of `a`: the low or high word of `a[k / 2]²`. -/
@[inline] def diagLimb (a : UInt32Array.Slice) (k : Nat) : UInt32 :=
  let x := a.getD (k / 2) 0
  if k % 2 = 0 then (x.mulAddAdd x 0 0).1 else (x.mulAddAdd x 0 0).2

private theorem getD_diagLimbs (l : List UInt32) (k : Nat) :
    (diagLimbs l).getD k 0 =
      if k % 2 = 0 then ((l.getD (k / 2) 0).mulAddAdd (l.getD (k / 2) 0) 0 0).1
      else ((l.getD (k / 2) 0).mulAddAdd (l.getD (k / 2) 0) 0 0).2 := by
  induction l generalizing k with
  | nil =>
    simp only [diagLimbs, List.getD_nil]
    split <;> rfl
  | cons x l ih =>
    match k with
    | 0 => simp [diagLimbs]
    | 1 => simp [diagLimbs]
    | k + 2 =>
      simp only [diagLimbs, List.getD_cons_succ]
      rw [ih k, show (k + 2) / 2 = k / 2 + 1 by lia, show (k + 2) % 2 = k % 2 by lia,
        List.getD_cons_succ]

private theorem diagLimb_eq (a : UInt32Array.Slice) (k : Nat) :
    diagLimb a k = (diagLimbs a.copy.toList).getD k 0 := by
  rw [getD_diagLimbs, diagLimb, getD_eq_getD_toList_copy]

/-- Replaces limbs `r[k...]` by `2 rᵢ + dᵢ` with the carry `c`, where `dᵢ = diagLimb a i`. -/
def sqrAddDiagLoop (a : UInt32Array.Slice) (r : UInt32Array) (k : Nat) (c : UInt32) :
    UInt32Array × UInt32 :=
  if h : k < r.size then
    let p := r[k].dblAddAdd (diagLimb a k) c
    sqrAddDiagLoop a (r.set k p.1 h) (k + 1) p.2
  else
    (r, c)
termination_by r.size - k

private theorem sqrAddDiagLoop_spec (a : UInt32Array.Slice) (r : UInt32Array) (k : Nat)
    (c : UInt32) (hD : 2 * a.size ≤ r.size) (hk : k ≤ r.size) :
    (sqrAddDiagLoop a r k c).1.size = r.size ∧
      ofLimbs (sqrAddDiagLoop a r k c).1.toList +
          2 ^ (32 * r.size) * (sqrAddDiagLoop a r k c).2.toNat =
        ofLimbs r.toList + 2 ^ (32 * k) * (c.toNat + ofLimbs (r.toList.drop k) +
          ofLimbs ((diagLimbs a.copy.toList).drop k)) := by
  induction r, k, c using sqrAddDiagLoop.induct a with
  | case1 r k c h p ih =>
    rw [sqrAddDiagLoop]
    simp only [h, ↓reduceDIte]
    obtain ⟨ih₁, ih₂⟩ := ih (by simpa using hD) (by simp; lia)
    simp only [UInt32Array.size_set] at ih₁ ih₂
    refine ⟨ih₁, ?_⟩
    have hk : k < r.toList.length := by simp; lia
    have hset := ofLimbs_set r.toList k p.1 hk
    have hstep := UInt32.dblAddAdd_spec r[k] (diagLimb a k) c
    simp only [UInt32Array.getElem_toList] at hset
    have hr' := ofLimbs_drop r.toList k
    have hd := ofLimbs_drop (diagLimbs a.copy.toList) k
    have hg' : r.toList.getD k 0 = r[k] := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk]
      simp only [Option.getD_some, UInt32Array.getElem_toList]
      rfl
    rw [hg'] at hr'
    rw [← diagLimb_eq] at hd
    rw [UInt32Array.toList_set, List.drop_set_of_lt (by lia : k < k + 1)] at ih₂
    rw [ih₂, Nat.mul_add 32 k 1, Nat.mul_one, Nat.pow_add]
    generalize ofLimbs (r.toList.set k p.1) = R₁ at *
    generalize ofLimbs r.toList = R at *
    generalize ofLimbs (r.toList.drop (k + 1)) = T at *
    generalize ofLimbs ((diagLimbs a.copy.toList).drop (k + 1)) = D at *
    generalize ofLimbs (r.toList.drop k) = T₀ at *
    generalize ofLimbs ((diagLimbs a.copy.toList).drop k) = D₀ at *
    generalize 2 ^ (32 * k) = P at *
    generalize p.1.toNat = lo at *
    generalize p.2.toNat = hi at *
    generalize (diagLimb a k).toNat = d at *
    generalize r[k].toNat = y at *
    grind
  | case2 r k c h =>
    rw [sqrAddDiagLoop]
    simp only [h, ↓reduceDIte]
    have h₁ : r.toList.drop k = [] := List.drop_of_length_le (by simp; lia)
    have h₂ : (diagLimbs a.copy.toList).drop k = [] :=
      List.drop_of_length_le (by simp; lia)
    have h₃ : k = r.size := by lia
    rw [h₁, h₂, h₃]
    simp

/-- `2 S + D` in place over `r`, with the carry out. -/
public def sqrAddDiag (a : UInt32Array.Slice) (r : UInt32Array) : UInt32Array × UInt32 :=
  sqrAddDiagLoop a r 0 0

private theorem toNat_shiftRight_one (k : USize) : (k >>> 1).toNat = k.toNat / 2 := by
  have : 1 % System.Platform.numBits = 1 := by
    rcases System.Platform.numBits_eq with h | h <;> simp [h]
  rw [USize.toNat_shiftRight]
  simp [Nat.shiftRight_eq_div_pow, this]

private theorem and_one_eq_zero_iff (k : USize) : k &&& 1 = 0 ↔ k.toNat % 2 = 0 := by
  rw [← USize.toNat_inj, USize.toNat_and]
  simp [Nat.and_one_is_mod]

/--
Limb `k` of the diagonal of the `n` limbs of `arr` from `st`, read with `USize` indices, for
`k < len ≤ 2 n`.
-/
@[inline] def diagLimbU (arr : UInt32Array) (st n : USize) (has : arr.size < USize.size)
    (h : st.toNat + n.toNat ≤ arr.size) (len : USize) (hlen : len.toNat ≤ 2 * n.toNat)
    (k : USize) (hk : k.toNat < len.toNat) : UInt32 :=
  let x := arr.uget (st + (k >>> 1)) (by
    rw [toNat_add_usize (by rw [toNat_shiftRight_one]; lia), toNat_shiftRight_one]
    lia)
  if k &&& 1 = 0 then (x.mulAddAdd x 0 0).1 else (x.mulAddAdd x 0 0).2

/-- The step of the fold of `sqrAddDiagFast`. -/
@[inline] def sqrAddDiagStep (arr : UInt32Array) (st n : USize) (has : arr.size < USize.size)
    (h : st.toNat + n.toNat ≤ arr.size) (len : USize) (hlen : len.toNat ≤ 2 * n.toNat)
    (k : USize) (hk : k.toNat < len.toNat) (y c : UInt32) : UInt32 × UInt32 :=
  y.dblAddAdd (diagLimbU arr st n has h len hlen k hk) c

private theorem diagLimbU_eq (a : UInt32Array.Slice) (has : a.array.size < USize.size)
    (len : USize) (hlen : len.toNat ≤ 2 * a.size.toUSize.toNat) (k : Nat) (hk)
    (hk' : k < 2 * a.size) (hk₀ : k < USize.size) :
    diagLimbU a.array a.start.toUSize a.size.toUSize has (limbU_bound a has) len hlen k.toUSize hk =
      diagLimb a k := by
  have := a.stop_le_array_size
  have := a.start_le_stop
  have := a.size_eq
  have hsh : (k.toUSize >>> 1).toNat = k / 2 := by rw [toNat_shiftRight_one, toNat_toUSize hk₀]
  have hst : a.start.toUSize.toNat = a.start := toNat_toUSize (by lia)
  have hidx : (a.start.toUSize + k.toUSize >>> 1).toNat = a.start + k / 2 := by
    rw [toNat_add_usize (by rw [hsh, hst]; lia), hsh, hst]
  have hx : a.array.uget (a.start.toUSize + k.toUSize >>> 1) (by rw [hidx]; lia) =
      a.getD (k / 2) 0 := by
    rw [uget_eq_getElem _ _ _ hidx, UInt32Array.Slice.getD_eq]
    simp only [show k / 2 < a.size by lia, ↓reduceDIte]
    rfl
  have hp : (k.toUSize &&& 1 = 0) ↔ k % 2 = 0 := by
    rw [and_one_eq_zero_iff, toNat_toUSize hk₀]
  simp only [diagLimbU, diagLimb, hx]
  by_cases he : k % 2 = 0
  · simp [he, hp.2 he]
  · simp [he, show ¬ (k.toUSize &&& 1 = 0) from fun h' => he (hp.1 h')]

/-- `sqrAddDiag` with `foldInPlace`, which the compiler uses in its place. -/
public def sqrAddDiagFast (a : UInt32Array.Slice) (r : UInt32Array) : UInt32Array × UInt32 :=
  if hs : r.size < 4294967295 ∧ a.array.size < 4294967295 ∧ r.size ≤ 2 * a.size then
    have has := lt_usizeSize hs.2.1
    have hrs := lt_usizeSize hs.1
    let arr := a.array
    let st := a.start.toUSize
    r.foldInPlace 0 r.size.toUSize 0
      (sqrAddDiagStep arr st a.size.toUSize has (limbU_bound a has) r.size.toUSize (by
        have := a.stop_le_array_size
        have := a.start_le_stop
        have := a.size_eq
        rw [toNat_toUSize hrs, toNat_toUSize (by lia)]
        exact hs.2.2))
      (by rw [USize.toNat_zero, toNat_toUSize hrs]; lia)
  else
    sqrAddDiagLoop a r 0 0

/-- The fold of `sqrAddDiagFast` from limb `k` on is `sqrAddDiagLoop` from limb `k` on. -/
private theorem foldInPlace_loop_sqrAddDiag (a : UInt32Array.Slice)
    (has : a.array.size < USize.size) (len : USize) (hl : len.toNat ≤ 2 * a.size.toUSize.toNat)
    (hla : len.toNat ≤ 2 * a.size) (r : UInt32Array) (s n : Nat) (hs : s = 0)
    (hn : n = r.size) (hnl : n = len.toNat) (k : Nat) (c : UInt32) (h' hlen) :
    UInt32Array.foldInPlace.loop len
        (sqrAddDiagStep a.array a.start.toUSize a.size.toUSize has (limbU_bound a has) len hl)
        s n r h' hlen k c =
      sqrAddDiagLoop a r k c := by
  subst s
  induction r, k, c using sqrAddDiagLoop.induct a with
  | case1 r k c h p ih =>
    rw [UInt32Array.foldInPlace.loop, sqrAddDiagLoop]
    simp only [show k < n by lia, h, ↓reduceDIte]
    simp only [Nat.zero_add, sqrAddDiagStep,
      diagLimbU_eq a has len hl k _ (by lia) (by have := len.toNat_lt_size; lia)]
    exact ih (by simp [hn]) _
  | case2 r k c h =>
    rw [UInt32Array.foldInPlace.loop, sqrAddDiagLoop]
    simp only [show ¬ k < n by lia, h, ↓reduceDIte]

@[csimp] public theorem sqrAddDiag_eq_sqrAddDiagFast : @sqrAddDiag = @sqrAddDiagFast := by
  funext a r
  rw [sqrAddDiag, sqrAddDiagFast]
  split
  · rename_i hs
    have := USize.le_size
    have := a.stop_le_array_size
    have := a.start_le_stop
    have := a.size_eq
    have hrs := lt_usizeSize hs.1
    exact (foldInPlace_loop_sqrAddDiag a (lt_usizeSize hs.2.1) _ _
      (by rw [toNat_toUSize hrs]; exact hs.2.2) r _ _ USize.toNat_zero (toNat_toUSize hrs) rfl 0 0
      _ _).symm
  · rfl

private theorem sqrAddDiag_spec (a : UInt32Array.Slice) (r : UInt32Array)
    (hD : 2 * a.size ≤ r.size) :
    (sqrAddDiag a r).1.size = r.size ∧
      ofLimbs (sqrAddDiag a r).1.toList + 2 ^ (32 * r.size) * (sqrAddDiag a r).2.toNat =
        2 * ofLimbs r.toList + sqDiag a.copy.toList := by
  obtain ⟨h₁, h₂⟩ := sqrAddDiagLoop_spec a r 0 0 hD (Nat.zero_le _)
  refine ⟨h₁, ?_⟩
  simp only [List.drop_zero, Nat.mul_zero, Nat.pow_zero, Nat.one_mul, UInt32.toNat_zero,
    Nat.zero_add, ofLimbs_diagLimbs] at h₂
  rw [sqrAddDiag, h₂]
  lia

/-- All `2 * a.size` limbs of `a * a`, untrimmed, by the schoolbook algorithm. -/
public def sqrBasecase (a : UInt32Array.Slice) : UInt32Array :=
  (sqrAddDiag a (sqrRowsLoop a (.replicate (2 * a.size) 0) 0 (by simp))).1

public theorem sqrBasecase_spec (a : UInt32Array.Slice) :
    (sqrBasecase a).size = a.size + a.size ∧ toNat (sqrBasecase a) = toNat a * toNat a := by
  rw [toNat_toSlice]
  unfold sqrBasecase
  obtain ⟨hss, hs⟩ := sqrRowsLoop_spec a (.replicate (2 * a.size) 0) 0 (by simp) (Nat.zero_le _)
    (by simp [sqDiag])
  generalize sqrRowsLoop a (.replicate (2 * a.size) 0) 0 (by simp) = s at *
  obtain ⟨hds, hd⟩ := sqrAddDiag_spec a s (by lia)
  have hlt : toNat a * toNat a < 2 ^ (32 * s.size) := by
    rw [hss, show 32 * (2 * a.size) = 32 * a.size + 32 * a.size by lia, Nat.pow_add]
    exact Nat.mul_lt_mul'' (toNat_lt a) (toNat_lt a)
  -- The square fits in `2 n` limbs, so the carry out is zero.
  have hc : (sqrAddDiag a s).2.toNat = 0 := by
    rcases Nat.eq_zero_or_pos (sqrAddDiag a s).2.toNat with h | h
    · exact h
    · have : 2 ^ (32 * s.size) * 1 ≤ 2 ^ (32 * s.size) * (sqrAddDiag a s).2.toNat :=
        Nat.mul_le_mul_left _ h
      lia
  refine ⟨by rw [hds, hss]; lia, ?_⟩
  rw [← hs]
  rw [hc, Nat.mul_zero, Nat.add_zero] at hd
  exact hd

/-! ## The compiled square

`sqrBasecaseFast` squares by Comba's method (`csqMul`) when the size allows it, and `@[csimp]`
makes the compiler use it in place of `sqrBasecase`: both compute all `2 * a.size` limbs of the
square, and limbs of a given length are determined by their value.
-/

/-- `sqrBasecase`, by Comba's method when the size allows it. -/
public def sqrBasecaseFast (a : UInt32Array.Slice) : UInt32Array :=
  if h : SqrOK a then csqMul a h else sqrBasecase a

@[csimp] public theorem sqrBasecase_eq_sqrBasecaseFast : @sqrBasecase = @sqrBasecaseFast := by
  funext a
  unfold sqrBasecaseFast
  split
  · rename_i h
    obtain ⟨hs, hv⟩ := csqMul_spec a h
    obtain ⟨hs', hv'⟩ := sqrBasecase_spec a
    apply UInt32Array.toList_inj.1
    apply ofLimbs_inj_of_length (by simp [hs, hs'])
    rw [← toNat_toSlice, ← toNat_toSlice, hv', hv]
  · rfl

end MPN
