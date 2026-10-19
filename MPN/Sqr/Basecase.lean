/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import MPN.Add
public import MPN.Mul.Limb
public import MPN.Mul.Comba
public import MPN.Mul.Rows

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

/-! ## Squares by rows into wide accumulators

`sqrRowsMul a` adds the rows `aᵢ a[i + 1...]` into `UInt64` accumulators at limb `2 i + 1` with
`addRow`, as `rowsMul` does for products, which gives the products below the diagonal, `S`. The
last pass computes `2 S + D` and the carries in one: limb `k` is twice accumulator `k`, plus the
limb `k` of the diagonal, plus the carry.
-/

private theorem slice_from_start (a : UInt32Array.Slice) (k : Nat) (hk : k ≤ a.size) :
    (a.slice k a.size).start = a.start + k := by
  have := a.stop_le_array_size; have := a.start_le_stop; have := a.size_eq
  simp only [UInt32Array.Slice.slice, UInt32Array.start_toSlice]
  lia

private theorem slice_from_array (a : UInt32Array.Slice) (k : Nat) :
    (a.slice k a.size).array = a.array := by
  simp [UInt32Array.Slice.slice]

private theorem toNat_slice_from_drop (a : UInt32Array.Slice) (k : Nat) :
    toNat (a.slice k a.size) = ofLimbs (a.copy.toList.drop k) := by
  rw [toNat, UInt32Array.Slice.copy_slice, UInt32Array.toList_extract, List.extract_eq_take_drop,
    List.take_of_length_le (by simp)]

/-- The rows `aᵢ a[i + 1...]` from `i` on, added into `acc` at limb `2 i + 1`. -/
def sqrRowsAcc (a : UInt32Array.Slice) (ha : a.array.size < USize.size)
    (hn : 2 * a.size < USize.size) (sa na : USize) (hsa : sa = a.start.toUSize)
    (hna : na = a.size.toUSize) (acc : UInt64Array) (hacc : acc.size = 2 * a.size)
    (i : USize) : UInt64Array :=
  if hi : i < na then
    have hna' : na.toNat = a.size := by rw [hna, toNat_toUSize (by lia)]
    have hi' : i.toNat < a.size := by rw [USize.lt_iff_toNat_lt, hna'] at hi; exact hi
    have hst : a.start + a.size < USize.size := by
      have := a.stop_le_array_size; have := a.start_le_stop; have := a.size_eq; lia
    let x := limbU a.array sa na ha (hsa ▸ hna ▸ limbU_bound a ha) i hi
    sqrRowsAcc a ha hn sa na hsa hna
      (addRow (a.slice (i.toNat + 1) a.size) a.array (slice_from_array a _).symm ha
        (sa + i + 1) (na - i - 1)
        (by
          apply USize.toNat_inj.1
          rw [slice_from_start a _ hi', toNat_toUSize (by lia), toNat_add_usize, toNat_add_usize,
            hsa, toNat_toUSize (by lia)]
          · lia
          · rw [hsa, toNat_toUSize (by lia)]; lia
          · rw [toNat_add_usize] <;> rw [hsa, toNat_toUSize (by lia)] <;> (try simp) <;> lia)
        (by
          apply USize.toNat_inj.1
          rw [UInt32Array.Slice.size_slice, toNat_toUSize (by lia), USize.toNat_sub_of_le,
            USize.toNat_sub_of_le, hna']
          · (try simp) <;> lia
          · rw [USize.le_iff_toNat_le]; (try simp) <;> lia
          · rw [USize.le_iff_toNat_le, USize.toNat_sub_of_le _ _ (by
                rw [USize.le_iff_toNat_le]; lia)]
            (try simp) <;> lia)
        x acc (i + i + 1) (by
          rw [toNat_add_usize, toNat_add_usize, USize.toNat_sub_of_le, USize.toNat_sub_of_le,
            hna', hacc]
          · (try simp) <;> lia
          · rw [USize.le_iff_toNat_le]; (try simp) <;> lia
          · rw [USize.le_iff_toNat_le, USize.toNat_sub_of_le _ _ (by
                rw [USize.le_iff_toNat_le]; lia)]
            (try simp) <;> lia
          · (try simp) <;> lia
          · rw [toNat_add_usize (by lia)]; (try simp) <;> lia))
      (by rw [size_addRow, hacc]) (i + 1)
  else acc
termination_by na.toNat - i.toNat
decreasing_by
  have : i.toNat < na.toNat := hi
  rw [toNat_add_usize (by have := na.toNat_lt_size; simp; lia)]; simp; lia


/-- The arithmetic of one row of the square, with `Q = β²ⁱ`. -/
private theorem sqr_row_arith (S V Q x T₁ D : Nat) (hS : S = V + Q * 2 ^ 32 * (x * T₁)) :
    2 * S + Q * 2 ^ 64 * (T₁ * T₁) + (D + Q * (x * x)) =
      2 * V + Q * ((x + 2 ^ 32 * T₁) * (x + 2 ^ 32 * T₁)) + D := by
  subst hS
  have h64 : (2 : Nat) ^ 64 = 2 ^ 32 * 2 ^ 32 := by decide
  rw [h64]
  generalize (2 : Nat) ^ 32 = β
  simp only [Nat.mul_add, Nat.add_mul, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
  lia

private theorem sqrRowsAcc_spec (a : UInt32Array.Slice) (ha : a.array.size < USize.size)
    (hn : 2 * a.size < USize.size) (ha31 : a.size < 2 ^ 30) (sa na : USize)
    (hsa : sa = a.start.toUSize) (hna : na = a.size.toUSize) :
    ∀ d (i : USize) (acc : UInt64Array) (hacc : acc.size = 2 * a.size),
      a.size - i.toNat = d → i.toNat ≤ a.size →
      (∀ v ∈ acc.toList, v.toNat ≤ 2 ^ 33 * i.toNat) →
      2 * accVal acc.toList + 2 ^ (64 * i.toNat) *
          (ofLimbs (a.copy.toList.drop i.toNat) * ofLimbs (a.copy.toList.drop i.toNat)) +
          sqDiag (a.copy.toList.take i.toNat) = toNat a * toNat a →
      let res := sqrRowsAcc a ha hn sa na hsa hna acc hacc i
      res.size = 2 * a.size ∧ 2 * accVal res.toList + sqDiag a.copy.toList = toNat a * toNat a ∧
        ∀ v ∈ res.toList, v.toNat ≤ 2 ^ 33 * a.size := by
  have hna' : na.toNat = a.size := by rw [hna, toNat_toUSize (by lia)]
  intro d
  induction d with
  | zero =>
    intro i acc hacc hd hi hall hval
    have hia : i.toNat = a.size := by lia
    rw [sqrRowsAcc, dite_eq_right (by rw [USize.lt_iff_toNat_lt, hna']; lia)]
    have hd : a.copy.toList.drop i.toNat = [] := List.drop_of_length_le (by simp; lia)
    have ht : a.copy.toList.take i.toNat = a.copy.toList := List.take_of_length_le (by simp; lia)
    simp only [hd, ht, ofLimbs_nil, Nat.mul_zero, Nat.add_zero] at hval
    exact ⟨hacc, hval, by rw [← hia]; exact hall⟩
  | succ d ih =>
    intro i acc hacc hd hi hall hval
    have hia : i.toNat < a.size := by clear ih; lia
    have hlt : i < na := by rw [USize.lt_iff_toNat_lt, hna']; exact hia
    rw [sqrRowsAcc, dite_eq_left hlt]
    dsimp only
    have hxa : limbU a.array sa na ha (hsa ▸ hna ▸ limbU_bound a ha) i hlt = a[i.toNat] := by
      subst hsa hna; exact limbU_eq' a ha i hlt hia
    have hi1 : (i + 1).toNat = i.toNat + 1 := by
      rw [toNat_add_usize (by have := na.toNat_lt_size; simp; clear ih; lia)]; simp
    have hbase : (i + i + 1).toNat = 2 * i.toNat + 1 := by
      have h1 : (i + i).toNat = i.toNat + i.toNat := toNat_add_usize (by clear ih; lia)
      rw [toNat_add_usize (by rw [h1, USize.toNat_one]; clear ih; lia), h1, USize.toNat_one]
      lia
    obtain ⟨hv, hbd⟩ := addRow_spec (a.slice (i.toNat + 1) a.size) a.array _ ha _ _ _ _ _ acc
      (i + i + 1) (2 ^ 33 * i.toNat)
      (by
        clear ih
        have h1 : i.toNat + 1 < 2 ^ 31 := by lia
        have := Nat.mul_lt_mul_of_pos_left h1 (show 0 < 2 ^ 33 by decide)
        rw [Nat.mul_succ] at this
        lia)
      (by rw [hbase, hacc, UInt32Array.Slice.size_slice]; clear ih; lia)
      (by rw [hacc]; exact hn) hall _
    have hd' : a.size - (i + 1).toNat = d := by rw [hi1, Nat.sub_succ, hd]; rfl
    refine ih (i + 1) _ _ hd' (by rw [hi1]; exact hia)
      (fun v hv' => by have := hbd v hv'; rw [hi1, Nat.mul_succ]; exact this) ?_
    rw [hv, hi1, ← hval, hxa, hbase, toNat_slice_from_drop, ofLimbs_drop_copy a i.toNat hia]
    have htake : a.copy.toList.take (i.toNat + 1) =
        a.copy.toList.take i.toNat ++ [a.copy.toList[i.toNat]'(by simp; lia)] :=
      List.take_succ_eq_append_getElem (by simp; lia)
    have hget : a.copy.toList[i.toNat]'(by simp; lia) = a[i.toNat] := by
      rw [UInt32Array.getElem_toList, UInt32Array.Slice.getElem_copy]
    rw [htake, sqDiag_append, hget, List.length_take, Nat.min_eq_left (by simp; lia)]
    simp only [sqDiag, Nat.mul_zero, Nat.add_zero]
    have hp1 : 2 ^ (32 * (2 * i.toNat + 1)) = 2 ^ (64 * i.toNat) * 2 ^ 32 := by
      rw [← Nat.pow_add]; congr 1; lia
    have hp2 : 2 ^ (64 * (i.toNat + 1)) = 2 ^ (64 * i.toNat) * 2 ^ 64 := by
      rw [Nat.mul_succ, Nat.pow_add]
    rw [hp1, hp2]
    exact sqr_row_arith _ _ _ _ _ _ rfl


/-- The step of the last pass at limb `k`: twice accumulator `k`, the diagonal and the carry. -/
@[inline] def carrySqStep (acc : UInt64Array) (n : USize) (hn : n.toNat ≤ acc.size)
    (arr : UInt32Array) (st na : USize) (has : arr.size < USize.size)
    (h : st.toNat + na.toNat ≤ arr.size) (hlen : n.toNat ≤ 2 * na.toNat) (k : USize)
    (hk : k.toNat < n.toNat) (_ : UInt32) (c : UInt64) : UInt32 × UInt64 :=
  let v := acc.uget k (by lia) + acc.uget k (by lia) +
    (diagLimbU arr st na has h n hlen k hk).toUInt64 + c
  (v.toUInt32, v >>> 32)

private theorem carry_sq_arith (S R Q A d c v T E : Nat) (hv : v = A + A + d + c)
    (hset : S = R + Q * (v % 2 ^ 32)) :
    S + Q * 2 ^ 32 * (v / 2 ^ 32 + (2 * T + E)) =
      R + Q * (c + (2 * (A + 2 ^ 32 * T) + (d + 2 ^ 32 * E))) := by
  have hdm := Nat.div_add_mod v (2 ^ 32)
  rw [hset]
  have : Q * (v % 2 ^ 32) + Q * 2 ^ 32 * (v / 2 ^ 32 + (2 * T + E)) =
      Q * (v % 2 ^ 32 + 2 ^ 32 * (v / 2 ^ 32)) + Q * (2 ^ 32 * (2 * T + E)) := by
    simp only [Nat.mul_add, Nat.mul_assoc]; lia
  rw [Nat.add_assoc, this, Nat.mod_add_div, hv]
  simp only [Nat.mul_add]; lia

private theorem carrySqLoop_spec (a : UInt32Array.Slice) (has : a.array.size < USize.size)
    (acc : UInt64Array) (N : Nat) (hN : N = acc.size) (hN2 : N = 2 * a.size)
    (hNU : N < USize.size) (E : Nat) (hE : 2 * E + 2 ^ 36 < 2 ^ 64)
    (hall : ∀ k (hk : k < acc.size), acc[k].toNat ≤ E) (s len : Nat) (hs : s = 0)
    (hl : N = len) :
    ∀ d j (r : UInt32Array) (c : UInt64), N - j = d → ∀ (h : s + len ≤ r.size)
      (hlen : len ≤ N.toUSize.toNat), j ≤ N → c.toNat ≤ 2 ^ 35 →
      (∀ k (hk : k < r.size), j ≤ k → r[k] = 0) →
      let res := UInt32Array.foldInPlace.loop N.toUSize
        (carrySqStep acc N.toUSize (by rw [toNat_toUSize hNU]; lia) a.array a.start.toUSize
          a.size.toUSize has (limbU_bound a has)
          (by rw [toNat_toUSize hNU, toNat_toUSize (by lia)]; lia)) s len r h hlen j c
      res.1.size = r.size ∧
        ofLimbs res.1.toList + 2 ^ (32 * N) * res.2.toNat =
          ofLimbs r.toList + 2 ^ (32 * j) * (c.toNat + (2 * accVal (acc.toList.drop j) +
            ofLimbs ((diagLimbs a.copy.toList).drop j))) := by
  subst hs hl
  intro d
  induction d with
  | zero =>
    intro j r c hd h hlen hj hc hz
    have hjN : j = N := by lia
    subst hjN
    rw [UInt32Array.foldInPlace.loop, dite_eq_right (by lia)]
    have hd₁ : acc.toList.drop j = [] := List.drop_of_length_le (by simp; lia)
    have hd₂ : (diagLimbs a.copy.toList).drop j = [] := List.drop_of_length_le (by simp; lia)
    simp only [hd₁, hd₂, accVal, ofLimbs_nil, Nat.mul_zero, Nat.add_zero]
    exact ⟨trivial, trivial⟩
  | succ d ih =>
    intro j r c hd h hlen hj hc hz
    have hjN : j < N := by clear ih; lia
    rw [UInt32Array.foldInPlace.loop, dite_eq_left hjN]
    dsimp only
    have hjU : j < USize.size := by clear ih; lia
    have hdg := diagLimbU_eq a has N.toUSize
      (by rw [toNat_toUSize hNU, toNat_toUSize (by lia)]; lia) j
      (by rw [toNat_toUSize hjU, toNat_toUSize hNU]; exact hjN) (by clear ih; lia) hjU
    simp only [Nat.zero_add, carrySqStep, UInt64Array.uget_eq_getElem, toNat_toUSize hjU, hdg]
    have hjacc : j < acc.size := by clear ih; lia
    have hA := hall j hjacc
    have hDl := (diagLimb a j).toNat_lt
    have hv : (acc[j] + acc[j] + (diagLimb a j).toUInt64 + c).toNat =
        acc[j].toNat + acc[j].toNat + (diagLimb a j).toNat + c.toNat := by
      rw [UInt64.toNat_add, UInt64.toNat_add, UInt64.toNat_add, UInt32.toNat_toUInt64]
      rw [Nat.mod_eq_of_lt (by clear ih; lia), Nat.mod_eq_of_lt (by clear ih; lia),
        Nat.mod_eq_of_lt (by clear ih; lia)]
    have hc' : ((acc[j] + acc[j] + (diagLimb a j).toUInt64 + c) >>> 32).toNat ≤ 2 ^ 35 := by
      rw [UInt64.toNat_shiftRight, hv]
      simp only [UInt64.reduceToNat, Nat.reduceMod, Nat.shiftRight_eq_div_pow]
      exact Nat.le_of_lt (Nat.div_lt_of_lt_mul (by clear ih; lia))
    have hjr : j < r.size := by clear ih; lia
    obtain ⟨ih₁, ih₂⟩ := ih (j + 1)
      (r.set j (acc[j] + acc[j] + (diagLimb a j).toUInt64 + c).toUInt32 hjr)
      ((acc[j] + acc[j] + (diagLimb a j).toUInt64 + c) >>> 32) (by clear ih; lia)
      (by simpa using h) hlen (by clear ih; lia) hc'
      (fun k hk hjk => by
        rw [UInt32Array.getElem_set, ite_eq_right (by clear ih; lia)]
        exact hz k (by simpa using hk) (by clear ih; lia))
    refine ⟨by rw [ih₁]; simp, ?_⟩
    rw [ih₂]
    have hset := ofLimbs_set r.toList j (acc[j] + acc[j] + (diagLimb a j).toUInt64 + c).toUInt32
      (by simpa using hjr)
    have hr0 : r.toList[j]'(by simpa using hjr) = 0 := by
      rw [UInt32Array.getElem_toList]; exact hz j hjr (Nat.le_refl _)
    rw [hr0, UInt32.toNat_zero, Nat.mul_zero, Nat.add_zero, UInt64.toNat_toUInt32, hv] at hset
    have hdd : ((diagLimbs a.copy.toList).getD j 0) = diagLimb a j := (diagLimb_eq a j).symm
    rw [UInt32Array.toList_set, accVal_drop acc.toList j (by simpa using hjacc),
      getElem_toList64, ofLimbs_drop (diagLimbs a.copy.toList) j, hdd,
      UInt64.toNat_shiftRight, hv]
    simp only [UInt64.reduceToNat, Nat.reduceMod, Nat.shiftRight_eq_div_pow]
    have hpow : 2 ^ (32 * (j + 1)) = 2 ^ (32 * j) * 2 ^ 32 := by rw [Nat.mul_succ, Nat.pow_add]
    rw [hpow]
    exact carry_sq_arith _ _ _ _ _ _ _ _ _ rfl hset

/-- The conditions under which `sqrRowsMul` runs: a nonempty operand, and sizes that fit. -/
@[expose] public def SqrRowsOK (a : UInt32Array.Slice) : Prop :=
  0 < a.size ∧ a.size < 2 ^ 26 ∧ a.array.size < 4294967295

public instance (a : UInt32Array.Slice) : Decidable (SqrRowsOK a) := by
  unfold SqrRowsOK; infer_instance

private theorem size_sqrRowsAcc (a : UInt32Array.Slice) (ha : a.array.size < USize.size)
    (hn : 2 * a.size < USize.size) (sa na : USize) (hsa hna) :
    ∀ d (i : USize) (acc : UInt64Array) (hacc : acc.size = 2 * a.size),
      na.toNat - i.toNat = d → (sqrRowsAcc a ha hn sa na hsa hna acc hacc i).size = 2 * a.size := by
  intro d
  induction d with
  | zero =>
    intro i acc hacc hd
    rw [sqrRowsAcc, dite_eq_right (by rw [USize.lt_iff_toNat_lt]; lia)]
    exact hacc
  | succ d ih =>
    intro i acc hacc hd
    have hlt : i < na := by rw [USize.lt_iff_toNat_lt]; clear ih; lia
    rw [sqrRowsAcc, dite_eq_left hlt]
    exact ih _ _ _ (by
      rw [toNat_add_usize (by have := na.toNat_lt_size; simp; clear ih; lia)]; simp; clear ih; lia)

/-- All `2 * a.size` limbs of `a * a`, by rows into wide accumulators, then `2 S + D`. -/
public def sqrRowsMul (a : UInt32Array.Slice) (h : SqrRowsOK a) : UInt32Array :=
  have ha := lt_usizeSize h.2.2
  have hn : 2 * a.size < USize.size := lt_usizeSize (by have := h.2.1; lia)
  (UInt32Array.replicate (2 * a.size) 0).foldInPlaceThen 0 (2 * a.size).toUSize 0
    (carrySqStep (sqrRowsAcc a ha hn a.start.toUSize a.size.toUSize rfl rfl
        (UInt64Array.replicate (2 * a.size) 0) (by simp) 0)
      (2 * a.size).toUSize
      (by rw [toNat_toUSize hn, size_sqrRowsAcc a ha hn _ _ _ _ _ 0 _ _ rfl]
          exact Nat.le_refl _)
      a.array a.start.toUSize a.size.toUSize ha (limbU_bound a ha)
      (by rw [toNat_toUSize hn, toNat_toUSize (by lia)]; exact Nat.le_refl _))
    (fun r _ => r) (by
      simp only [UInt32Array.size_replicate, USize.toNat_zero, Nat.zero_add, toNat_toUSize hn]
      exact Nat.le_refl _)

public theorem sqrRowsMul_spec (a : UInt32Array.Slice) (h : SqrRowsOK a) :
    (sqrRowsMul a h).size = a.size + a.size ∧ toNat (sqrRowsMul a h) = toNat a * toNat a := by
  have ha := lt_usizeSize h.2.2
  have hn : 2 * a.size < USize.size := lt_usizeSize (by have := h.2.1; lia)
  have ha30 : a.size < 2 ^ 30 := by have := h.2.1; lia
  have hrep : (UInt64Array.replicate (2 * a.size) 0).toList =
      List.replicate (2 * a.size) 0 := by
    simp [← UInt64Array.toList_data]
  obtain ⟨hs, hv, hbd⟩ := sqrRowsAcc_spec a ha hn ha30 _ _ rfl rfl a.size 0
    (UInt64Array.replicate (2 * a.size) 0) (by simp) (by simp) (Nat.zero_le _)
    (by intro v hv; rw [hrep] at hv; rw [(List.mem_replicate.1 hv).2]; simp)
    (by rw [hrep, accVal_replicate_zero]; simp [sqDiag, toNat])
  simp only [sqrRowsMul, UInt32Array.foldInPlaceThen_eq, UInt32Array.foldInPlace]
  have hE : 2 * (2 ^ 33 * a.size) + 2 ^ 36 < 2 ^ 64 := by
    have h1 : a.size < 2 ^ 26 := h.2.1
    have := Nat.mul_lt_mul_of_pos_left h1 (show 0 < 2 * 2 ^ 33 by decide)
    lia
  obtain ⟨h₁, h₂⟩ := carrySqLoop_spec a ha
    (sqrRowsAcc a ha hn a.start.toUSize a.size.toUSize rfl rfl
      (UInt64Array.replicate (2 * a.size) 0) (by simp) 0)
    (2 * a.size) hs.symm rfl hn (2 ^ 33 * a.size) hE
    (fun k hk => hbd _ (List.mem_iff_getElem.2 ⟨k, by simpa using hk, getElem_toList64 _ _ _⟩))
    (USize.toNat 0) ((2 * a.size).toUSize.toNat) rfl (toNat_toUSize hn).symm
    (2 * a.size) 0 (UInt32Array.replicate (2 * a.size) 0) 0 (Nat.sub_zero _)
    (by
      simp only [USize.toNat_zero, Nat.zero_add, toNat_toUSize hn, UInt32Array.size_replicate]
      exact Nat.le_refl _)
    (Nat.le_refl _) (Nat.zero_le _) (by simp) (fun k hk _ => by simp)
  simp only [UInt32Array.toList_replicate, ofLimbs_replicate_zero, Nat.mul_zero, Nat.zero_add,
    List.drop_zero, UInt64.toNat_zero, Nat.pow_zero, Nat.one_mul, ofLimbs_diagLimbs, hv] at h₂
  revert h₁ h₂
  generalize UInt32Array.foldInPlace.loop (2 * a.size).toUSize
    (carrySqStep (sqrRowsAcc a ha hn a.start.toUSize a.size.toUSize rfl rfl
        (UInt64Array.replicate (2 * a.size) 0) (by simp) 0) (2 * a.size).toUSize _ a.array
      a.start.toUSize a.size.toUSize ha (limbU_bound a ha) _) (USize.toNat 0)
    ((2 * a.size).toUSize.toNat) (UInt32Array.replicate (2 * a.size) 0) _ _ 0 0 = R
  intro h₁ h₂
  have hlt : toNat a * toNat a < 2 ^ (32 * (2 * a.size)) := by
    rw [show 32 * (2 * a.size) = 32 * a.size + 32 * a.size by lia, Nat.pow_add]
    exact Nat.mul_lt_mul'' (toNat_lt a) (toNat_lt a)
  have hR2 : R.2.toNat = 0 := by
    rcases Nat.eq_zero_or_pos R.2.toNat with h0 | h0
    · exact h0
    · have : 2 ^ (32 * (2 * a.size)) ≤ 2 ^ (32 * (2 * a.size)) * R.2.toNat :=
        Nat.le_mul_of_pos_right _ h0
      lia
  rw [hR2, Nat.mul_zero, Nat.add_zero] at h₂
  exact ⟨by rw [h₁]; simp; lia, by rw [toNat_toSlice, h₂]⟩

/-! ## The compiled square

`sqrBasecaseFast` squares by rows into wide accumulators (`sqrRowsMul`) from 16 limbs, and by
Comba's method (`csqMul`) below, whose lower fixed cost makes it up to 29% faster there.
`@[csimp]` makes the compiler use it in place of `sqrBasecase`: both compute all `2 * a.size` limbs
of the square, and limbs of a given length are determined by their value.
-/

/-- `sqrBasecase`, by rows into wide accumulators or by Comba's method when the size allows it. -/
public def sqrBasecaseFast (a : UInt32Array.Slice) : UInt32Array :=
  if h : 16 ≤ a.size ∧ SqrRowsOK a then sqrRowsMul a h.2
  else if h : SqrOK a then csqMul a h
  else sqrBasecase a

@[csimp] public theorem sqrBasecase_eq_sqrBasecaseFast : @sqrBasecase = @sqrBasecaseFast := by
  funext a
  unfold sqrBasecaseFast
  obtain ⟨hs', hv'⟩ := sqrBasecase_spec a
  split
  · rename_i h
    obtain ⟨hs, hv⟩ := sqrRowsMul_spec a h.2
    apply UInt32Array.toList_inj.1
    apply ofLimbs_inj_of_length (by simp [hs, hs'])
    rw [← toNat_toSlice, ← toNat_toSlice, hv', hv]
  · split
    · rename_i h
      obtain ⟨hs, hv⟩ := csqMul_spec a h
      apply UInt32Array.toList_inj.1
      apply ofLimbs_inj_of_length (by simp [hs, hs'])
      rw [← toNat_toSlice, ← toNat_toSlice, hv', hv]
    · rfl

end MPN
