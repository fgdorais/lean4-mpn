/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import MPN.Basic
public import ScalarArray.UInt64

/-!
# Schoolbook multiplication by rows into wide accumulators

`rowsMul a b` adds the rows `aᵢ b` into an array of `UInt64` accumulators, one per limb of the
product, and propagates the carries in one pass at the end. Within a row, accumulator `i + j`
receives the low half of `aᵢ b_j` and the high half of `aᵢ b_{j-1}`: no carry goes from one
product to the next, so the C compiler vectorizes the row (two products per instruction with
SSE2, four with AVX2), where the columns of Comba's method (`Mul.Comba`) need a sum across the
vector after each column. Each accumulator gains less than `2³³` per row, so fewer than `2³¹`
rows cannot overflow it.

The value of the accumulators is `accVal`, the limbs with base `2³²` but each up to `2⁶⁴ - 1`.
-/

open ScalarArray

namespace MPN

/-! ## Wide limbs -/

/-- The value of wide limbs at base `2³²`: `v₀ + 2³² v₁ + 2⁶⁴ v₂ + ⋯`. -/
@[expose] public def accVal : List UInt64 → Nat
  | [] => 0
  | v :: l => v.toNat + 2 ^ 32 * accVal l

private theorem accVal_set (l : List UInt64) (k : Nat) (v : UInt64) (h : k < l.length) :
    accVal (l.set k v) + 2 ^ (32 * k) * l[k].toNat = accVal l + 2 ^ (32 * k) * v.toNat := by
  induction l generalizing k with
  | nil => simp at h
  | cons d l ih =>
    cases k with
    | zero => simp [accVal]; lia
    | succ k =>
      have := ih k (by simpa using h)
      simp only [List.set_cons_succ, accVal, List.getElem_cons_succ, Nat.mul_add, Nat.mul_one,
        Nat.pow_add]
      grind

public theorem accVal_drop (l : List UInt64) (j : Nat) (hj : j < l.length) :
    accVal (l.drop j) = l[j].toNat + 2 ^ 32 * accVal (l.drop (j + 1)) := by
  rw [List.drop_eq_getElem_cons hj, accVal]

public theorem accVal_replicate_zero (n : Nat) : accVal (List.replicate n 0) = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => simp [List.replicate_succ, accVal, ih]

/-- The limb `j` of a slice and the value of the limbs above it. -/
public theorem ofLimbs_drop_copy (b : UInt32Array.Slice) (j : Nat) (hj : j < b.size) :
    ofLimbs (b.copy.toList.drop j) =
      b[j].toNat + 2 ^ 32 * ofLimbs (b.copy.toList.drop (j + 1)) := by
  rw [ofLimbs_drop, ← getD_eq_getD_toList_copy, UInt32Array.Slice.getD_eq, dite_eq_left hj]

/-! ## A row -/

/--
The step of a row at limb `k` of `b` (the slice `arr[st...st + len]`): `x b_k` into the
accumulator `v`, its low half with the high half `c` of the product before.
-/
@[inline] public def rowStep (arr : UInt32Array) (st len : USize) (has : arr.size < USize.size)
    (h : st.toNat + len.toNat ≤ arr.size) (x : UInt32) (k : USize) (hk : k.toNat < len.toNat)
    (v c : UInt64) : UInt64 × UInt64 :=
  let p := x.toUInt64 * (limbU arr st len has h k hk).toUInt64
  (v + (p &&& 0xFFFFFFFF) + c, p >>> 32)

/-- The bounds under which a row runs: `b` fits `USize` and the row fits the accumulators. -/
private theorem rowStep_val (x : UInt64) (hx : x.toNat < 2 ^ 32) (y : UInt32) (v c : UInt64)
    (M : Nat) (hM : M + 2 ^ 33 < 2 ^ 64) (hv : v.toNat ≤ M) (hc : c.toNat < 2 ^ 32) :
    (v + ((x * y.toUInt64) &&& 0xFFFFFFFF) + c).toNat =
        v.toNat + (x.toNat * y.toNat) % 2 ^ 32 + c.toNat ∧
      ((x * y.toUInt64) >>> 32).toNat = (x.toNat * y.toNat) / 2 ^ 32 ∧
      (x.toNat * y.toNat) / 2 ^ 32 < 2 ^ 32 := by
  have hy := y.toNat_lt
  have hp : (x * y.toUInt64).toNat = x.toNat * y.toNat := by
    rw [UInt64.toNat_mul, UInt32.toNat_toUInt64]
    exact Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le (Nat.mul_lt_mul'' hx hy) (by decide))
  have hlo : ((x * y.toUInt64) &&& 0xFFFFFFFF).toNat = (x.toNat * y.toNat) % 2 ^ 32 := by
    rw [UInt64.toNat_and, hp]
    exact Nat.and_two_pow_sub_one_eq_mod _ 32
  have hhi : ((x * y.toUInt64) >>> 32).toNat = (x.toNat * y.toNat) / 2 ^ 32 := by
    rw [UInt64.toNat_shiftRight, hp]
    simp [Nat.shiftRight_eq_div_pow]
  have hlt : (x.toNat * y.toNat) / 2 ^ 32 < 2 ^ 32 :=
    Nat.div_lt_of_lt_mul (Nat.mul_lt_mul'' hx hy)
  have hm := Nat.mod_lt (x.toNat * y.toNat) (show 0 < 2 ^ 32 by decide)
  refine ⟨?_, hhi, hlt⟩
  rw [UInt64.toNat_add, UInt64.toNat_add, hlo]
  rw [Nat.mod_eq_of_lt (by lia : v.toNat + x.toNat * y.toNat % 2 ^ 32 < 2 ^ 64)]
  exact Nat.mod_eq_of_lt (by lia)

/-- The arithmetic of one step of a row, with `S` the new accumulators and `V` the old ones. -/
private theorem row_arith (S V Q a c X y T : Nat)
    (hset : S + Q * a = V + Q * (a + X * y % 2 ^ 32 + c)) :
    S + Q * 2 ^ 32 * (X * y / 2 ^ 32 + X * T) = V + Q * (c + X * (y + 2 ^ 32 * T)) := by
  have hdm := Nat.div_add_mod (X * y) (2 ^ 32)
  have h₁ : S = V + Q * (X * y % 2 ^ 32 + c) := by
    simp only [Nat.mul_add] at hset; lia
  rw [h₁]
  have h₂ : Q * (X * y % 2 ^ 32 + c) + Q * 2 ^ 32 * (X * y / 2 ^ 32 + X * T) =
      Q * (c + (X * y % 2 ^ 32 + 2 ^ 32 * (X * y / 2 ^ 32)) + 2 ^ 32 * (X * T)) := by
    simp only [Nat.mul_add, Nat.mul_assoc]; lia
  rw [Nat.add_assoc, h₂, Nat.mod_add_div, Nat.mul_add X y, Nat.mul_left_comm (2 ^ 32) X T]
  simp only [Nat.mul_add]; lia

/-- The loop of a row from limb `j` of `b`, with the high half `c` of the product before. -/
private theorem rowLoop_spec (b : UInt32Array.Slice) (has : b.array.size < USize.size)
    (x : UInt32) (base M : Nat) (hM : M + 2 ^ 33 < 2 ^ 64)
    (len : Nat) (hn : len = b.size) (hlen : len ≤ b.size.toUSize.toNat) :
    ∀ d j (acc : UInt64Array) (c : UInt64), b.size - j = d → ∀ (h : base + len ≤ acc.size),
      j ≤ b.size → c.toNat < 2 ^ 32 →
      (∀ k (hk : k < acc.size), base + j ≤ k → acc[k].toNat ≤ M) →
      (∀ k (hk : k < acc.size), acc[k].toNat ≤ M + 2 ^ 33) →
      let res := UInt64Array.foldInPlace.loop b.size.toUSize
        (rowStep b.array b.start.toUSize b.size.toUSize has (limbU_bound b has) x) base len
        acc h hlen j c
      res.1.size = acc.size ∧
        accVal res.1.toList + 2 ^ (32 * (base + b.size)) * res.2.toNat =
          accVal acc.toList + 2 ^ (32 * (base + j)) *
            (c.toNat + x.toUInt64.toNat * ofLimbs (b.copy.toList.drop j)) ∧
        res.2.toNat < 2 ^ 32 ∧
        (∀ k (hk : k < res.1.size), res.1[k].toNat ≤ M + 2 ^ 33) ∧
        (∀ k (hk : k < acc.size) (hk' : k < res.1.size), base + b.size ≤ k →
          res.1[k] = acc[k]) := by
  subst hn
  have hx : x.toUInt64.toNat < 2 ^ 32 := by rw [UInt32.toNat_toUInt64]; exact x.toNat_lt
  intro d
  induction d with
  | zero =>
    intro j acc c hd h hj hc hlow hall
    have hjb : j = b.size := by lia
    subst hjb
    rw [UInt64Array.foldInPlace.loop, dite_eq_right (by lia)]
    have hd : b.copy.toList.drop b.size = [] := List.drop_of_length_le (by simp)
    simp only [hd, ofLimbs_nil, Nat.mul_zero, Nat.add_zero]
    exact ⟨trivial, trivial, hc, hall, fun _ _ _ _ => trivial⟩
  | succ d ih =>
    intro j acc c hd h hj hc hlow hall
    have hjb : j < b.size := by clear ih; lia
    rw [UInt64Array.foldInPlace.loop, dite_eq_left hjb]
    dsimp only
    have hy : limbU b.array b.start.toUSize b.size.toUSize has (limbU_bound b has) j.toUSize
        (by
          have := b.stop_le_array_size; have := b.start_le_stop; have := b.size_eq
          clear ih; rw [toNat_toUSize (by lia), toNat_toUSize (by lia)]; lia) = b[j] :=
      limbU_eq b has j _ hjb
    simp only [rowStep, hy]
    have hk : base + j < acc.size := by clear ih; lia
    obtain ⟨hv, hhi, hlt⟩ := rowStep_val x.toUInt64 hx b[j] acc[base + j] c M hM
      (hlow _ hk (by clear ih; lia)) hc
    obtain ⟨ih₁, ih₂, ih₃, ih₄, ih₅⟩ := ih (j + 1)
      (acc.set (base + j) (acc[base + j] + ((x.toUInt64 * b[j].toUInt64) &&& 0xFFFFFFFF) + c) hk)
      ((x.toUInt64 * b[j].toUInt64) >>> 32) (by clear ih; lia) (by simpa using h) (by clear ih; lia)
      (by rw [hhi]; exact hlt)
      (fun k hk' hkj => by
        rw [UInt64Array.getElem_set, ite_eq_right (by clear ih; lia)]
        exact hlow k (by simpa using hk') (by clear ih; lia))
      (fun k hk' => by
        rw [UInt64Array.getElem_set]
        split
        · rw [hv]
          have := hlow (base + j) hk (by clear ih; lia)
          have := Nat.mod_lt (x.toUInt64.toNat * b[j].toNat) (show 0 < 2 ^ 32 by decide)
          clear ih; lia
        · exact hall k (by simpa using hk'))
    refine ⟨by rw [ih₁]; simp, ?_, ih₃, ih₄, fun k hk' hk'' hkl => ?_⟩
    · rw [ih₂, hhi]
      have hset := accVal_set acc.toList (base + j)
        (acc[base + j] + ((x.toUInt64 * b[j].toUInt64) &&& 0xFFFFFFFF) + c) (by simpa using hk)
      rw [UInt64Array.toList_set]
      have hgl : acc.toList[base + j]'(by simpa using hk) = acc[base + j] := by
        simp [← UInt64Array.toList_toArray]
      rw [hgl, hv] at hset
      have hdrop := ofLimbs_drop_copy b j hjb
      have hpow : 2 ^ (32 * (base + (j + 1))) = 2 ^ (32 * (base + j)) * 2 ^ 32 := by
        rw [← Nat.add_assoc, Nat.mul_succ, Nat.pow_add]
      rw [hpow, hdrop]
      exact row_arith _ _ _ _ _ _ _ _ hset
    · rw [ih₅ k (by simpa using hk') hk'' hkl, UInt64Array.getElem_set,
        ite_eq_right (by clear ih; lia)]

public theorem getElem_toList64 (a : UInt64Array) (k : Nat) (h : k < a.toList.length) :
    a.toList[k] = a[k]'(by simpa using h) := by
  simp [← UInt64Array.toList_toArray]

private theorem uset64_eq_set (a : UInt64Array) (i : USize) (v : UInt64) (h) :
    a.uset i v h = a.set i.toNat v h := by
  cases a; rfl

/--
`acc + 2^(32 base) x b`, the row of `x`: the loop over `b`, then the last high half into the
accumulator above it, `base + b.size`. The limbs are read from `arr`, the array of `b`, at `sb`;
`b` itself only serves the specification.
-/
@[inline] public def addRow (b : UInt32Array.Slice) (arr : UInt32Array) (harr : arr = b.array)
    (has : arr.size < USize.size) (sb nb : USize) (hsb : sb = b.start.toUSize)
    (hnb : nb = b.size.toUSize) (x : UInt32) (acc : UInt64Array) (base : USize)
    (h : base.toNat + nb.toNat ≤ acc.size) : UInt64Array :=
  let t := base + nb
  acc.foldInPlaceThen base nb 0
    (rowStep arr sb nb has (harr ▸ hsb ▸ hnb ▸ limbU_bound b (harr ▸ has)) x)
    (fun acc c => if ht : t.toNat < acc.size then acc.uset t (acc.uget t ht + c) ht else acc) h

public theorem size_addRow (b : UInt32Array.Slice) (arr : UInt32Array) (harr)
    (has : arr.size < USize.size) (sb nb : USize) (hsb hnb) (x : UInt32) (acc : UInt64Array)
    (base : USize) (h) :
    (addRow b arr harr has sb nb hsb hnb x acc base h).size = acc.size := by
  subst harr hsb hnb
  simp only [addRow, UInt64Array.foldInPlaceThen_eq]
  split
  · simp
  · simp

private theorem slice_size_lt (b : UInt32Array.Slice) (has : b.array.size < USize.size) :
    b.size < USize.size := by
  have := b.stop_le_array_size; have := b.start_le_stop; have := b.size_eq; lia

/-- The store that ends a row, when its index is in bounds. -/
private theorem finalStore_eq (R : UInt64Array) (c : UInt64) (t : USize) (tn : Nat)
    (ht : t.toNat = tn) (htR : tn < R.size) :
    (if h : t.toNat < R.size then R.uset t (R.uget t h + c) h else R) =
      R.set tn (R[tn] + c) htR := by
  subst ht
  rw [dite_eq_left htR, uset64_eq_set, UInt64Array.uget_eq_getElem]

public theorem addRow_spec (b : UInt32Array.Slice) (arr : UInt32Array) (harr)
    (has : arr.size < USize.size) (sb nb : USize) (hsb hnb)
    (x : UInt32) (acc : UInt64Array) (base : USize) (M : Nat)
    (hM : M + 2 ^ 33 < 2 ^ 64) (hfit : base.toNat + b.size < acc.size)
    (hacc : acc.size < USize.size) (hall' : ∀ v ∈ acc.toList, v.toNat ≤ M) (h) :
    accVal (addRow b arr harr has sb nb hsb hnb x acc base h).toList =
        accVal acc.toList + 2 ^ (32 * base.toNat) * (x.toNat * toNat b) ∧
      ∀ v ∈ (addRow b arr harr has sb nb hsb hnb x acc base h).toList, v.toNat ≤ M + 2 ^ 33 := by
  subst harr hsb hnb
  have hall : ∀ k (hk : k < acc.size), acc[k].toNat ≤ M := fun k hk =>
    hall' _ (List.mem_iff_getElem.2 ⟨k, by simpa using hk, by simp [← UInt64Array.toList_toArray]⟩)
  have hbs := slice_size_lt b has
  have hnb : b.size.toUSize.toNat = b.size := toNat_toUSize hbs
  have ht : (base + b.size.toUSize).toNat = base.toNat + b.size := by
    rw [toNat_add_usize (by rw [hnb]; lia), hnb]
  simp only [addRow, UInt64Array.foldInPlaceThen_eq]
  have hsp := rowLoop_spec b has x base.toNat M hM _ hnb (Nat.le_refl _) b.size 0 acc 0
    (by lia) h (Nat.zero_le _) (by simp) (fun k hk _ => hall k hk)
    (fun k hk => by have := hall k hk; lia)
  obtain ⟨h₁, h₂, h₃, h₄, h₅⟩ := hsp
  have htR : base.toNat + b.size < (UInt64Array.foldInPlace.loop b.size.toUSize
      (rowStep b.array b.start.toUSize b.size.toUSize has (limbU_bound b has) x) base.toNat
      b.size.toUSize.toNat acc h (Nat.le_refl _) 0 (0 : UInt64)).1.size := by rw [h₁]; exact hfit
  have hL : acc.foldInPlace base b.size.toUSize 0
      (rowStep b.array b.start.toUSize b.size.toUSize has (limbU_bound b has) x) h =
      UInt64Array.foldInPlace.loop b.size.toUSize
        (rowStep b.array b.start.toUSize b.size.toUSize has (limbU_bound b has) x) base.toNat
        b.size.toUSize.toNat acc h (Nat.le_refl _) 0 (0 : UInt64) := rfl
  rw [hL, finalStore_eq _ _ _ _ ht htR]
  generalize UInt64Array.foldInPlace.loop b.size.toUSize
    (rowStep b.array b.start.toUSize b.size.toUSize has (limbU_bound b has) x) base.toNat
    b.size.toUSize.toNat acc h (Nat.le_refl _) 0 (0 : UInt64) = R at h₁ h₂ h₃ h₄ h₅ htR ⊢
  have hRt : R.1[base.toNat + b.size] = acc[base.toNat + b.size] :=
    h₅ _ hfit htR (Nat.le_refl _)
  have hv : (R.1[base.toNat + b.size] + R.2).toNat =
      R.1[base.toNat + b.size].toNat + R.2.toNat := by
    rw [UInt64.toNat_add, hRt]
    have := hall _ hfit
    exact Nat.mod_eq_of_lt (by lia)
  refine ⟨?_, fun v hv' => ?_⟩
  · have hset := accVal_set R.1.toList (base.toNat + b.size) (R.1[base.toNat + b.size] + R.2)
      (by simpa using htR)
    have hgl : R.1.toList[base.toNat + b.size]'(by simpa using htR) = R.1[base.toNat + b.size] := by
      simp [← UInt64Array.toList_toArray]
    rw [hgl, hv] at hset
    rw [UInt64Array.toList_set]
    simp only [Nat.add_zero, List.drop_zero, UInt32.toNat_toUInt64] at h₂
    rw [toNat]
    lia
  · obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.1 hv'
    have hk' : k < R.1.size := by simpa using hk
    rw [getElem_toList64, UInt64Array.getElem_set]
    split
    · rw [hv, hRt]
      have := hall _ hfit
      lia
    · exact h₄ k hk'

/-! ## All rows -/

/-- Limb `i` of a slice, read with a `USize` index. -/
public theorem limbU_eq' (a : UInt32Array.Slice) (has : a.array.size < USize.size) (i : USize)
    (hi) (hi' : i.toNat < a.size) :
    limbU a.array a.start.toUSize a.size.toUSize has (limbU_bound a has) i hi = a[i.toNat] := by
  obtain ⟨k, hk, rfl⟩ : ∃ k : Nat, k < USize.size ∧ i = k.toUSize :=
    ⟨i.toNat, i.toNat_lt_size, USize.ofNat_toNat.symm⟩
  simp only [toNat_toUSize hk]
  exact limbU_eq a has k hi (by rw [toNat_toUSize hk] at hi'; exact hi')

/--
The rows `a_i b` from `i` on, added into `acc`. The fields of the slices are read once, into
`sa`, `na`, `sb` and `nb`.
-/
def rowsLoop (a b : UInt32Array.Slice) (ha : a.array.size < USize.size)
    (hb : b.array.size < USize.size) (hab : a.size + b.size < USize.size) (sa na sb nb : USize)
    (hsa : sa = a.start.toUSize) (hna : na = a.size.toUSize) (hsb : sb = b.start.toUSize)
    (hnb : nb = b.size.toUSize) (acc : UInt64Array) (hacc : acc.size = a.size + b.size)
    (i : USize) : UInt64Array :=
  if hi : i < na then
    have hi' : i.toNat < a.size := by
      rw [USize.lt_iff_toNat_lt, hna, toNat_toUSize (by lia)] at hi; exact hi
    let x := limbU a.array sa na ha (hsa ▸ hna ▸ limbU_bound a ha) i hi
    rowsLoop a b ha hb hab sa na sb nb hsa hna hsb hnb
      (addRow b b.array rfl hb sb nb hsb hnb x acc i (by
        rw [hnb, toNat_toUSize (by lia)]; lia))
      (by rw [size_addRow, hacc]) (i + 1)
  else acc
termination_by na.toNat - i.toNat
decreasing_by
  have : i.toNat < na.toNat := hi
  rw [toNat_add_usize (by have := na.toNat_lt_size; simp; lia)]; simp; lia

private theorem rowsLoop_spec (a b : UInt32Array.Slice) (ha : a.array.size < USize.size)
    (hb : b.array.size < USize.size) (hab : a.size + b.size < USize.size) (ha31 : a.size < 2 ^ 31)
    (hb0 : 0 < b.size) (sa na sb nb : USize) (hsa : sa = a.start.toUSize)
    (hna : na = a.size.toUSize) (hsb : sb = b.start.toUSize) (hnb : nb = b.size.toUSize) :
    ∀ d (i : USize) (acc : UInt64Array) (hacc : acc.size = a.size + b.size),
      a.size - i.toNat = d → i.toNat ≤ a.size →
      (∀ v ∈ acc.toList, v.toNat ≤ 2 ^ 33 * i.toNat) →
      accVal acc.toList + 2 ^ (32 * i.toNat) * (toNat b * ofLimbs (a.copy.toList.drop i.toNat)) =
        toNat a * toNat b →
      let res := rowsLoop a b ha hb hab sa na sb nb hsa hna hsb hnb acc hacc i
      res.size = a.size + b.size ∧ accVal res.toList = toNat a * toNat b ∧
        ∀ v ∈ res.toList, v.toNat ≤ 2 ^ 33 * a.size := by
  have hna' : na.toNat = a.size := by rw [hna, toNat_toUSize (by lia)]
  intro d
  induction d with
  | zero =>
    intro i acc hacc hd hi hall hval
    have hia : i.toNat = a.size := by lia
    rw [rowsLoop, dite_eq_right (by rw [USize.lt_iff_toNat_lt, hna']; lia)]
    have hd : a.copy.toList.drop i.toNat = [] := List.drop_of_length_le (by simp; lia)
    simp only [hd, ofLimbs_nil, Nat.mul_zero, Nat.add_zero] at hval
    exact ⟨hacc, hval, by rw [← hia]; exact hall⟩
  | succ d ih =>
    intro i acc hacc hd hi hall hval
    have hia : i.toNat < a.size := by clear ih; lia
    have hlt : i < na := by rw [USize.lt_iff_toNat_lt, hna']; exact hia
    rw [rowsLoop, dite_eq_left hlt]
    dsimp only
    have hxa : limbU a.array sa na ha (hsa ▸ hna ▸ limbU_bound a ha) i hlt = a[i.toNat] := by
      subst hsa hna; exact limbU_eq' a ha i hlt hia
    have hi1 : (i + 1).toNat = i.toNat + 1 := by
      rw [toNat_add_usize (by have := na.toNat_lt_size; simp; clear ih; lia)]; simp
    obtain ⟨hv, hbd⟩ := addRow_spec b b.array rfl hb sb nb hsb hnb _ acc i
      (2 ^ 33 * i.toNat)
      (by
        clear ih
        have h1 : i.toNat + 1 < 2 ^ 31 := by lia
        have := Nat.mul_lt_mul_of_pos_left h1 (show 0 < 2 ^ 33 by decide)
        rw [Nat.mul_succ] at this
        lia)
      (by rw [hacc]; clear ih; lia) (by rw [hacc]; exact hab) hall _
    have hd' : a.size - (i + 1).toNat = d := by rw [hi1, Nat.sub_succ, hd]; rfl
    refine ih (i + 1) _ _ hd' (by rw [hi1]; exact hia)
      (fun v hv' => by have := hbd v hv'; rw [hi1, Nat.mul_succ]; exact this) ?_
    rw [hv, hi1, ← hval, ofLimbs_drop_copy a i.toNat hia]
    have hpow : 2 ^ (32 * (i.toNat + 1)) = 2 ^ (32 * i.toNat) * 2 ^ 32 := by
      rw [Nat.mul_succ, Nat.pow_add]
    rw [hpow, hxa]
    generalize 2 ^ (32 * i.toNat) = Q
    generalize ofLimbs (a.copy.toList.drop (i.toNat + 1)) = T
    simp only [Nat.mul_add, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
    lia

/-! ## The carries -/

/-- The step of the carries at limb `k`: accumulator `k` plus the carry `c`. -/
@[inline] def carryStep (acc : UInt64Array) (n : USize) (hn : n.toNat ≤ acc.size) (k : USize)
    (hk : k.toNat < n.toNat) (_ : UInt32) (c : UInt64) : UInt32 × UInt64 :=
  let v := acc.uget k (by lia) + c
  (v.toUInt32, v >>> 32)

private theorem carry_arith (S R Q A c v T : Nat) (hv : v = A + c)
    (hset : S = R + Q * (v % 2 ^ 32)) :
    S + Q * 2 ^ 32 * (v / 2 ^ 32 + T) = R + Q * (c + (A + 2 ^ 32 * T)) := by
  have hdm := Nat.div_add_mod v (2 ^ 32)
  rw [hset]
  have : Q * (v % 2 ^ 32) + Q * 2 ^ 32 * (v / 2 ^ 32 + T) =
      Q * (v % 2 ^ 32 + 2 ^ 32 * (v / 2 ^ 32)) + Q * (2 ^ 32 * T) := by
    simp only [Nat.mul_add, Nat.mul_assoc]; lia
  rw [Nat.add_assoc, this, Nat.mod_add_div, hv]
  simp only [Nat.mul_add]; lia

private theorem carryLoop_spec (acc : UInt64Array) (N : Nat) (hN : N = acc.size)
    (hNU : N < USize.size) (E : Nat) (hE : E + 2 ^ 33 < 2 ^ 64)
    (hall : ∀ k (hk : k < acc.size), acc[k].toNat ≤ E) (s len : Nat) (hs : s = 0)
    (hl : N = len) :
    ∀ d j (r : UInt32Array) (c : UInt64), N - j = d → ∀ (h : s + len ≤ r.size)
      (hlen : len ≤ N.toUSize.toNat), j ≤ N → c.toNat ≤ 2 ^ 33 →
      (∀ k (hk : k < r.size), j ≤ k → r[k] = 0) →
      let res := UInt32Array.foldInPlace.loop N.toUSize
        (carryStep acc N.toUSize (by rw [toNat_toUSize hNU]; lia)) s len r h hlen j c
      res.1.size = r.size ∧
        ofLimbs res.1.toList + 2 ^ (32 * N) * res.2.toNat =
          ofLimbs r.toList + 2 ^ (32 * j) * (c.toNat + accVal (acc.toList.drop j)) := by
  subst hs hl
  intro d
  induction d with
  | zero =>
    intro j r c hd h hlen hj hc hz
    have hjN : j = N := by lia
    subst hjN
    rw [UInt32Array.foldInPlace.loop, dite_eq_right (by lia)]
    have hd : acc.toList.drop j = [] := List.drop_of_length_le (by simp; lia)
    simp only [hd, accVal, Nat.add_zero]
    exact ⟨trivial, trivial⟩
  | succ d ih =>
    intro j r c hd h hlen hj hc hz
    have hjN : j < N := by clear ih; lia
    rw [UInt32Array.foldInPlace.loop, dite_eq_left hjN]
    dsimp only
    simp only [Nat.zero_add, carryStep, UInt64Array.uget_eq_getElem,
      toNat_toUSize (show j < USize.size by
      clear ih; lia)]
    have hjacc : j < acc.size := by clear ih; lia
    have hA := hall j hjacc
    have hv : (acc[j] + c).toNat = acc[j].toNat + c.toNat := by
      rw [UInt64.toNat_add]; exact Nat.mod_eq_of_lt (by clear ih; lia)
    have hc' : ((acc[j] + c) >>> 32).toNat ≤ 2 ^ 33 := by
      rw [UInt64.toNat_shiftRight, hv]
      simp only [UInt64.reduceToNat, Nat.reduceMod, Nat.shiftRight_eq_div_pow]
      exact Nat.le_of_lt (Nat.div_lt_of_lt_mul (by clear ih; lia))
    have hjr : j < r.size := by clear ih; lia
    obtain ⟨ih₁, ih₂⟩ := ih (j + 1) (r.set j (acc[j] + c).toUInt32 hjr)
      ((acc[j] + c) >>> 32) (by clear ih; lia) (by simpa using h) hlen (by clear ih; lia) hc'
      (fun k hk hjk => by
        rw [UInt32Array.getElem_set, ite_eq_right (by clear ih; lia)]
        exact hz k (by simpa using hk) (by clear ih; lia))
    refine ⟨by rw [ih₁]; simp, ?_⟩
    rw [ih₂]
    have hset := ofLimbs_set r.toList j (acc[j] + c).toUInt32 (by simpa using hjr)
    have hr0 : r.toList[j]'(by simpa using hjr) = 0 := by
      rw [UInt32Array.getElem_toList]; exact hz j hjr (Nat.le_refl _)
    rw [hr0, UInt32.toNat_zero, Nat.mul_zero, Nat.add_zero, UInt64.toNat_toUInt32, hv] at hset
    rw [UInt32Array.toList_set, accVal_drop acc.toList j (by simpa using hjacc), getElem_toList64,
      UInt64.toNat_shiftRight, hv]
    simp only [UInt64.reduceToNat, Nat.reduceMod, Nat.shiftRight_eq_div_pow]
    have hpow : 2 ^ (32 * (j + 1)) = 2 ^ (32 * j) * 2 ^ 32 := by rw [Nat.mul_succ, Nat.pow_add]
    rw [hpow]
    exact carry_arith _ _ _ _ _ _ _ rfl hset

/-! ## The product -/

/-- The conditions under which `rowsMul` runs: a nonempty `b` and sizes that fit. -/
@[expose] public def RowsOK (a b : UInt32Array.Slice) : Prop :=
  0 < b.size ∧ a.size + b.size < 2147483648 ∧ a.array.size < 4294967295 ∧
    b.array.size < 4294967295

public instance (a b : UInt32Array.Slice) : Decidable (RowsOK a b) := by
  unfold RowsOK; infer_instance

private theorem size_rowsLoop (a b : UInt32Array.Slice) (ha : a.array.size < USize.size)
    (hb : b.array.size < USize.size) (hab : a.size + b.size < USize.size) (sa na sb nb : USize)
    (hsa hna hsb hnb) :
    ∀ d (i : USize) (acc : UInt64Array) (hacc : acc.size = a.size + b.size),
      na.toNat - i.toNat = d →
      (rowsLoop a b ha hb hab sa na sb nb hsa hna hsb hnb acc hacc i).size = a.size + b.size := by
  intro d
  induction d with
  | zero =>
    intro i acc hacc hd
    rw [rowsLoop, dite_eq_right (by rw [USize.lt_iff_toNat_lt]; lia)]
    exact hacc
  | succ d ih =>
    intro i acc hacc hd
    have hlt : i < na := by rw [USize.lt_iff_toNat_lt]; clear ih; lia
    rw [rowsLoop, dite_eq_left hlt]
    exact ih _ _ _ (by
      rw [toNat_add_usize (by have := na.toNat_lt_size; simp; clear ih; lia)]; simp; clear ih; lia)

/-- All `a.size + b.size` limbs of `a * b`, by rows into wide accumulators, then the carries. -/
public def rowsMul (a b : UInt32Array.Slice) (h : RowsOK a b) : UInt32Array :=
  have ha := lt_usizeSize h.2.2.1
  have hb := lt_usizeSize h.2.2.2
  have hab : a.size + b.size < USize.size := lt_usizeSize (by have := h.2.1; lia)
  (UInt32Array.replicate (a.size + b.size) 0).foldInPlaceThen 0 (a.size + b.size).toUSize 0
    (carryStep (rowsLoop a b ha hb hab a.start.toUSize a.size.toUSize b.start.toUSize
        b.size.toUSize rfl rfl rfl rfl (UInt64Array.replicate (a.size + b.size) 0) (by simp) 0)
      (a.size + b.size).toUSize
      (by rw [toNat_toUSize hab, size_rowsLoop a b ha hb hab _ _ _ _ _ _ _ _ _ 0 _ _ rfl]
          exact Nat.le_refl _))
    (fun r _ => r) (by
      simp only [UInt32Array.size_replicate, USize.toNat_zero, Nat.zero_add, toNat_toUSize hab]
      exact Nat.le_refl _)

public theorem rowsMul_spec (a b : UInt32Array.Slice) (h : RowsOK a b) :
    (rowsMul a b h).size = a.size + b.size ∧ toNat (rowsMul a b h) = toNat a * toNat b := by
  have ha := lt_usizeSize h.2.2.1
  have hb := lt_usizeSize h.2.2.2
  have hab : a.size + b.size < USize.size := lt_usizeSize (by have := h.2.1; lia)
  have ha31 : a.size < 2 ^ 31 := by have := h.2.1; lia
  have hrep : (UInt64Array.replicate (a.size + b.size) 0).toList =
      List.replicate (a.size + b.size) 0 := by
    simp [← UInt64Array.toList_toArray]
  obtain ⟨hs, hv, hbd⟩ := rowsLoop_spec a b ha hb hab ha31 h.1 _ _ _ _ rfl rfl rfl rfl a.size 0
    (UInt64Array.replicate (a.size + b.size) 0) (by simp) (by simp) (Nat.zero_le _)
    (by intro v hv; rw [hrep] at hv; rw [(List.mem_replicate.1 hv).2]; simp)
    (by rw [hrep, accVal_replicate_zero]; simp [toNat, Nat.mul_comm])
  simp only [rowsMul, UInt32Array.foldInPlaceThen_eq, UInt32Array.foldInPlace]
  have hE : 2 ^ 33 * a.size + 2 ^ 33 < 2 ^ 64 := by
    have h1 : a.size + 1 < 2 ^ 31 := by have := h.2.1; have := h.1; lia
    have := Nat.mul_lt_mul_of_pos_left h1 (show 0 < 2 ^ 33 by decide)
    rw [Nat.mul_succ] at this
    lia
  obtain ⟨h₁, h₂⟩ := carryLoop_spec
    (rowsLoop a b ha hb hab a.start.toUSize a.size.toUSize b.start.toUSize b.size.toUSize rfl rfl
      rfl rfl (UInt64Array.replicate (a.size + b.size) 0) (by simp) 0)
    (a.size + b.size) hs.symm hab (2 ^ 33 * a.size) hE
    (fun k hk => hbd _ (List.mem_iff_getElem.2 ⟨k, by simpa using hk, getElem_toList64 _ _ _⟩))
    (USize.toNat 0) ((a.size + b.size).toUSize.toNat) rfl (toNat_toUSize hab).symm
    (a.size + b.size) 0 (UInt32Array.replicate (a.size + b.size) 0) 0 (Nat.sub_zero _)
    (by
      simp only [USize.toNat_zero, Nat.zero_add, toNat_toUSize hab, UInt32Array.size_replicate]
      exact Nat.le_refl _)
    (Nat.le_refl _) (Nat.zero_le _) (by simp) (fun k hk _ => by simp)
  simp only [UInt32Array.toList_replicate, ofLimbs_replicate_zero, Nat.mul_zero, Nat.zero_add,
    List.drop_zero, UInt64.toNat_zero, Nat.pow_zero, Nat.one_mul, hv] at h₂
  revert h₁ h₂
  generalize UInt32Array.foldInPlace.loop (a.size + b.size).toUSize
    (carryStep (rowsLoop a b ha hb hab a.start.toUSize a.size.toUSize b.start.toUSize
      b.size.toUSize rfl rfl
      rfl rfl (UInt64Array.replicate (a.size + b.size) 0) (by simp) 0)
      (a.size + b.size).toUSize _) (USize.toNat 0) ((a.size + b.size).toUSize.toNat)
    (UInt32Array.replicate (a.size + b.size) 0) _ _ 0 0 = R
  intro h₁ h₂
  have hlt : toNat a * toNat b < 2 ^ (32 * (a.size + b.size)) := by
    rw [Nat.mul_add, Nat.pow_add]
    exact Nat.mul_lt_mul'' (toNat_lt a) (toNat_lt b)
  have hR2 : R.2.toNat = 0 := by
    rcases Nat.eq_zero_or_pos R.2.toNat with h0 | h0
    · exact h0
    · have : 2 ^ (32 * (a.size + b.size)) ≤ 2 ^ (32 * (a.size + b.size)) * R.2.toNat :=
        Nat.le_mul_of_pos_right _ h0
      lia
  rw [hR2, Nat.mul_zero, Nat.add_zero] at h₂
  exact ⟨by rw [h₁]; simp, by rw [toNat_toSlice, h₂]⟩

end MPN
