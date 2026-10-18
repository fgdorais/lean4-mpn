/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import MPN.Basic
public import MPN.Sum

/-!
# Comba multiplication

The schoolbook product column by column, after Paul Comba: limb `k` of `a * b` comes from the sum
of the products `aᵢ b_{k-i}`, plus the carry from the column below. Within a column the products
are independent, so there is no carry chain from one product to the next as in the rows of
`addMul1`. For short operands the low and high halves of the products go into two `UInt64`
accumulators, which cannot overflow for fewer than `2³¹` products, and the C compiler vectorizes
the loop (`colLoop`); from 32 limbs the whole products go into one accumulator that counts its
wraps (`colLoopW`), an addition with carry per product, which is faster although not vectorized.

The specification is `Σ_k βᵏ colSum k = a * b` (`weighted_eq`), where `colSum k` adds the products
of column `k` over all `i ≤ k`, with limbs past the end read as zero.
-/

open ScalarArray

namespace MPN

/-! ## Column sums -/

/-- The `i`-th limb of `l`, zero past its end, as a number. -/
public def limbD (l : List UInt32) (i : Nat) : Nat := (l.getD i 0).toNat

/-- The products of column `k`, from `i = 0` to `t - 1`. -/
public def colPart (la lb : List UInt32) (k t : Nat) : Nat :=
  sumRange (fun i => limbD la i * limbD lb (k - i)) t

/-- The sum of column `k` of the product of `la` and `lb`. -/
public def colSum (la lb : List UInt32) (k : Nat) : Nat := colPart la lb k (k + 1)

/-- `Σ_{k < N} βᵏ colSum k`. -/
public def weighted (la lb : List UInt32) (N : Nat) : Nat :=
  sumRange (fun k => 2 ^ (32 * k) * colSum la lb k) N

private theorem sumRange_limbs (l : List UInt32) (N : Nat) (h : l.length ≤ N) :
    sumRange (fun k => 2 ^ (32 * k) * limbD l k) N = ofLimbs l := by
  induction l generalizing N with
  | nil =>
    rw [sumRange_extend (Nat.zero_le N) (fun i _ _ => by simp [limbD])]
    rfl
  | cons x l ih =>
    obtain ⟨N, rfl⟩ : ∃ N', N = N' + 1 := ⟨N - 1, by simp at h; lia⟩
    have hs : sumRange (fun i => 2 ^ (32 * (i + 1)) * limbD (x :: l) (i + 1)) N =
        sumRange (fun i => 2 ^ 32 * (2 ^ (32 * i) * limbD l i)) N :=
      sumRange_congr fun i _ => by
        simp only [limbD, List.getD_cons_succ]
        rw [Nat.mul_add, Nat.pow_add, Nat.mul_one, Nat.mul_comm (2 ^ (32 * i)) (2 ^ 32),
          Nat.mul_assoc]
    rw [sumRange_succ_left, hs, ← sumRange_mul_left, ih N (by simp at h; lia), ofLimbs_cons]
    simp [limbD]

private theorem colSum_cons_zero (x : UInt32) (la lb : List UInt32) :
    colSum (x :: la) lb 0 = x.toNat * limbD lb 0 := by
  simp [colSum, colPart, sumRange, limbD]

private theorem colSum_cons_succ (x : UInt32) (la lb : List UInt32) (k : Nat) :
    colSum (x :: la) lb (k + 1) = x.toNat * limbD lb (k + 1) + colSum la lb k := by
  rw [colSum, colPart, sumRange_succ_left, colSum, colPart]
  have hs : sumRange (fun i => limbD (x :: la) (i + 1) * limbD lb (k + 1 - (i + 1))) (k + 1) =
      sumRange (fun i => limbD la i * limbD lb (k - i)) (k + 1) :=
    sumRange_congr fun i _ => by
      simp only [limbD, List.getD_cons_succ]
      rw [show k + 1 - (i + 1) = k - i by lia]
  rw [hs]
  simp [limbD]

private theorem colSum_nil (lb : List UInt32) (k : Nat) : colSum [] lb k = 0 := by
  rw [colSum, colPart, sumRange_extend (n := 0) (Nat.zero_le _) (fun i _ _ => by simp [limbD])]
  rfl

/-- The columns of a product, weighted by their place, add up to the product. -/
public theorem weighted_eq (la lb : List UInt32) (N : Nat) (h : la.length + lb.length ≤ N + 1) :
    weighted la lb N = ofLimbs la * ofLimbs lb := by
  induction la generalizing N with
  | nil =>
    rw [weighted, sumRange_extend (n := 0) (Nat.zero_le N) (fun k _ _ => by
      rw [colSum_nil, Nat.mul_zero])]
    simp [sumRange]
  | cons x la ih =>
    rcases N with _ | N
    · -- No column at all: `lb` is empty.
      have : lb = [] := List.eq_nil_of_length_eq_zero (by simp at h; lia)
      subst this
      simp [weighted, sumRange]
    · have hs : sumRange (fun k => 2 ^ (32 * (k + 1)) * colSum (x :: la) lb (k + 1)) N =
          x.toNat * sumRange (fun k => 2 ^ (32 * (k + 1)) * limbD lb (k + 1)) N +
            2 ^ 32 * weighted la lb N := by
        rw [weighted, sumRange_mul_left, sumRange_mul_left, ← sumRange_add]
        apply sumRange_congr
        intro i _
        rw [colSum_cons_succ]
        have e : 2 ^ (32 * (i + 1)) = 2 ^ 32 * 2 ^ (32 * i) := by
          rw [← Nat.pow_add]; congr 1; lia
        rw [e]
        generalize 2 ^ 32 = B
        generalize 2 ^ (32 * i) = P
        generalize limbD lb (i + 1) = y
        generalize colSum la lb i = c
        rw [Nat.mul_add, Nat.mul_left_comm (B * P), Nat.mul_assoc B P c]
      have hl := sumRange_limbs lb (N + 1) (by simp at h; lia)
      rw [sumRange_succ_left] at hl
      simp only [Nat.mul_zero, Nat.pow_zero, Nat.one_mul] at hl
      rw [weighted, sumRange_succ_left, colSum_cons_zero, hs, ih N (by simp at h; lia),
        ofLimbs_cons, ← hl]
      simp only [Nat.mul_zero, Nat.pow_zero, Nat.one_mul]
      generalize sumRange (fun k => 2 ^ (32 * (k + 1)) * limbD lb (k + 1)) N = S
      generalize limbD lb 0 = y
      generalize ofLimbs la = A
      generalize (2 : Nat) ^ 32 = B
      rw [Nat.add_mul, Nat.mul_add, Nat.mul_assoc, ← Nat.add_assoc]
      simp only [Nat.mul_add]

/-! ## Column sums of a square -/

/-- The diagonal term of column `k` of a square: `a_{k/2}²` when `k` is even. -/
public def sqDiagCol (la : List UInt32) (k : Nat) : Nat :=
  if k % 2 = 0 then limbD la (k / 2) * limbD la (k / 2) else 0

/--
A column of a square is twice its products below the diagonal, `i < k - i`, plus the diagonal:
the products `aᵢ a_{k-i}` and `a_{k-i} aᵢ` are equal.
-/
public theorem colSum_sq (la : List UInt32) (k : Nat) :
    colSum la la k = 2 * colPart la la k ((k + 1) / 2) + sqDiagCol la k := by
  unfold colSum colPart sqDiagCol
  generalize hf : (fun i => limbD la i * limbD la (k - i)) = f
  have hsym : ∀ i, i ≤ k → f (k - i) = f i := by
    intro i hi; rw [← hf]; dsimp only; rw [show k - (k - i) = i by lia, Nat.mul_comm]
  rcases Nat.mod_two_eq_zero_or_one k with he | ho
  · -- `k = 2h`: the products below `h`, the diagonal `h`, and those above, reflected.
    obtain ⟨h, rfl⟩ : ∃ h, k = 2 * h := ⟨k / 2, by lia⟩
    rw [show (2 * h + 1) / 2 = h by lia, ite_eq_left he, show 2 * h + 1 = h + (h + 1) by lia,
      sumRange_append, sumRange_succ_left]
    have hup : sumRange (fun i => f (h + (i + 1))) h = sumRange f h := by
      rw [← sumRange_reflect f h]
      exact sumRange_congr fun i hi => by
        rw [← hsym (h + (i + 1)) (by lia), show 2 * h - (h + (i + 1)) = h - 1 - i by lia]
    have hd : f (h + 0) = limbD la (2 * h / 2) * limbD la (2 * h / 2) := by
      rw [← hf]; dsimp only; rw [show 2 * h / 2 = h by lia, show 2 * h - (h + 0) = h by lia,
        Nat.add_zero]
    rw [hup, hd]
    lia
  · -- `k = 2h - 1`: the products below `h`, and those above, reflected.
    obtain ⟨h, rfl⟩ : ∃ h, k = 2 * h + 1 := ⟨k / 2, by lia⟩
    rw [show (2 * h + 1 + 1) / 2 = h + 1 by lia, ite_eq_right (by lia),
      show 2 * h + 1 + 1 = (h + 1) + (h + 1) by lia, sumRange_append]
    have hup : sumRange (fun i => f (h + 1 + i)) (h + 1) = sumRange f (h + 1) := by
      rw [← sumRange_reflect f (h + 1)]
      exact sumRange_congr fun i hi => by
        rw [← hsym (h + 1 + i) (by lia), show 2 * h + 1 - (h + 1 + i) = h + 1 - 1 - i by lia]
    rw [hup]
    lia

/-! ## The compiled loops -/

/--
Writes the column total `lo + β hi` into limbs `k`, `k + 1` and `k + 2` of `r`: the limb of the
column and, above it, the carry into the next column.
-/
@[inline] def writeCol (r : UInt32Array) (k : USize) (hrs : r.size < USize.size)
    (hk : k.toNat + 2 < r.size) (lo hi : UInt64) : UInt32Array :=
  let c := (lo >>> 32) + hi
  ((r.uset k lo.toUInt32 (by lia)).uset (k + 1) c.toUInt32
      (by rw [UInt32Array.size_uset, toNat_add_usize (by simp; lia)]; simp; lia)).uset (k + 2)
    (c >>> 32).toUInt32
    (by rw [UInt32Array.size_uset, UInt32Array.size_uset, toNat_add_usize (by simp; lia)]
        simp; lia)

private theorem writeCol_eq (r : UInt32Array) (k : USize) (hrs : r.size < USize.size)
    (hk : k.toNat + 2 < r.size) (lo hi : UInt64) :
    writeCol r k hrs hk lo hi =
      ((r.set k.toNat lo.toUInt32 (by lia)).set (k.toNat + 1) ((lo >>> 32) + hi).toUInt32
        (by simp; lia)).set (k.toNat + 2) (((lo >>> 32) + hi) >>> 32).toUInt32
        (by simp; lia) := by
  have hk1 : (k + 1).toNat = k.toNat + 1 := by rw [toNat_add_usize (by simp; lia)]; simp
  have hk2 : (k + 2).toNat = k.toNat + 2 := by rw [toNat_add_usize (by simp; lia)]; simp
  have h₀ : ∀ (a : UInt32Array) v h, a.uset k v h = a.set k.toNat v h :=
    fun a v h => uset_eq_set a k _ rfl v h
  have h₁ : ∀ (a : UInt32Array) v h, a.uset (k + 1) v h = a.set (k.toNat + 1) v (hk1 ▸ h) :=
    fun a v h => uset_eq_set a _ _ hk1 v h
  have h₂ : ∀ (a : UInt32Array) v h, a.uset (k + 2) v h = a.set (k.toNat + 2) v (hk2 ▸ h) :=
    fun a v h => uset_eq_set a _ _ hk2 v h
  simp only [writeCol, h₀, h₁, h₂]

private theorem writeCol_spec (r : UInt32Array) (k : USize) (hrs : r.size < USize.size)
    (hk : k.toNat + 2 < r.size) (lo hi : UInt64)
    (_hfit : lo.toNat + 2 ^ 32 * hi.toNat < 2 ^ 96) (_hhi : hi.toNat + 2 ^ 32 ≤ 2 ^ 64) :
    (writeCol r k hrs hk lo hi).size = r.size ∧
      (∀ j, k.toNat + 3 ≤ j → ∀ (hj' : j < r.size),
        (writeCol r k hrs hk lo hi)[j]'(by simp only [writeCol_eq]; simpa using hj') = r[j]) ∧
      ofLimbs (writeCol r k hrs hk lo hi).toList +
          2 ^ (32 * k.toNat) * (r[k.toNat].toNat + 2 ^ 32 * (r[k.toNat + 1]'(by lia)).toNat +
            2 ^ 64 * (r[k.toNat + 2]'(by lia)).toNat) =
        ofLimbs r.toList + 2 ^ (32 * k.toNat) * (lo.toNat + 2 ^ 32 * hi.toNat) := by
  simp only [writeCol_eq]
  refine ⟨by simp, fun j hj hj' => ?_, ?_⟩
  · simp only [UInt32Array.getElem_set]
    rw [ite_eq_right (by lia), ite_eq_right (by lia), ite_eq_right (by lia)]
  · -- The three limbs written are the digits of `lo + β hi`.
    have hlo := lo.toNat_lt
    have hc : ((lo >>> 32) + hi).toNat = lo.toNat / 2 ^ 32 + hi.toNat := by
      rw [UInt64.toNat_add, UInt64.toNat_shiftRight]
      simp only [UInt64.reduceToNat, Nat.reduceMod, Nat.shiftRight_eq_div_pow]
      exact Nat.mod_eq_of_lt (by lia)
    have hcβ : lo.toNat / 2 ^ 32 + hi.toNat < 2 ^ 64 := by lia
    have hd0 : lo.toUInt32.toNat = lo.toNat % 2 ^ 32 := UInt64.toNat_toUInt32 _
    have hd1 : ((lo >>> 32) + hi).toUInt32.toNat = (lo.toNat / 2 ^ 32 + hi.toNat) % 2 ^ 32 := by
      rw [UInt64.toNat_toUInt32, hc]
    have hd2 : (((lo >>> 32) + hi) >>> 32).toUInt32.toNat =
        (lo.toNat / 2 ^ 32 + hi.toNat) / 2 ^ 32 := by
      rw [UInt64.toNat_toUInt32, UInt64.toNat_shiftRight, hc]
      simp only [UInt64.reduceToNat, Nat.reduceMod, Nat.shiftRight_eq_div_pow]
      exact Nat.mod_eq_of_lt (by lia)
    have hsum : lo.toNat % 2 ^ 32 + 2 ^ 32 * ((lo.toNat / 2 ^ 32 + hi.toNat) % 2 ^ 32) +
        2 ^ 64 * ((lo.toNat / 2 ^ 32 + hi.toNat) / 2 ^ 32) = lo.toNat + 2 ^ 32 * hi.toNat := by
      have h₁ := Nat.div_add_mod lo.toNat (2 ^ 32)
      have h₂ := Nat.div_add_mod (lo.toNat / 2 ^ 32 + hi.toNat) (2 ^ 32)
      generalize hq : lo.toNat / 2 ^ 32 = q at h₁ h₂ ⊢
      generalize hcd : q + hi.toNat = c at h₂ ⊢
      lia
    simp only [UInt32Array.toList_set]
    have e₁ := ofLimbs_set r.toList k.toNat lo.toUInt32 (by simp; lia)
    have e₂ := ofLimbs_set (r.toList.set k.toNat lo.toUInt32) (k.toNat + 1)
      ((lo >>> 32) + hi).toUInt32 (by simp; lia)
    have e₃ := ofLimbs_set ((r.toList.set k.toNat lo.toUInt32).set (k.toNat + 1)
      ((lo >>> 32) + hi).toUInt32) (k.toNat + 2) (((lo >>> 32) + hi) >>> 32).toUInt32
      (by simp; lia)
    simp only [List.getElem_set_ne (show k.toNat ≠ k.toNat + 1 by lia),
      List.getElem_set_ne (show k.toNat ≠ k.toNat + 2 by lia),
      List.getElem_set_ne (show k.toNat + 1 ≠ k.toNat + 2 by lia),
      UInt32Array.getElem_toList] at e₁ e₂ e₃
    rw [hd0] at e₁
    rw [hd1] at e₂
    rw [hd2] at e₃
    rw [← hsum]
    have p₁ : 2 ^ (32 * (k.toNat + 1)) = 2 ^ (32 * k.toNat) * 2 ^ 32 := by
      rw [← Nat.pow_add]; congr 1
    have p₂ : 2 ^ (32 * (k.toNat + 2)) = 2 ^ (32 * k.toNat) * 2 ^ 64 := by
      rw [← Nat.pow_add]; congr 1
    rw [p₁] at e₂
    rw [p₂] at e₃
    generalize 2 ^ (32 * k.toNat) = P at *
    generalize ofLimbs _ = L₃ at e₃ ⊢
    generalize ofLimbs ((r.toList.set k.toNat lo.toUInt32).set (k.toNat + 1)
      ((lo >>> 32) + hi).toUInt32) = L₂ at e₂ e₃
    generalize ofLimbs (r.toList.set k.toNat lo.toUInt32) = L₁ at e₁ e₂
    generalize lo.toNat % 2 ^ 32 = d₀ at *
    generalize (lo.toNat / 2 ^ 32 + hi.toNat) % 2 ^ 32 = d₁ at *
    generalize (lo.toNat / 2 ^ 32 + hi.toNat) / 2 ^ 32 = d₂ at *
    generalize (2 : Nat) ^ 32 = B at *
    generalize (2 : Nat) ^ 64 = B₂ at *
    grind

/--
The products of column `k` from `i` to `iEnd` added to `lo + β hi`, low halves in `lo` and high
halves in `hi`, then handed to `fin`. The limbs of `a` are `aa[sa ...]` and those of `b` are
`bb[sb ...]`, read with `limbU`. The product finishes by writing the column (`combaCol`), the
square by doubling it first (`csqCol`).
-/
@[specialize] def colLoop (aa : UInt32Array) (sa na : USize) (ha : aa.size < USize.size)
    (hA : sa.toNat + na.toNat ≤ aa.size) (bb : UInt32Array) (sb nb : USize)
    (hb : bb.size < USize.size) (hB : sb.toNat + nb.toNat ≤ bb.size)
    (k iEnd : USize) (hiE : iEnd.toNat ≤ na.toNat) (hiEk : iEnd.toNat ≤ k.toNat + 1)
    (fin : UInt64 → UInt64 → UInt32Array)
    (i : USize) (_hii : i.toNat ≤ iEnd.toNat) (hst : k.toNat + 1 ≤ nb.toNat + i.toNat)
    (lo hi : UInt64) : UInt32Array :=
  if h : i < iEnd then
    have h' : i.toNat < iEnd.toNat := h
    let x := limbU aa sa na ha hA i (by lia)
    let y := limbU bb sb nb hb hB (k - i)
      (by rw [USize.toNat_sub_of_le _ _ (USize.le_iff_toNat_le.2 (by lia))]; lia)
    let p := x.toUInt64 * y.toUInt64
    colLoop aa sa na ha hA bb sb nb hb hB k iEnd hiE hiEk fin (i + 1)
      (by rw [toNat_add_usize (by simp; lia)]; simp; lia)
      (by rw [toNat_add_usize (by simp; lia)]; simp; lia)
      (lo + (p &&& 0xFFFFFFFF)) (hi + (p >>> 32))
  else
    fin lo hi
termination_by iEnd.toNat - i.toNat
decreasing_by
  rw [toNat_add_usize (by simp; lia)]; simp; lia

private theorem colLoop_spec (aa : UInt32Array) (sa na : USize) (ha : aa.size < USize.size)
    (hA : sa.toNat + na.toNat ≤ aa.size) (bb : UInt32Array) (sb nb : USize)
    (hb : bb.size < USize.size) (hB : sb.toNat + nb.toNat ≤ bb.size)
    (k iEnd : USize) (hiE : iEnd.toNat ≤ na.toNat) (hiEk : iEnd.toNat ≤ k.toNat + 1)
    (fin : UInt64 → UInt64 → UInt32Array) (la lb : List UInt32)
    (hxa : ∀ j (_ : j < na.toNat), (aa[sa.toNat + j]'(by lia)).toNat = limbD la j)
    (hxb : ∀ j (_ : j < nb.toNat), (bb[sb.toNat + j]'(by lia)).toNat = limbD lb j)
    (c₀ : Nat) (i : USize) (hii : i.toNat ≤ iEnd.toNat) (hst : k.toNat + 1 ≤ nb.toNat + i.toNat)
    (lo hi : UInt64)
    (hacc : lo.toNat + 2 ^ 32 * hi.toNat = c₀ + colPart la lb k.toNat i.toNat)
    (hlo : lo.toNat + (iEnd.toNat - i.toNat) * 2 ^ 32 < 2 ^ 64)
    (hhi : hi.toNat + (iEnd.toNat - i.toNat) * 2 ^ 32 < 2 ^ 64) :
    ∃ lo' hi' : UInt64, colLoop aa sa na ha hA bb sb nb hb hB k iEnd hiE hiEk fin i hii hst
        lo hi = fin lo' hi' ∧
      lo'.toNat + 2 ^ 32 * hi'.toNat = c₀ + colPart la lb k.toNat iEnd.toNat ∧
      lo'.toNat ≤ lo.toNat + (iEnd.toNat - i.toNat) * 2 ^ 32 ∧
      hi'.toNat ≤ hi.toNat + (iEnd.toNat - i.toNat) * 2 ^ 32 := by
  induction hd : iEnd.toNat - i.toNat generalizing i lo hi with
  | zero =>
    have hie : i.toNat = iEnd.toNat := by lia
    rw [colLoop, dite_eq_right (by rw [USize.lt_iff_toNat_lt]; lia)]
    exact ⟨lo, hi, rfl, by rw [hacc, hie], by lia, by lia⟩
  | succ d ih =>
    have h' : i.toNat < iEnd.toNat := by lia
    rw [colLoop, dite_eq_left (show i < iEnd from h')]
    dsimp only
    have hi1 : (i + 1).toNat = i.toNat + 1 := by rw [toNat_add_usize (by simp; lia)]; simp
    have hki : (k - i).toNat = k.toNat - i.toNat :=
      USize.toNat_sub_of_le _ _ (USize.le_iff_toNat_le.2 (by lia))
    have hx : (limbU aa sa na ha hA i (by lia)).toNat = limbD la i.toNat := by
      rw [limbU_eq_getElem _ _ _ _ _ _ _ _ rfl, hxa _ (by lia)]
    have hy : (limbU bb sb nb hb hB (k - i) (by rw [hki]; lia)).toNat =
        limbD lb (k.toNat - i.toNat) := by
      rw [limbU_eq_getElem _ _ _ _ _ _ _ _ rfl]
      simp only [hki]
      rw [hxb _ (by lia)]
    generalize limbU aa sa na ha hA i _ = x at hx ⊢
    generalize limbU bb sb nb hb hB (k - i) _ = y at hy ⊢
    have hp : (x.toUInt64 * y.toUInt64).toNat = x.toNat * y.toNat := by
      rw [UInt64.toNat_mul, UInt32.toNat_toUInt64, UInt32.toNat_toUInt64]
      exact Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le (Nat.mul_lt_mul'' x.toNat_lt y.toNat_lt)
        (by decide))
    have hpl : ((x.toUInt64 * y.toUInt64) &&& 0xFFFFFFFF).toNat = x.toNat * y.toNat % 2 ^ 32 := by
      rw [UInt64.toNat_and, hp]
      exact Nat.and_two_pow_sub_one_eq_mod _ 32
    have hph : ((x.toUInt64 * y.toUInt64) >>> 32).toNat = x.toNat * y.toNat / 2 ^ 32 := by
      rw [UInt64.toNat_shiftRight, hp]
      simp [Nat.shiftRight_eq_div_pow]
    have hxy : x.toNat * y.toNat / 2 ^ 32 < 2 ^ 32 := by
      rw [Nat.div_lt_iff_lt_mul (by decide)]
      exact Nat.lt_of_lt_of_le (Nat.mul_lt_mul'' x.toNat_lt y.toNat_lt) (by decide)
    have hxym := Nat.mod_lt (x.toNat * y.toNat) (show 0 < 2 ^ 32 by decide)
    have hlo' : (lo + ((x.toUInt64 * y.toUInt64) &&& 0xFFFFFFFF)).toNat =
        lo.toNat + x.toNat * y.toNat % 2 ^ 32 := by
      rw [UInt64.toNat_add, hpl]; exact Nat.mod_eq_of_lt (by lia)
    have hhi' : (hi + ((x.toUInt64 * y.toUInt64) >>> 32)).toNat =
        hi.toNat + x.toNat * y.toNat / 2 ^ 32 := by
      rw [UInt64.toNat_add, hph]; exact Nat.mod_eq_of_lt (by lia)
    obtain ⟨lo', hi', heq, hacc', hlo'', hhi''⟩ := ih (i + 1)
      (by rw [hi1]; lia) (by rw [hi1]; lia) (lo + ((x.toUInt64 * y.toUInt64) &&& 0xFFFFFFFF))
      (hi + ((x.toUInt64 * y.toUInt64) >>> 32))
      (by
        rw [hlo', hhi', hi1, colPart, sumRange, ← colPart, ← hx, ← hy, Nat.mul_add]
        have := Nat.div_add_mod (x.toNat * y.toNat) (2 ^ 32)
        lia)
      (by rw [hlo', hi1]; lia) (by rw [hhi', hi1]; lia) (by rw [hi1]; lia)
    refine ⟨lo', hi', heq, hacc', ?_, ?_⟩
    · rw [hlo'] at hlo''; lia
    · rw [hhi'] at hhi''; lia

/-- `colLoop` finished by writing the column into `r`, for the product. -/
@[inline] def combaCol (aa : UInt32Array) (sa na : USize) (ha : aa.size < USize.size)
    (hA : sa.toNat + na.toNat ≤ aa.size) (bb : UInt32Array) (sb nb : USize)
    (hb : bb.size < USize.size) (hB : sb.toNat + nb.toNat ≤ bb.size)
    (k iEnd : USize) (hiE : iEnd.toNat ≤ na.toNat) (hiEk : iEnd.toNat ≤ k.toNat + 1)
    (r : UInt32Array) (hrs : r.size < USize.size) (hr : k.toNat + 2 < r.size)
    (i : USize) (hii : i.toNat ≤ iEnd.toNat) (hst : k.toNat + 1 ≤ nb.toNat + i.toNat)
    (lo hi : UInt64) : UInt32Array :=
  colLoop aa sa na ha hA bb sb nb hb hB k iEnd hiE hiEk (fun lo hi => writeCol r k hrs hr lo hi) i
    hii hst lo hi

private theorem combaCol_spec (aa : UInt32Array) (sa na : USize) (ha : aa.size < USize.size)
    (hA : sa.toNat + na.toNat ≤ aa.size) (bb : UInt32Array) (sb nb : USize)
    (hb : bb.size < USize.size) (hB : sb.toNat + nb.toNat ≤ bb.size)
    (k iEnd : USize) (hiE : iEnd.toNat ≤ na.toNat) (hiEk : iEnd.toNat ≤ k.toNat + 1)
    (r : UInt32Array) (hrs : r.size < USize.size) (hr : k.toNat + 2 < r.size)
    (la lb : List UInt32)
    (hxa : ∀ j (hj : j < na.toNat), (aa[sa.toNat + j]'(by lia)).toNat = limbD la j)
    (hxb : ∀ j (hj : j < nb.toNat), (bb[sb.toNat + j]'(by lia)).toNat = limbD lb j)
    (c₀ : Nat) (i : USize) (hii : i.toNat ≤ iEnd.toNat) (hst : k.toNat + 1 ≤ nb.toNat + i.toNat)
    (lo hi : UInt64)
    (hacc : lo.toNat + 2 ^ 32 * hi.toNat = c₀ + colPart la lb k.toNat i.toNat)
    (hlo : lo.toNat + (iEnd.toNat - i.toNat) * 2 ^ 32 < 2 ^ 64)
    (hhi : hi.toNat + (iEnd.toNat - i.toNat + 1) * 2 ^ 32 ≤ 2 ^ 64) :
    ∃ lo' hi' : UInt64, combaCol aa sa na ha hA bb sb nb hb hB k iEnd hiE hiEk r hrs hr i hii hst
        lo hi = writeCol r k hrs hr lo' hi' ∧
      lo'.toNat + 2 ^ 32 * hi'.toNat = c₀ + colPart la lb k.toNat iEnd.toNat ∧
      hi'.toNat + 2 ^ 32 ≤ 2 ^ 64 := by
  obtain ⟨lo', hi', heq, hacc', _, hhi'⟩ := colLoop_spec aa sa na ha hA bb sb nb hb hB k iEnd hiE
    hiEk _ la lb hxa hxb c₀ i hii hst lo hi hacc hlo (by lia)
  exact ⟨lo', hi', heq, hacc', by lia⟩

private theorem size_colLoop (aa : UInt32Array) (sa na : USize) (ha : aa.size < USize.size)
    (hA : sa.toNat + na.toNat ≤ aa.size) (bb : UInt32Array) (sb nb : USize)
    (hb : bb.size < USize.size) (hB : sb.toNat + nb.toNat ≤ bb.size)
    (k iEnd : USize) (hiE : iEnd.toNat ≤ na.toNat) (hiEk : iEnd.toNat ≤ k.toNat + 1)
    (fin : UInt64 → UInt64 → UInt32Array) (S : Nat) (hfin : ∀ lo hi, (fin lo hi).size = S)
    (i : USize) (hii : i.toNat ≤ iEnd.toNat) (hst : k.toNat + 1 ≤ nb.toNat + i.toNat)
    (lo hi : UInt64) :
    (colLoop aa sa na ha hA bb sb nb hb hB k iEnd hiE hiEk fin i hii hst lo hi).size = S := by
  induction hd : iEnd.toNat - i.toNat generalizing i lo hi with
  | zero =>
    rw [colLoop, dite_eq_right (by rw [USize.lt_iff_toNat_lt]; lia)]
    exact hfin _ _
  | succ d ih =>
    have h' : i.toNat < iEnd.toNat := by lia
    rw [colLoop, dite_eq_left (show i < iEnd from h')]
    dsimp only
    apply ih
    rw [toNat_add_usize (by simp; lia)]; simp; lia

private theorem size_combaCol (aa : UInt32Array) (sa na : USize) (ha : aa.size < USize.size)
    (hA : sa.toNat + na.toNat ≤ aa.size) (bb : UInt32Array) (sb nb : USize)
    (hb : bb.size < USize.size) (hB : sb.toNat + nb.toNat ≤ bb.size)
    (k iEnd : USize) (hiE : iEnd.toNat ≤ na.toNat) (hiEk : iEnd.toNat ≤ k.toNat + 1)
    (r : UInt32Array) (hrs : r.size < USize.size) (hr : k.toNat + 2 < r.size)
    (i : USize) (hii : i.toNat ≤ iEnd.toNat) (hst : k.toNat + 1 ≤ nb.toNat + i.toNat)
    (lo hi : UInt64) :
    (combaCol aa sa na ha hA bb sb nb hb hB k iEnd hiE hiEk r hrs hr i hii hst lo hi).size =
      r.size :=
  size_colLoop _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (fun _ _ => by simp only [writeCol_eq,
    UInt32Array.size_set]) _ _ _ _ _

/--
The products of column `k` from `i` to `iEnd` added to `acc + 2⁶⁴ w`, whole products in `acc`
with `w` counting its wraps, then handed to `fin`. One addition with carry per product, where
`colLoop` adds the two halves of each product into two sums: from 32 limbs up the products are
5–13% faster this way, although the C compiler vectorizes `colLoop` and not this loop.
-/
@[specialize] def colLoopW (aa : UInt32Array) (sa na : USize) (ha : aa.size < USize.size)
    (hA : sa.toNat + na.toNat ≤ aa.size) (bb : UInt32Array) (sb nb : USize)
    (hb : bb.size < USize.size) (hB : sb.toNat + nb.toNat ≤ bb.size)
    (k iEnd : USize) (hiE : iEnd.toNat ≤ na.toNat) (hiEk : iEnd.toNat ≤ k.toNat + 1)
    (fin : UInt64 → UInt64 → UInt32Array)
    (i : USize) (_hii : i.toNat ≤ iEnd.toNat) (hst : k.toNat + 1 ≤ nb.toNat + i.toNat)
    (acc w : UInt64) : UInt32Array :=
  if h : i < iEnd then
    have h' : i.toNat < iEnd.toNat := h
    let x := limbU aa sa na ha hA i (by lia)
    let y := limbU bb sb nb hb hB (k - i)
      (by rw [USize.toNat_sub_of_le _ _ (USize.le_iff_toNat_le.2 (by lia))]; lia)
    let p := x.toUInt64 * y.toUInt64
    let acc' := acc + p
    colLoopW aa sa na ha hA bb sb nb hb hB k iEnd hiE hiEk fin (i + 1)
      (by rw [toNat_add_usize (by simp; lia)]; simp; lia)
      (by rw [toNat_add_usize (by simp; lia)]; simp; lia)
      acc' (w + if acc' < p then 1 else 0)
  else
    fin acc w
termination_by iEnd.toNat - i.toNat
decreasing_by
  rw [toNat_add_usize (by simp; lia)]; simp; lia

/-- Adding a word to a word: the sum modulo `2⁶⁴` and its wrap, which the comparison detects. -/
private theorem add_wrap (acc p : UInt64) :
    (acc + p).toNat + 2 ^ 64 * (if acc + p < p then 1 else 0) = acc.toNat + p.toNat := by
  have := acc.toNat_lt
  have := p.toNat_lt
  rw [UInt64.toNat_add]
  by_cases hc : acc.toNat + p.toNat < 2 ^ 64
  · rw [ite_eq_right (by rw [UInt64.lt_iff_toNat_lt, UInt64.toNat_add, Nat.mod_eq_of_lt hc]; lia),
      Nat.mod_eq_of_lt hc]
    simp
  · rw [ite_eq_left (by rw [UInt64.lt_iff_toNat_lt, UInt64.toNat_add]; lia)]
    lia

private theorem colLoopW_spec (aa : UInt32Array) (sa na : USize) (ha : aa.size < USize.size)
    (hA : sa.toNat + na.toNat ≤ aa.size) (bb : UInt32Array) (sb nb : USize)
    (hb : bb.size < USize.size) (hB : sb.toNat + nb.toNat ≤ bb.size)
    (k iEnd : USize) (hiE : iEnd.toNat ≤ na.toNat) (hiEk : iEnd.toNat ≤ k.toNat + 1)
    (fin : UInt64 → UInt64 → UInt32Array) (la lb : List UInt32)
    (hxa : ∀ j (_ : j < na.toNat), (aa[sa.toNat + j]'(by lia)).toNat = limbD la j)
    (hxb : ∀ j (_ : j < nb.toNat), (bb[sb.toNat + j]'(by lia)).toNat = limbD lb j)
    (c₀ : Nat) (i : USize) (hii : i.toNat ≤ iEnd.toNat) (hst : k.toNat + 1 ≤ nb.toNat + i.toNat)
    (acc w : UInt64)
    (hacc : acc.toNat + 2 ^ 64 * w.toNat = c₀ + colPart la lb k.toNat i.toNat)
    (hw : w.toNat + (iEnd.toNat - i.toNat) < 2 ^ 64) :
    ∃ acc' w' : UInt64, colLoopW aa sa na ha hA bb sb nb hb hB k iEnd hiE hiEk fin i hii hst
        acc w = fin acc' w' ∧
      acc'.toNat + 2 ^ 64 * w'.toNat = c₀ + colPart la lb k.toNat iEnd.toNat ∧
      w'.toNat ≤ w.toNat + (iEnd.toNat - i.toNat) := by
  induction hd : iEnd.toNat - i.toNat generalizing i acc w with
  | zero =>
    have hie : i.toNat = iEnd.toNat := by lia
    rw [colLoopW, dite_eq_right (by rw [USize.lt_iff_toNat_lt]; lia)]
    exact ⟨acc, w, rfl, by rw [hacc, hie], by lia⟩
  | succ d ih =>
    have h' : i.toNat < iEnd.toNat := by lia
    rw [colLoopW, dite_eq_left (show i < iEnd from h')]
    dsimp only
    have hi1 : (i + 1).toNat = i.toNat + 1 := by rw [toNat_add_usize (by simp; lia)]; simp
    have hki : (k - i).toNat = k.toNat - i.toNat :=
      USize.toNat_sub_of_le _ _ (USize.le_iff_toNat_le.2 (by lia))
    have hx : (limbU aa sa na ha hA i (by lia)).toNat = limbD la i.toNat := by
      rw [limbU_eq_getElem _ _ _ _ _ _ _ _ rfl, hxa _ (by lia)]
    have hy : (limbU bb sb nb hb hB (k - i) (by rw [hki]; lia)).toNat =
        limbD lb (k.toNat - i.toNat) := by
      rw [limbU_eq_getElem _ _ _ _ _ _ _ _ rfl]
      simp only [hki]
      rw [hxb _ (by lia)]
    generalize limbU aa sa na ha hA i _ = x at hx ⊢
    generalize limbU bb sb nb hb hB (k - i) _ = y at hy ⊢
    have hp : (x.toUInt64 * y.toUInt64).toNat = x.toNat * y.toNat := by
      rw [UInt64.toNat_mul, UInt32.toNat_toUInt64, UInt32.toNat_toUInt64]
      exact Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le (Nat.mul_lt_mul'' x.toNat_lt y.toNat_lt)
        (by decide))
    have hwrap := add_wrap acc (x.toUInt64 * y.toUInt64)
    generalize x.toUInt64 * y.toUInt64 = p at hp hwrap ⊢
    generalize hb' : (if acc + p < p then (1 : UInt64) else 0) = bit
    have hbit : (if acc + p < p then 1 else 0) = bit.toNat := by
      rw [← hb']; split <;> rfl
    rw [hbit] at hwrap
    have hbit1 : bit.toNat ≤ 1 := by rw [← hbit]; split <;> lia
    have hw' : (w + bit).toNat = w.toNat + bit.toNat := by
      rw [UInt64.toNat_add]; exact Nat.mod_eq_of_lt (by lia)
    obtain ⟨acc', w', heq, hacc', hw''⟩ := ih (i + 1) (by rw [hi1]; lia) (by rw [hi1]; lia)
      (acc + p) (w + bit)
      (by
        rw [hw', hi1, colPart, sumRange, ← colPart, ← hx, ← hy, ← hp]
        lia)
      (by rw [hw', hi1]; lia) (by rw [hi1]; lia)
    refine ⟨acc', w', heq, hacc', ?_⟩
    rw [hw'] at hw''
    lia

private theorem size_colLoopW (aa : UInt32Array) (sa na : USize) (ha : aa.size < USize.size)
    (hA : sa.toNat + na.toNat ≤ aa.size) (bb : UInt32Array) (sb nb : USize)
    (hb : bb.size < USize.size) (hB : sb.toNat + nb.toNat ≤ bb.size)
    (k iEnd : USize) (hiE : iEnd.toNat ≤ na.toNat) (hiEk : iEnd.toNat ≤ k.toNat + 1)
    (fin : UInt64 → UInt64 → UInt32Array) (S : Nat) (hfin : ∀ acc w, (fin acc w).size = S)
    (i : USize) (hii : i.toNat ≤ iEnd.toNat) (hst : k.toNat + 1 ≤ nb.toNat + i.toNat)
    (acc w : UInt64) :
    (colLoopW aa sa na ha hA bb sb nb hb hB k iEnd hiE hiEk fin i hii hst acc w).size = S := by
  induction hd : iEnd.toNat - i.toNat generalizing i acc w with
  | zero =>
    rw [colLoopW, dite_eq_right (by rw [USize.lt_iff_toNat_lt]; lia)]
    exact hfin _ _
  | succ d ih =>
    have h' : i.toNat < iEnd.toNat := by lia
    rw [colLoopW, dite_eq_left (show i < iEnd from h')]
    dsimp only
    apply ih
    rw [toNat_add_usize (by simp; lia)]; simp; lia

/--
`colLoopW` finished by writing the column into `r`, for the product: `acc + 2⁶⁴ w` as
`lo + β hi`, from the carry `lo + β hi` of the columns below.
-/
@[inline] def combaColW (aa : UInt32Array) (sa na : USize) (ha : aa.size < USize.size)
    (hA : sa.toNat + na.toNat ≤ aa.size) (bb : UInt32Array) (sb nb : USize)
    (hb : bb.size < USize.size) (hB : sb.toNat + nb.toNat ≤ bb.size)
    (k iEnd : USize) (hiE : iEnd.toNat ≤ na.toNat) (hiEk : iEnd.toNat ≤ k.toNat + 1)
    (r : UInt32Array) (hrs : r.size < USize.size) (hr : k.toNat + 2 < r.size)
    (i : USize) (hii : i.toNat ≤ iEnd.toNat) (hst : k.toNat + 1 ≤ nb.toNat + i.toNat)
    (lo hi : UInt64) : UInt32Array :=
  colLoopW aa sa na ha hA bb sb nb hb hB k iEnd hiE hiEk
    (fun acc w => writeCol r k hrs hr (acc &&& 0xFFFFFFFF) ((acc >>> 32) + (w <<< 32))) i hii hst
    (lo + (hi <<< 32)) 0

private theorem combaColW_spec (aa : UInt32Array) (sa na : USize) (ha : aa.size < USize.size)
    (hA : sa.toNat + na.toNat ≤ aa.size) (bb : UInt32Array) (sb nb : USize)
    (hb : bb.size < USize.size) (hB : sb.toNat + nb.toNat ≤ bb.size)
    (k iEnd : USize) (hiE : iEnd.toNat ≤ na.toNat) (hiEk : iEnd.toNat ≤ k.toNat + 1)
    (r : UInt32Array) (hrs : r.size < USize.size) (hr : k.toNat + 2 < r.size)
    (la lb : List UInt32)
    (hxa : ∀ j (hj : j < na.toNat), (aa[sa.toNat + j]'(by lia)).toNat = limbD la j)
    (hxb : ∀ j (hj : j < nb.toNat), (bb[sb.toNat + j]'(by lia)).toNat = limbD lb j)
    (c₀ : Nat) (i : USize) (hii : i.toNat ≤ iEnd.toNat) (hst : k.toNat + 1 ≤ nb.toNat + i.toNat)
    (lo hi : UInt64)
    (hacc : lo.toNat + 2 ^ 32 * hi.toNat = c₀ + colPart la lb k.toNat i.toNat)
    (hlo : lo.toNat < 2 ^ 32) (hhi : hi.toNat < 2 ^ 32)
    (hlen : iEnd.toNat - i.toNat ≤ 2 ^ 31) :
    ∃ lo' hi' : UInt64, combaColW aa sa na ha hA bb sb nb hb hB k iEnd hiE hiEk r hrs hr i hii hst
        lo hi = writeCol r k hrs hr lo' hi' ∧
      lo'.toNat + 2 ^ 32 * hi'.toNat = c₀ + colPart la lb k.toNat iEnd.toNat ∧
      hi'.toNat + 2 ^ 32 ≤ 2 ^ 64 := by
  have h₀ : (lo + (hi <<< 32)).toNat = lo.toNat + 2 ^ 32 * hi.toNat := by
    rw [UInt64.toNat_add, UInt64.toNat_shiftLeft]
    simp only [UInt64.reduceToNat, Nat.reduceMod, Nat.shiftLeft_eq]
    lia
  obtain ⟨acc', w', heq, hacc', hw'⟩ := colLoopW_spec aa sa na ha hA bb sb nb hb hB k iEnd hiE
    hiEk _ la lb hxa hxb c₀ i hii hst (lo + (hi <<< 32)) 0
    (by rw [h₀, hacc]; simp) (by simp; lia)
  simp only [UInt64.toNat_zero, Nat.zero_add] at hw'
  have hacc'β := acc'.toNat_lt
  have hl : (acc' &&& 0xFFFFFFFF).toNat = acc'.toNat % 2 ^ 32 := by
    rw [UInt64.toNat_and]
    exact Nat.and_two_pow_sub_one_eq_mod _ 32
  have hh : ((acc' >>> 32) + (w' <<< 32)).toNat = acc'.toNat / 2 ^ 32 + 2 ^ 32 * w'.toNat := by
    rw [UInt64.toNat_add, UInt64.toNat_shiftRight, UInt64.toNat_shiftLeft]
    simp only [UInt64.reduceToNat, Nat.reduceMod, Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow]
    lia
  refine ⟨_, _, heq, ?_, ?_⟩
  · rw [hl, hh, ← hacc']
    have := Nat.div_add_mod acc'.toNat (2 ^ 32)
    lia
  · rw [hh]; lia

private theorem size_combaColW (aa : UInt32Array) (sa na : USize) (ha : aa.size < USize.size)
    (hA : sa.toNat + na.toNat ≤ aa.size) (bb : UInt32Array) (sb nb : USize)
    (hb : bb.size < USize.size) (hB : sb.toNat + nb.toNat ≤ bb.size)
    (k iEnd : USize) (hiE : iEnd.toNat ≤ na.toNat) (hiEk : iEnd.toNat ≤ k.toNat + 1)
    (r : UInt32Array) (hrs : r.size < USize.size) (hr : k.toNat + 2 < r.size)
    (i : USize) (hii : i.toNat ≤ iEnd.toNat) (hst : k.toNat + 1 ≤ nb.toNat + i.toNat)
    (lo hi : UInt64) :
    (combaColW aa sa na ha hA bb sb nb hb hB k iEnd hiE hiEk r hrs hr i hii hst lo hi).size =
      r.size :=
  size_colLoopW _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (fun _ _ => by simp only [writeCol_eq,
    UInt32Array.size_set]) _ _ _ _ _

/-- The end of the products of column `k`: `min (k + 1) na`. -/
@[inline] def colEnd (k na : USize) : USize := if k + 1 < na then k + 1 else na

/-- The start of the products of column `k`: `k + 1 - nb`, or `0`. -/
@[inline] def colStart (k nb : USize) : USize := if nb ≤ k then k + 1 - nb else 0

private theorem toNat_colEnd (k na : USize) (hk : k.toNat + 1 < USize.size) :
    (colEnd k na).toNat = min (k.toNat + 1) na.toNat := by
  have h1 : (k + 1).toNat = k.toNat + 1 := by rw [toNat_add_usize (by simp; lia)]; simp
  unfold colEnd
  split
  · rename_i h; rw [USize.lt_iff_toNat_lt, h1] at h; rw [h1]; lia
  · rename_i h; rw [USize.lt_iff_toNat_lt, h1] at h; lia

private theorem toNat_colStart (k nb : USize) (hk : k.toNat + 1 < USize.size) :
    (colStart k nb).toNat = k.toNat + 1 - nb.toNat := by
  have h1 : (k + 1).toNat = k.toNat + 1 := by rw [toNat_add_usize (by simp; lia)]; simp
  unfold colStart
  split
  · rename_i h
    rw [USize.le_iff_toNat_le] at h
    rw [USize.toNat_sub_of_le _ _ (by rw [USize.le_iff_toNat_le, h1]; lia), h1]
  · rename_i h
    rw [USize.le_iff_toNat_le] at h
    simp; lia

/--
The columns `k` to `kEnd - 1` of the product, each with `combaCol`, the carry of each column
going up in `r[k + 1]` and `r[k + 2]`.
-/
def combaOuter (aa : UInt32Array) (sa na : USize) (ha : aa.size < USize.size)
    (hA : sa.toNat + na.toNat ≤ aa.size) (bb : UInt32Array) (sb nb : USize)
    (hb : bb.size < USize.size) (hB : sb.toNat + nb.toNat ≤ bb.size)
    (kEnd : USize) (hkE : kEnd.toNat + 1 = na.toNat + nb.toNat)
    (r : UInt32Array) (hrs : r.size < USize.size) (hr : r.size = kEnd.toNat + 2)
    (k : USize) (_hk : k.toNat ≤ kEnd.toNat) : UInt32Array :=
  if h : k < kEnd then
    have h' : k.toNat < kEnd.toNat := h
    have hk1 : k.toNat + 1 < USize.size := by lia
    let lo := (r.uget k (by lia)).toUInt64
    let hi := (r.uget (k + 1) (by rw [toNat_add_usize (by simp; lia)]; simp; lia)).toUInt64
    let r' := combaCol aa sa na ha hA bb sb nb hb hB k (colEnd k na)
      (by rw [toNat_colEnd _ _ hk1]; lia) (by rw [toNat_colEnd _ _ hk1]; lia) r hrs
      (by lia) (colStart k nb)
      (by rw [toNat_colEnd _ _ hk1, toNat_colStart _ _ hk1]; lia)
      (by rw [toNat_colStart _ _ hk1]; lia) lo hi
    combaOuter aa sa na ha hA bb sb nb hb hB kEnd hkE r'
      (by rw [size_combaCol]; exact hrs) (by rw [size_combaCol]; exact hr) (k + 1)
      (by rw [toNat_add_usize (by simp; lia)]; simp; lia)
  else
    r
termination_by kEnd.toNat - k.toNat
decreasing_by
  rw [toNat_add_usize (by simp; lia)]; simp; lia

/--
The columns `k` to `kEnd - 1` of the product, each with `combaColW`, the carry of each column
going up in `r[k + 1]` and `r[k + 2]`.
-/
def combaOuterW (aa : UInt32Array) (sa na : USize) (ha : aa.size < USize.size)
    (hA : sa.toNat + na.toNat ≤ aa.size) (bb : UInt32Array) (sb nb : USize)
    (hb : bb.size < USize.size) (hB : sb.toNat + nb.toNat ≤ bb.size)
    (kEnd : USize) (hkE : kEnd.toNat + 1 = na.toNat + nb.toNat)
    (r : UInt32Array) (hrs : r.size < USize.size) (hr : r.size = kEnd.toNat + 2)
    (k : USize) (_hk : k.toNat ≤ kEnd.toNat) : UInt32Array :=
  if h : k < kEnd then
    have h' : k.toNat < kEnd.toNat := h
    have hk1 : k.toNat + 1 < USize.size := by lia
    let lo := (r.uget k (by lia)).toUInt64
    let hi := (r.uget (k + 1) (by rw [toNat_add_usize (by simp; lia)]; simp; lia)).toUInt64
    let r' := combaColW aa sa na ha hA bb sb nb hb hB k (colEnd k na)
      (by rw [toNat_colEnd _ _ hk1]; lia) (by rw [toNat_colEnd _ _ hk1]; lia) r hrs
      (by lia) (colStart k nb)
      (by rw [toNat_colEnd _ _ hk1, toNat_colStart _ _ hk1]; lia)
      (by rw [toNat_colStart _ _ hk1]; lia) lo hi
    combaOuterW aa sa na ha hA bb sb nb hb hB kEnd hkE r'
      (by rw [size_combaColW]; exact hrs) (by rw [size_combaColW]; exact hr) (k + 1)
      (by rw [toNat_add_usize (by simp; lia)]; simp; lia)
  else
    r
termination_by kEnd.toNat - k.toNat
decreasing_by
  rw [toNat_add_usize (by simp; lia)]; simp; lia

private theorem limbD_of_length_le {l : List UInt32} {j : Nat} (h : l.length ≤ j) :
    limbD l j = 0 := by
  simp [limbD, List.getD_eq_getElem?_getD, List.getElem?_eq_none h]

private theorem limbD_lt (l : List UInt32) (j : Nat) : limbD l j < 2 ^ 32 :=
  UInt32.toNat_lt _

private theorem colPart_le (la lb : List UInt32) (k t : Nat) :
    colPart la lb k t ≤ t * 2 ^ 64 := by
  induction t with
  | zero => simp [colPart, sumRange]
  | succ t ih =>
    rw [colPart, sumRange, ← colPart, Nat.succ_mul]
    have := Nat.mul_le_mul (Nat.le_of_lt (limbD_lt la t)) (Nat.le_of_lt (limbD_lt lb (k - t)))
    have : (2 : Nat) ^ 32 * 2 ^ 32 = 2 ^ 64 := by decide
    lia

/-- The products of column `k` below `k + 1 - nb` read limbs of `lb` past its end. -/
private theorem colPart_start (la lb : List UInt32) (k : Nat) :
    colPart la lb k (k + 1 - lb.length) = 0 := by
  rw [colPart, sumRange_extend (n := 0) (Nat.zero_le _) (fun i _ hi => by
    rw [limbD_of_length_le (l := lb) (by lia), Nat.mul_zero])]
  rfl

/-- The products of column `k` from `la.length` on read limbs of `la` past its end. -/
private theorem colPart_end (la lb : List UInt32) (k : Nat) :
    colPart la lb k (min (k + 1) la.length) = colSum la lb k := by
  unfold colSum colPart
  exact (sumRange_extend (Nat.min_le_left _ _) (fun i hi _ => by
    rw [limbD_of_length_le (l := la) (by lia), Nat.zero_mul])).symm

private theorem combaOuter_spec (aa : UInt32Array) (sa na : USize) (ha : aa.size < USize.size)
    (hA : sa.toNat + na.toNat ≤ aa.size) (bb : UInt32Array) (sb nb : USize)
    (hb : bb.size < USize.size) (hB : sb.toNat + nb.toNat ≤ bb.size)
    (kEnd : USize) (hkE : kEnd.toNat + 1 = na.toNat + nb.toNat)
    (la lb : List UInt32) (hla : la.length = na.toNat) (hlb : lb.length = nb.toNat)
    (hxa : ∀ j (hj : j < na.toNat), (aa[sa.toNat + j]'(by lia)).toNat = limbD la j)
    (hxb : ∀ j (hj : j < nb.toNat), (bb[sb.toNat + j]'(by lia)).toNat = limbD lb j)
    (hna : na.toNat < 2 ^ 31)
    (r : UInt32Array) (hrs : r.size < USize.size) (hr : r.size = kEnd.toNat + 2)
    (k : USize) (hk : k.toNat ≤ kEnd.toNat)
    (hv : ofLimbs r.toList = weighted la lb k.toNat)
    (hz : ∀ j, k.toNat + 2 ≤ j → ∀ (hj' : j < r.size), r[j] = 0) :
    ofLimbs (combaOuter aa sa na ha hA bb sb nb hb hB kEnd hkE r hrs hr k hk).toList =
      weighted la lb kEnd.toNat := by
  induction hd : kEnd.toNat - k.toNat generalizing k r with
  | zero =>
    rw [combaOuter, dite_eq_right (by rw [USize.lt_iff_toNat_lt]; lia)]
    rw [hv, show k.toNat = kEnd.toNat by lia]
  | succ d ih =>
    have h' : k.toNat < kEnd.toNat := by lia
    have hk1 : k.toNat + 1 < USize.size := by lia
    have hk1' : (k + 1).toNat = k.toNat + 1 := by rw [toNat_add_usize (by simp; lia)]; simp
    rw [combaOuter, dite_eq_left (show k < kEnd from h')]
    dsimp only
    -- The carry in `r[k]`, `r[k + 1]`, and the column with `combaCol`.
    have hlo : ((r.uget k (by lia)).toUInt64).toNat = (r[k.toNat]'(by lia)).toNat := by
      rw [UInt32.toNat_toUInt64, uget_eq_getElem _ _ _ rfl]
    have hhi : ((r.uget (k + 1) (by rw [hk1']; lia)).toUInt64).toNat =
        (r[k.toNat + 1]'(by lia)).toNat := by
      rw [UInt32.toNat_toUInt64, uget_eq_getElem _ _ _ hk1']
    have hr₀ := (r[k.toNat]'(by lia)).toNat_lt
    have hr₁ := (r[k.toNat + 1]'(by lia)).toNat_lt
    have hr₂ : r[k.toNat + 2]'(by lia) = 0 := hz _ (Nat.le_refl _) (by lia)
    have hE := toNat_colEnd k na hk1
    have hS := toNat_colStart k nb hk1
    obtain ⟨lo', hi', heq, hacc, hhi'⟩ := combaCol_spec aa sa na ha hA bb sb nb hb hB k
      (colEnd k na) (by lia) (by lia) r hrs (by lia) la lb hxa hxb
      ((r[k.toNat]'(by lia)).toNat + 2 ^ 32 * (r[k.toNat + 1]'(by lia)).toNat)
      (colStart k nb) (by lia) (by lia) (r.uget k (by lia)).toUInt64
      (r.uget (k + 1) (by rw [hk1']; lia)).toUInt64
      (by rw [hlo, hhi, hS, ← hlb, colPart_start]; rfl)
      (by rw [hlo]; have := Nat.mul_le_mul_right (2 ^ 32) (show (colEnd k na).toNat -
            (colStart k nb).toNat ≤ 2 ^ 31 by lia); lia)
      (by rw [hhi]; have := Nat.mul_le_mul_right (2 ^ 32) (show (colEnd k na).toNat -
            (colStart k nb).toNat + 1 ≤ 2 ^ 31 by lia); lia)
    rw [hE, ← hla, colPart_end] at hacc
    have hcol : colSum la lb k.toNat ≤ na.toNat * 2 ^ 64 := by
      rw [← colPart_end, hla]
      exact Nat.le_trans (colPart_le _ _ _ _) (Nat.mul_le_mul_right _ (Nat.min_le_right _ _))
    obtain ⟨hs', hz', hv'⟩ := writeCol_spec r k hrs (by lia) lo' hi'
      (by rw [hacc]; have := Nat.mul_le_mul_right (2 ^ 64) (Nat.le_of_lt hna); lia) hhi'
    -- `weighted (k + 1) = weighted k + βᵏ colSum k`.
    simp only [heq]
    have hw : weighted la lb (k.toNat + 1) =
        weighted la lb k.toNat + 2 ^ (32 * k.toNat) * colSum la lb k.toNat := rfl
    apply ih
    · rw [hk1', hw, ← hv]
      simp only [hr₂, UInt32.toNat_zero, Nat.mul_zero, Nat.add_zero] at hv'
      rw [hacc] at hv'
      generalize (r[k.toNat]'(by lia)).toNat + 2 ^ 32 * (r[k.toNat + 1]'(by lia)).toNat = A
        at hv'
      rw [Nat.mul_add] at hv'
      lia
    · intro j hj hj'
      rw [hk1'] at hj
      rw [hz' j (by lia) (by rw [hs'] at hj'; exact hj')]
      exact hz j (by lia) _
    · rw [hk1']; lia

private theorem size_combaOuter (aa : UInt32Array) (sa na : USize) (ha : aa.size < USize.size)
    (hA : sa.toNat + na.toNat ≤ aa.size) (bb : UInt32Array) (sb nb : USize)
    (hb : bb.size < USize.size) (hB : sb.toNat + nb.toNat ≤ bb.size)
    (kEnd : USize) (hkE : kEnd.toNat + 1 = na.toNat + nb.toNat)
    (r : UInt32Array) (hrs : r.size < USize.size) (hr : r.size = kEnd.toNat + 2)
    (k : USize) (hk : k.toNat ≤ kEnd.toNat) :
    (combaOuter aa sa na ha hA bb sb nb hb hB kEnd hkE r hrs hr k hk).size = kEnd.toNat + 2 := by
  induction hd : kEnd.toNat - k.toNat generalizing k r with
  | zero =>
    rw [combaOuter, dite_eq_right (by rw [USize.lt_iff_toNat_lt]; lia)]
    exact hr
  | succ d ih =>
    have h' : k.toNat < kEnd.toNat := by lia
    rw [combaOuter, dite_eq_left (show k < kEnd from h')]
    dsimp only
    apply ih
    rw [toNat_add_usize (by simp; lia)]; simp; lia

private theorem combaOuterW_spec (aa : UInt32Array) (sa na : USize) (ha : aa.size < USize.size)
    (hA : sa.toNat + na.toNat ≤ aa.size) (bb : UInt32Array) (sb nb : USize)
    (hb : bb.size < USize.size) (hB : sb.toNat + nb.toNat ≤ bb.size)
    (kEnd : USize) (hkE : kEnd.toNat + 1 = na.toNat + nb.toNat)
    (la lb : List UInt32) (hla : la.length = na.toNat) (hlb : lb.length = nb.toNat)
    (hxa : ∀ j (hj : j < na.toNat), (aa[sa.toNat + j]'(by lia)).toNat = limbD la j)
    (hxb : ∀ j (hj : j < nb.toNat), (bb[sb.toNat + j]'(by lia)).toNat = limbD lb j)
    (hna : na.toNat < 2 ^ 31)
    (r : UInt32Array) (hrs : r.size < USize.size) (hr : r.size = kEnd.toNat + 2)
    (k : USize) (hk : k.toNat ≤ kEnd.toNat)
    (hv : ofLimbs r.toList = weighted la lb k.toNat)
    (hz : ∀ j, k.toNat + 2 ≤ j → ∀ (hj' : j < r.size), r[j] = 0) :
    ofLimbs (combaOuterW aa sa na ha hA bb sb nb hb hB kEnd hkE r hrs hr k hk).toList =
      weighted la lb kEnd.toNat := by
  induction hd : kEnd.toNat - k.toNat generalizing k r with
  | zero =>
    rw [combaOuterW, dite_eq_right (by rw [USize.lt_iff_toNat_lt]; lia)]
    rw [hv, show k.toNat = kEnd.toNat by lia]
  | succ d ih =>
    have h' : k.toNat < kEnd.toNat := by lia
    have hk1 : k.toNat + 1 < USize.size := by lia
    have hk1' : (k + 1).toNat = k.toNat + 1 := by rw [toNat_add_usize (by simp; lia)]; simp
    rw [combaOuterW, dite_eq_left (show k < kEnd from h')]
    dsimp only
    -- The carry in `r[k]`, `r[k + 1]`, and the column with `combaCol`.
    have hlo : ((r.uget k (by lia)).toUInt64).toNat = (r[k.toNat]'(by lia)).toNat := by
      rw [UInt32.toNat_toUInt64, uget_eq_getElem _ _ _ rfl]
    have hhi : ((r.uget (k + 1) (by rw [hk1']; lia)).toUInt64).toNat =
        (r[k.toNat + 1]'(by lia)).toNat := by
      rw [UInt32.toNat_toUInt64, uget_eq_getElem _ _ _ hk1']
    have hr₀ := (r[k.toNat]'(by lia)).toNat_lt
    have hr₁ := (r[k.toNat + 1]'(by lia)).toNat_lt
    have hr₂ : r[k.toNat + 2]'(by lia) = 0 := hz _ (Nat.le_refl _) (by lia)
    have hE := toNat_colEnd k na hk1
    have hS := toNat_colStart k nb hk1
    obtain ⟨lo', hi', heq, hacc, hhi'⟩ := combaColW_spec aa sa na ha hA bb sb nb hb hB k
      (colEnd k na) (by lia) (by lia) r hrs (by lia) la lb hxa hxb
      ((r[k.toNat]'(by lia)).toNat + 2 ^ 32 * (r[k.toNat + 1]'(by lia)).toNat)
      (colStart k nb) (by lia) (by lia) (r.uget k (by lia)).toUInt64
      (r.uget (k + 1) (by rw [hk1']; lia)).toUInt64
      (by rw [hlo, hhi, hS, ← hlb, colPart_start]; rfl)
      (by rw [hlo]; exact hr₀) (by rw [hhi]; exact hr₁) (by lia)
    rw [hE, ← hla, colPart_end] at hacc
    have hcol : colSum la lb k.toNat ≤ na.toNat * 2 ^ 64 := by
      rw [← colPart_end, hla]
      exact Nat.le_trans (colPart_le _ _ _ _) (Nat.mul_le_mul_right _ (Nat.min_le_right _ _))
    obtain ⟨hs', hz', hv'⟩ := writeCol_spec r k hrs (by lia) lo' hi'
      (by rw [hacc]; have := Nat.mul_le_mul_right (2 ^ 64) (Nat.le_of_lt hna); lia) hhi'
    -- `weighted (k + 1) = weighted k + βᵏ colSum k`.
    simp only [heq]
    have hw : weighted la lb (k.toNat + 1) =
        weighted la lb k.toNat + 2 ^ (32 * k.toNat) * colSum la lb k.toNat := rfl
    apply ih
    · rw [hk1', hw, ← hv]
      simp only [hr₂, UInt32.toNat_zero, Nat.mul_zero, Nat.add_zero] at hv'
      rw [hacc] at hv'
      generalize (r[k.toNat]'(by lia)).toNat + 2 ^ 32 * (r[k.toNat + 1]'(by lia)).toNat = A
        at hv'
      rw [Nat.mul_add] at hv'
      lia
    · intro j hj hj'
      rw [hk1'] at hj
      rw [hz' j (by lia) (by rw [hs'] at hj'; exact hj')]
      exact hz j (by lia) _
    · rw [hk1']; lia

private theorem size_combaOuterW (aa : UInt32Array) (sa na : USize) (ha : aa.size < USize.size)
    (hA : sa.toNat + na.toNat ≤ aa.size) (bb : UInt32Array) (sb nb : USize)
    (hb : bb.size < USize.size) (hB : sb.toNat + nb.toNat ≤ bb.size)
    (kEnd : USize) (hkE : kEnd.toNat + 1 = na.toNat + nb.toNat)
    (r : UInt32Array) (hrs : r.size < USize.size) (hr : r.size = kEnd.toNat + 2)
    (k : USize) (hk : k.toNat ≤ kEnd.toNat) :
    (combaOuterW aa sa na ha hA bb sb nb hb hB kEnd hkE r hrs hr k hk).size = kEnd.toNat + 2 := by
  induction hd : kEnd.toNat - k.toNat generalizing k r with
  | zero =>
    rw [combaOuterW, dite_eq_right (by rw [USize.lt_iff_toNat_lt]; lia)]
    exact hr
  | succ d ih =>
    have h' : k.toNat < kEnd.toNat := by lia
    rw [combaOuterW, dite_eq_left (show k < kEnd from h')]
    dsimp only
    apply ih
    rw [toNat_add_usize (by simp; lia)]; simp; lia

private theorem mod_usize {n : Nat} (h : n < USize.size) : n % 2 ^ System.Platform.numBits = n :=
  Nat.mod_eq_of_lt (by rwa [← USize.size_eq_two_pow])

/-- The conditions under which `combaMul` runs: nonempty operands, and sizes that fit. -/
@[expose] public def CombaOK (a b : UInt32Array.Slice) : Prop :=
  0 < a.size ∧ 0 < b.size ∧ a.size + b.size < 2147483648 ∧ a.array.size < 4294967295 ∧
    b.array.size < 4294967295

public instance (a b : UInt32Array.Slice) : Decidable (CombaOK a b) := by
  unfold CombaOK; infer_instance

private theorem slice_size_le (a : UInt32Array.Slice) : a.size ≤ a.array.size := by
  have := a.stop_le_array_size; have := a.size_eq; lia

/--
All `a.size + b.size` limbs of `a * b` by Comba's method, one column at a time, into
`a.size + b.size + 1` limbs whose top limb, which only held a carry, is dropped. The columns come
from `combaOuter` when either operand is shorter than 32 limbs and from `combaOuterW` otherwise:
the column loop of `combaOuterW` adds whole products and counts the wraps of its sum, which is
5–13% faster from 32 limbs, but setting up its unrolled loop for each column made products of 2
to 16 limbs 5–8% slower, also when both loops shared one function and chose by column length.
-/
public def combaMul (a b : UInt32Array.Slice) (h : CombaOK a b) : UInt32Array :=
  have ha := lt_usizeSize h.2.2.2.1
  have hb := lt_usizeSize h.2.2.2.2
  have hla := slice_size_le a
  have hlb := slice_size_le b
  have hn : a.size + b.size + 1 < USize.size := lt_usizeSize (by have := h.2.2.1; lia)
  have hkE : (a.size + b.size - 1).toUSize.toNat + 1 =
      a.size.toUSize.toNat + b.size.toUSize.toNat := by
    have := mod_usize (n := a.size + b.size - 1) (by lia)
    have := mod_usize (n := a.size) (by lia); have := mod_usize (n := b.size) (by lia)
    have := h.1; simp; lia
  have hrs : (UInt32Array.replicate (a.size + b.size + 1) 0).size < USize.size := by
    rw [UInt32Array.size_replicate]; exact hn
  have hr0 : (UInt32Array.replicate (a.size + b.size + 1) 0).size =
      (a.size + b.size - 1).toUSize.toNat + 2 := by
    have := mod_usize (n := a.size + b.size - 1) (by lia); have := h.1; simp; lia
  if a.size < 32 ∨ b.size < 32 then
    (combaOuter a.array a.start.toUSize a.size.toUSize ha (limbU_bound a ha)
      b.array b.start.toUSize b.size.toUSize hb (limbU_bound b hb) (a.size + b.size - 1).toUSize
      hkE (.replicate (a.size + b.size + 1) 0) hrs hr0 0 (by simp)).pop
  else
    (combaOuterW a.array a.start.toUSize a.size.toUSize ha (limbU_bound a ha)
      b.array b.start.toUSize b.size.toUSize hb (limbU_bound b hb) (a.size + b.size - 1).toUSize
      hkE (.replicate (a.size + b.size + 1) 0) hrs hr0 0 (by simp)).pop

/-- The limbs of a slice as `combaOuter` reads them. -/
private theorem limbs_read (a : UInt32Array.Slice) (has : a.array.size < USize.size) (j : Nat)
    (hj : j < a.size.toUSize.toNat) :
    (a.array[a.start.toUSize.toNat + j]'(by have := limbU_bound a has; lia)).toNat =
      limbD a.copy.toList j := by
  have hla := slice_size_le a
  have hst : a.start.toUSize.toNat = a.start := toNat_toUSize (by
    have := a.start_le_stop; have := a.stop_le_array_size; lia)
  have hsz : a.size.toUSize.toNat = a.size := toNat_toUSize (by lia)
  rw [hsz] at hj
  have := a.stop_le_array_size; have := a.size_eq; have := a.start_le_stop
  have e : ∀ i (hi : i < a.array.size), i = a.start + j →
      a.array[i] = a.array[a.start + j]'(by lia) := by
    intro i hi he; subst he; rfl
  rw [e _ _ (by rw [hst]), limbD, ← getD_eq_getD_toList_copy, UInt32Array.Slice.getD_eq,
    dite_eq_left hj, UInt32Array.Slice.getElem_eq]

/-- The limbs of `a * b` with a zero limb on top, which `pop` removes. -/
private theorem pop_of_toNat_eq_mul (a b : UInt32Array.Slice) (r : UInt32Array)
    (hrsz : r.size = a.size + b.size + 1) (hv : ofLimbs r.toList = toNat a * toNat b) :
    r.pop.size = a.size + b.size ∧ toNat r.pop = toNat a * toNat b := by
  -- The top limb is zero: `a b < β^(a.size + b.size)`.
  have hlt : ofLimbs r.toList < 2 ^ (32 * (a.size + b.size)) := by
    rw [hv, Nat.mul_add, Nat.pow_add]
    have hA := toNat_lt a; have hB := toNat_lt b
    exact Nat.mul_lt_mul'' hA hB
  have htop := getElem_eq_zero_of_ofLimbs_lt (l := r.toList) (k := a.size + b.size)
    (by simp; lia) hlt
  have hne : r.toList ≠ [] := by
    intro h'; have := congrArg List.length h'; simp at this; lia
  have hlast : r.toList.getLast hne = 0 := by
    rw [List.getLast_eq_getElem]; simpa [hrsz] using htop
  refine ⟨by simp [hrsz], ?_⟩
  rw [toNat_toSlice, UInt32Array.toList_pop, ← hv]
  conv => rhs; rw [← List.dropLast_concat_getLast hne, hlast]
  rw [ofLimbs_concat, UInt32.toNat_zero, Nat.mul_zero, Nat.add_zero]

public theorem combaMul_spec (a b : UInt32Array.Slice) (h : CombaOK a b) :
    (combaMul a b h).size = a.size + b.size ∧ toNat (combaMul a b h) = toNat a * toNat b := by
  have ha := lt_usizeSize h.2.2.2.1
  have hb := lt_usizeSize h.2.2.2.2
  have hla := slice_size_le a
  have hlb := slice_size_le b
  have hsa : a.size.toUSize.toNat = a.size := toNat_toUSize (by lia)
  have hsb : b.size.toUSize.toNat = b.size := toNat_toUSize (by lia)
  have hn : a.size + b.size + 1 < USize.size := lt_usizeSize (by have := h.2.2.1; lia)
  have hkE' : (a.size + b.size - 1).toUSize.toNat = a.size + b.size - 1 := toNat_toUSize (by lia)
  have hkE : (a.size + b.size - 1).toUSize.toNat + 1 =
      a.size.toUSize.toNat + b.size.toUSize.toNat := by
    have := h.1; lia
  have hrs : (UInt32Array.replicate (a.size + b.size + 1) 0).size < USize.size := by
    rw [UInt32Array.size_replicate]; exact hn
  have hr0 : (UInt32Array.replicate (a.size + b.size + 1) 0).size =
      (a.size + b.size - 1).toUSize.toNat + 2 := by
    have := h.1; simp; lia
  -- Both outer loops leave the weighted column sums, `a b` with a zero limb on top.
  have hfin (r : UInt32Array) (hsize : r.size = (a.size + b.size - 1).toUSize.toNat + 2)
      (hspec : ofLimbs r.toList =
        weighted a.copy.toList b.copy.toList (a.size + b.size - 1).toUSize.toNat) :
      r.pop.size = a.size + b.size ∧ toNat r.pop = toNat a * toNat b :=
    pop_of_toNat_eq_mul a b r (by rw [hsize]; have := h.1; lia)
      (by rw [hspec, hkE', weighted_eq _ _ _ (by simp; lia)]; rfl)
  have hv0 : ofLimbs (UInt32Array.replicate (a.size + b.size + 1) 0).toList =
      weighted a.copy.toList b.copy.toList (0 : USize).toNat := by
    simp [weighted, UInt32Array.toList_replicate, ofLimbs_replicate_zero]
  by_cases hw : a.size < 32 ∨ b.size < 32
  · have heq : combaMul a b h = (combaOuter a.array a.start.toUSize a.size.toUSize ha
        (limbU_bound a ha) b.array b.start.toUSize b.size.toUSize hb (limbU_bound b hb)
        (a.size + b.size - 1).toUSize hkE (UInt32Array.replicate (a.size + b.size + 1) 0) hrs hr0
        0 (by simp)).pop := by
      unfold combaMul; simp only [hw, ↓reduceIte]
    rw [heq]
    exact hfin _ (size_combaOuter _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _)
      (combaOuter_spec a.array a.start.toUSize a.size.toUSize ha (limbU_bound a ha)
        b.array b.start.toUSize b.size.toUSize hb (limbU_bound b hb) _ hkE
        a.copy.toList b.copy.toList (by simp [hsa]) (by simp [hsb]) (limbs_read a ha)
        (limbs_read b hb) (by rw [hsa]; have := h.2.2.1; lia) _ hrs hr0 0 (by simp) hv0
        (fun j _ _ => by simp))
  · have heq : combaMul a b h = (combaOuterW a.array a.start.toUSize a.size.toUSize ha
        (limbU_bound a ha) b.array b.start.toUSize b.size.toUSize hb (limbU_bound b hb)
        (a.size + b.size - 1).toUSize hkE (UInt32Array.replicate (a.size + b.size + 1) 0) hrs hr0
        0 (by simp)).pop := by
      unfold combaMul; simp only [hw, ↓reduceIte]
    rw [heq]
    exact hfin _ (size_combaOuterW _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _)
      (combaOuterW_spec a.array a.start.toUSize a.size.toUSize ha (limbU_bound a ha)
        b.array b.start.toUSize b.size.toUSize hb (limbU_bound b hb) _ hkE
        a.copy.toList b.copy.toList (by simp [hsa]) (by simp [hsb]) (limbs_read a ha)
        (limbs_read b hb) (by rw [hsa]; have := h.2.2.1; lia) _ hrs hr0 0 (by simp) hv0
        (fun j _ _ => by simp))

/-! ## Squares -/

/-- The diagonal term of column `k`, `a_{k/2}²` when `k` is even, as a word. -/
@[inline] def diagWord (aa : UInt32Array) (sa na : USize) (ha : aa.size < USize.size)
    (hA : sa.toNat + na.toNat ≤ aa.size) (k : USize) (hk : (k / 2).toNat < na.toNat) : UInt64 :=
  if k % 2 = 0 then
    let x := (limbU aa sa na ha hA (k / 2) hk).toUInt64
    x * x
  else 0

private theorem toNat_diagWord (aa : UInt32Array) (sa na : USize) (ha : aa.size < USize.size)
    (hA : sa.toNat + na.toNat ≤ aa.size) (k : USize) (hk : (k / 2).toNat < na.toNat)
    (la : List UInt32)
    (hxa : ∀ j (_ : j < na.toNat), (aa[sa.toNat + j]'(by lia)).toNat = limbD la j) :
    (diagWord aa sa na ha hA k hk).toNat = sqDiagCol la k.toNat := by
  rw [diagWord, sqDiagCol]
  have hmod : (k % 2 = 0) ↔ k.toNat % 2 = 0 := by
    rw [← USize.toNat_inj, USize.toNat_mod]; simp
  have hdiv : (k / 2).toNat = k.toNat / 2 := by rw [USize.toNat_div]; simp
  by_cases hk2 : k.toNat % 2 = 0
  · rw [ite_eq_left (hmod.2 hk2), ite_eq_left hk2]
    have hx : (limbU aa sa na ha hA (k / 2) hk).toNat = limbD la (k.toNat / 2) := by
      rw [limbU_eq_getElem _ _ _ _ _ _ _ _ rfl]
      simp only [hdiv]
      rw [hxa _ (by rw [← hdiv]; exact hk)]
    rw [UInt64.toNat_mul, UInt32.toNat_toUInt64, hx]
    exact Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le (Nat.mul_lt_mul'' (limbD_lt _ _)
      (limbD_lt _ _)) (by decide))
  · rw [ite_eq_right (fun h => hk2 (hmod.1 h)), ite_eq_right hk2]
    rfl

/--
The columns `k` to `kEnd - 1` of the square of `a`: the products of each column below the
diagonal with `colLoop`, then twice them, the diagonal and the carry written with `writeCol`.
-/
def csqOuter (aa : UInt32Array) (sa na : USize) (ha : aa.size < USize.size)
    (hA : sa.toNat + na.toNat ≤ aa.size) (kEnd : USize) (hkE : kEnd.toNat + 1 = 2 * na.toNat)
    (r : UInt32Array) (hrs : r.size < USize.size) (hr : r.size = kEnd.toNat + 2)
    (k : USize) (_hk : k.toNat ≤ kEnd.toNat) : UInt32Array :=
  if h : k < kEnd then
    have h' : k.toNat < kEnd.toNat := h
    have hk1 : k.toNat + 1 < USize.size := by lia
    have hk1' : (k + 1).toNat = k.toNat + 1 := by rw [toNat_add_usize (by simp; lia)]; simp
    have he : ((k + 1) / 2).toNat = (k.toNat + 1) / 2 := by rw [USize.toNat_div, hk1']; simp
    have hS := toNat_colStart k na hk1
    let d := diagWord aa sa na ha hA k (by rw [USize.toNat_div]; simp; lia)
    let c₀ := (r.uget k (by lia)).toUInt64
    let c₁ := (r.uget (k + 1) (by rw [hk1']; lia)).toUInt64
    let r' := colLoop aa sa na ha hA aa sa na ha hA k ((k + 1) / 2) (by rw [he]; lia)
      (by rw [he]; lia)
      (fun lo hi => writeCol r k hrs (by lia) (lo + lo + (d &&& 0xFFFFFFFF) + c₀)
        (hi + hi + (d >>> 32) + c₁))
      (colStart k na) (by rw [he, hS]; lia) (by rw [hS]; lia) 0 0
    csqOuter aa sa na ha hA kEnd hkE r'
      (by rw [size_colLoop _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ r.size (fun _ _ => by
            simp only [writeCol_eq, UInt32Array.size_set])]; exact hrs)
      (by rw [size_colLoop _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ r.size (fun _ _ => by
            simp only [writeCol_eq, UInt32Array.size_set])]; exact hr)
      (k + 1) (by rw [hk1']; lia)
  else
    r
termination_by kEnd.toNat - k.toNat
decreasing_by
  rw [toNat_add_usize (by simp; lia)]; simp; lia

private theorem size_csqOuter (aa : UInt32Array) (sa na : USize) (ha : aa.size < USize.size)
    (hA : sa.toNat + na.toNat ≤ aa.size) (kEnd : USize) (hkE : kEnd.toNat + 1 = 2 * na.toNat)
    (r : UInt32Array) (hrs : r.size < USize.size) (hr : r.size = kEnd.toNat + 2)
    (k : USize) (hk : k.toNat ≤ kEnd.toNat) :
    (csqOuter aa sa na ha hA kEnd hkE r hrs hr k hk).size = kEnd.toNat + 2 := by
  induction hd : kEnd.toNat - k.toNat generalizing k r with
  | zero =>
    rw [csqOuter, dite_eq_right (by rw [USize.lt_iff_toNat_lt]; lia)]
    exact hr
  | succ d ih =>
    have h' : k.toNat < kEnd.toNat := by lia
    rw [csqOuter, dite_eq_left (show k < kEnd from h')]
    dsimp only
    apply ih
    rw [toNat_add_usize (by simp; lia)]; simp; lia

private theorem csqOuter_spec (aa : UInt32Array) (sa na : USize) (ha : aa.size < USize.size)
    (hA : sa.toNat + na.toNat ≤ aa.size) (kEnd : USize) (hkE : kEnd.toNat + 1 = 2 * na.toNat)
    (la : List UInt32) (hla : la.length = na.toNat)
    (hxa : ∀ j (_ : j < na.toNat), (aa[sa.toNat + j]'(by lia)).toNat = limbD la j)
    (hna : na.toNat < 2 ^ 30)
    (r : UInt32Array) (hrs : r.size < USize.size) (hr : r.size = kEnd.toNat + 2)
    (k : USize) (hk : k.toNat ≤ kEnd.toNat)
    (hv : ofLimbs r.toList = weighted la la k.toNat)
    (hz : ∀ j, k.toNat + 2 ≤ j → ∀ (hj' : j < r.size), r[j] = 0) :
    ofLimbs (csqOuter aa sa na ha hA kEnd hkE r hrs hr k hk).toList =
      weighted la la kEnd.toNat := by
  induction hd : kEnd.toNat - k.toNat generalizing k r with
  | zero =>
    rw [csqOuter, dite_eq_right (by rw [USize.lt_iff_toNat_lt]; lia)]
    rw [hv, show k.toNat = kEnd.toNat by lia]
  | succ d ih =>
    have h' : k.toNat < kEnd.toNat := by lia
    have hk1 : k.toNat + 1 < USize.size := by lia
    have hk1' : (k + 1).toNat = k.toNat + 1 := by rw [toNat_add_usize (by simp; lia)]; simp
    have he : ((k + 1) / 2).toNat = (k.toNat + 1) / 2 := by rw [USize.toNat_div, hk1']; simp
    have hS := toNat_colStart k na hk1
    rw [csqOuter, dite_eq_left (show k < kEnd from h')]
    dsimp only
    have hc₀ : ((r.uget k (by lia)).toUInt64).toNat = (r[k.toNat]'(by lia)).toNat := by
      rw [UInt32.toNat_toUInt64, uget_eq_getElem _ _ _ rfl]
    have hc₁ : ((r.uget (k + 1) (by rw [hk1']; lia)).toUInt64).toNat =
        (r[k.toNat + 1]'(by lia)).toNat := by
      rw [UInt32.toNat_toUInt64, uget_eq_getElem _ _ _ hk1']
    have hr₀ := (r[k.toNat]'(by lia)).toNat_lt
    have hr₁ := (r[k.toNat + 1]'(by lia)).toNat_lt
    have hr₂ : r[k.toNat + 2]'(by lia) = 0 := hz _ (Nat.le_refl _) (by lia)
    -- The diagonal term.
    have hdk : (k / 2).toNat < na.toNat := by rw [USize.toNat_div]; simp; lia
    have hdd := toNat_diagWord aa sa na ha hA k hdk la hxa
    have hdlo : ((diagWord aa sa na ha hA k hdk) &&& 0xFFFFFFFF).toNat =
        (diagWord aa sa na ha hA k hdk).toNat % 2 ^ 32 := by
      rw [UInt64.toNat_and]; exact Nat.and_two_pow_sub_one_eq_mod _ 32
    have hdhi : ((diagWord aa sa na ha hA k hdk) >>> 32).toNat =
        (diagWord aa sa na ha hA k hdk).toNat / 2 ^ 32 := by
      rw [UInt64.toNat_shiftRight]; simp [Nat.shiftRight_eq_div_pow]
    have hdβ := (diagWord aa sa na ha hA k hdk).toNat_lt
    -- The products below the diagonal, from zero.
    obtain ⟨lo', hi', heq, hacc, hlo', hhi'⟩ := colLoop_spec aa sa na ha hA aa sa na ha hA k
      ((k + 1) / 2) (by rw [he]; lia) (by rw [he]; lia)
      (fun lo hi => writeCol r k hrs (by lia)
        (lo + lo + ((diagWord aa sa na ha hA k hdk) &&& 0xFFFFFFFF) +
          (r.uget k (by lia)).toUInt64)
        (hi + hi + ((diagWord aa sa na ha hA k hdk) >>> 32) +
          (r.uget (k + 1) (by rw [hk1']; lia)).toUInt64))
      la la hxa hxa 0 (colStart k na)
      (by rw [he, hS]; lia) (by rw [hS]; lia) 0 0
      (by rw [hS, ← hla, colPart_start]; rfl)
      (by have := Nat.mul_le_mul_right (2 ^ 32) (show ((k + 1) / 2).toNat -
            (colStart k na).toNat ≤ 2 ^ 30 by lia); rw [UInt64.toNat_zero]; lia)
      (by have := Nat.mul_le_mul_right (2 ^ 32) (show ((k + 1) / 2).toNat -
            (colStart k na).toNat ≤ 2 ^ 30 by lia); rw [UInt64.toNat_zero]; lia)
    rw [he, Nat.zero_add] at hacc
    simp only [UInt64.toNat_zero, Nat.zero_add] at hlo' hhi'
    have hcnt : ((k + 1) / 2).toNat - (colStart k na).toNat ≤ 2 ^ 30 := by lia
    have hlo2 : lo'.toNat ≤ 2 ^ 62 := by
      have := Nat.mul_le_mul_right (2 ^ 32) hcnt; lia
    have hhi2 : hi'.toNat ≤ 2 ^ 62 := by
      have := Nat.mul_le_mul_right (2 ^ 32) hcnt; lia
    -- The column total: twice the products, the diagonal and the carry.
    have hL : (lo' + lo' + ((diagWord aa sa na ha hA k hdk) &&& 0xFFFFFFFF) +
          (r.uget k (by lia)).toUInt64).toNat =
        2 * lo'.toNat + (diagWord aa sa na ha hA k hdk).toNat % 2 ^ 32 +
          (r[k.toNat]'(by lia)).toNat := by
      simp only [UInt64.toNat_add, hdlo, hc₀]
      have := Nat.mod_lt (diagWord aa sa na ha hA k hdk).toNat (show 0 < 2 ^ 32 by decide)
      lia
    have hH : (hi' + hi' + ((diagWord aa sa na ha hA k hdk) >>> 32) +
          (r.uget (k + 1) (by rw [hk1']; lia)).toUInt64).toNat =
        2 * hi'.toNat + (diagWord aa sa na ha hA k hdk).toNat / 2 ^ 32 +
          (r[k.toNat + 1]'(by lia)).toNat := by
      simp only [UInt64.toNat_add, hdhi, hc₁]
      have : (diagWord aa sa na ha hA k hdk).toNat / 2 ^ 32 < 2 ^ 32 := by
        rw [Nat.div_lt_iff_lt_mul (by decide)]; exact Nat.lt_of_lt_of_le hdβ (by decide)
      lia
    have htot : 2 * lo'.toNat + (diagWord aa sa na ha hA k hdk).toNat % 2 ^ 32 +
          (r[k.toNat]'(by lia)).toNat +
        2 ^ 32 * (2 * hi'.toNat + (diagWord aa sa na ha hA k hdk).toNat / 2 ^ 32 +
          (r[k.toNat + 1]'(by lia)).toNat) =
        ((r[k.toNat]'(by lia)).toNat + 2 ^ 32 * (r[k.toNat + 1]'(by lia)).toNat) +
          colSum la la k.toNat := by
      rw [colSum_sq, ← hacc, ← hdd]
      have := Nat.div_add_mod (diagWord aa sa na ha hA k hdk).toNat (2 ^ 32)
      lia
    have hcol : colSum la la k.toNat ≤ 2 ^ 95 := by
      rw [colSum_sq, ← hacc, ← hdd]
      have : (diagWord aa sa na ha hA k hdk).toNat < 2 ^ 64 := hdβ
      lia
    obtain ⟨hs', hz', hv'⟩ := writeCol_spec r k hrs (by lia)
      (lo' + lo' + ((diagWord aa sa na ha hA k hdk) &&& 0xFFFFFFFF) +
        (r.uget k (by lia)).toUInt64)
      (hi' + hi' + ((diagWord aa sa na ha hA k hdk) >>> 32) +
        (r.uget (k + 1) (by rw [hk1']; lia)).toUInt64)
      (by rw [hL, hH, htot]; lia) (by rw [hH]; lia)
    simp only [heq]
    have hw : weighted la la (k.toNat + 1) =
        weighted la la k.toNat + 2 ^ (32 * k.toNat) * colSum la la k.toNat := rfl
    have hw' : weighted la la (k + 1).toNat = weighted la la (k.toNat + 1) := by rw [hk1']
    apply ih
    · rw [hw', hw, ← hv]
      simp only [hr₂, UInt32.toNat_zero, Nat.mul_zero, Nat.add_zero] at hv'
      rw [hL, hH, htot] at hv'
      generalize (r[k.toNat]'(by lia)).toNat + 2 ^ 32 * (r[k.toNat + 1]'(by lia)).toNat = A
        at hv'
      rw [Nat.mul_add] at hv'
      lia
    · intro j hj hj'
      rw [hk1'] at hj
      rw [hz' j (by lia) (by rw [hs'] at hj'; exact hj')]
      exact hz j (by lia) _
    · rw [hk1']; lia

/-- The conditions under which `csqMul` runs: a nonempty operand, and sizes that fit. -/
@[expose] public def SqrOK (a : UInt32Array.Slice) : Prop :=
  0 < a.size ∧ 2 * a.size < 2147483648 ∧ a.array.size < 4294967295

public instance (a : UInt32Array.Slice) : Decidable (SqrOK a) := by
  unfold SqrOK; infer_instance

/--
All `2 * a.size` limbs of `a * a` by Comba's method: each column is twice its products below the
diagonal, plus the diagonal, which is about half the products of `combaMul a a`.
-/
public def csqMul (a : UInt32Array.Slice) (h : SqrOK a) : UInt32Array :=
  have ha := lt_usizeSize h.2.2
  have hla := slice_size_le a
  have hn : 2 * a.size + 1 < USize.size := lt_usizeSize (by have := h.2.1; lia)
  (csqOuter a.array a.start.toUSize a.size.toUSize ha (limbU_bound a ha) (2 * a.size - 1).toUSize
      (by have := mod_usize (n := 2 * a.size - 1) (by lia)
          have := mod_usize (n := a.size) (by lia); have := h.1; simp; lia)
      (.replicate (2 * a.size + 1) 0) (by rw [UInt32Array.size_replicate]; exact hn)
      (by have := mod_usize (n := 2 * a.size - 1) (by lia); have := h.1; simp; lia)
      0 (by simp)).pop

public theorem csqMul_spec (a : UInt32Array.Slice) (h : SqrOK a) :
    (csqMul a h).size = a.size + a.size ∧ toNat (csqMul a h) = toNat a * toNat a := by
  have ha := lt_usizeSize h.2.2
  have hla := slice_size_le a
  have hsa : a.size.toUSize.toNat = a.size := toNat_toUSize (by lia)
  have hn : 2 * a.size + 1 < USize.size := lt_usizeSize (by have := h.2.1; lia)
  have hkE : (2 * a.size - 1).toUSize.toNat + 1 = 2 * a.size.toUSize.toNat := by
    have := mod_usize (n := 2 * a.size - 1) (by lia)
    have := mod_usize (n := a.size) (by lia); have := h.1; simp; lia
  have hkE' : (2 * a.size - 1).toUSize.toNat = 2 * a.size - 1 := toNat_toUSize (by lia)
  have hrs : (UInt32Array.replicate (2 * a.size + 1) 0).size < USize.size := by
    rw [UInt32Array.size_replicate]; exact hn
  have hr0 : (UInt32Array.replicate (2 * a.size + 1) 0).size =
      (2 * a.size - 1).toUSize.toNat + 2 := by
    have := mod_usize (n := 2 * a.size - 1) (by lia); have := h.1; simp; lia
  have hspec := csqOuter_spec a.array a.start.toUSize a.size.toUSize ha (limbU_bound a ha)
    (2 * a.size - 1).toUSize hkE a.copy.toList (by simp [hsa]) (limbs_read a ha)
    (by rw [hsa]; have := h.2.1; lia) _ hrs hr0 0 (by simp)
    (by simp [weighted, UInt32Array.toList_replicate, ofLimbs_replicate_zero])
    (fun j _ _ => by simp)
  have hsize := size_csqOuter a.array a.start.toUSize a.size.toUSize ha (limbU_bound a ha)
    (2 * a.size - 1).toUSize hkE _ hrs hr0 0 (by simp)
  have heq : csqMul a h = (csqOuter a.array a.start.toUSize a.size.toUSize ha (limbU_bound a ha)
      (2 * a.size - 1).toUSize hkE (UInt32Array.replicate (2 * a.size + 1) 0) hrs hr0 0
      (by simp)).pop := rfl
  rw [heq]
  generalize csqOuter a.array a.start.toUSize a.size.toUSize _ _ (2 * a.size - 1).toUSize _
    (UInt32Array.replicate (2 * a.size + 1) 0) _ _ 0 _ = r at hspec hsize ⊢
  have hrsz : r.size = 2 * a.size + 1 := by
    rw [hsize]
    have := mod_usize (n := 2 * a.size - 1) (by lia); have := h.1; simp; lia
  have hv : ofLimbs r.toList = toNat a * toNat a := by
    rw [hspec, hkE', weighted_eq _ _ _ (by simp; lia)]
    rfl
  have hlt : ofLimbs r.toList < 2 ^ (32 * (2 * a.size)) := by
    rw [hv, show 32 * (2 * a.size) = 32 * a.size + 32 * a.size by lia, Nat.pow_add]
    exact Nat.mul_lt_mul'' (toNat_lt a) (toNat_lt a)
  have htop := getElem_eq_zero_of_ofLimbs_lt (l := r.toList) (k := 2 * a.size)
    (by simp; lia) hlt
  have hne : r.toList ≠ [] := by
    intro h'; have := congrArg List.length h'; simp at this; lia
  have hlast : r.toList.getLast hne = 0 := by
    rw [List.getLast_eq_getElem]; simpa [hrsz] using htop
  refine ⟨by simp [hrsz]; lia, ?_⟩
  rw [toNat_toSlice, UInt32Array.toList_pop, ← hv]
  conv => rhs; rw [← List.dropLast_concat_getLast hne, hlast]
  rw [ofLimbs_concat, UInt32.toNat_zero, Nat.mul_zero, Nat.add_zero]

end MPN
