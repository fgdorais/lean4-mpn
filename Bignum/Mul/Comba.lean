/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bignum.Basic

/-!
# Comba multiplication

The schoolbook product column by column, after Paul Comba: limb `k` of `a * b` comes from the sum
of the products `aᵢ b_{k-i}`, plus the carry from the column below. Within a column the products
are independent, so there is no carry chain from one product to the next as in the rows of
`addMul1`, and the C compiler vectorizes the loop. The low and high halves of the products go into
two `UInt64` accumulators, which cannot overflow for fewer than `2³¹` products.

The specification is `Σ_k βᵏ colSum k = a * b` (`weighted_eq`), where `colSum k` adds the products
of column `k` over all `i ≤ k`, with limbs past the end read as zero.
-/

open ScalarArray

namespace Bignum

/-! ## Column sums -/

/-- `f 0 + ⋯ + f (t - 1)`. -/
public def sumTo (f : Nat → Nat) : Nat → Nat
  | 0 => 0
  | t + 1 => sumTo f t + f t

private theorem sumTo_succ_left (f : Nat → Nat) (t : Nat) :
    sumTo f (t + 1) = f 0 + sumTo (fun i => f (i + 1)) t := by
  induction t with
  | zero => simp [sumTo]
  | succ t ih => rw [sumTo, ih, sumTo]; omega

private theorem sumTo_add (f g : Nat → Nat) (t : Nat) :
    sumTo (fun i => f i + g i) t = sumTo f t + sumTo g t := by
  induction t with
  | zero => rfl
  | succ t ih => simp only [sumTo, ih]; omega

private theorem sumTo_mul_left (c : Nat) (f : Nat → Nat) (t : Nat) :
    sumTo (fun i => c * f i) t = c * sumTo f t := by
  induction t with
  | zero => simp [sumTo]
  | succ t ih => simp only [sumTo, ih, Nat.mul_add]

private theorem sumTo_congr {f g : Nat → Nat} {t : Nat} (h : ∀ i, i < t → f i = g i) :
    sumTo f t = sumTo g t := by
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [sumTo, sumTo, ih (fun i hi => h i (by omega)), h t (by omega)]

/-- Terms that are zero from `t` to `u` don't change the sum. -/
private theorem sumTo_extend {f : Nat → Nat} {t u : Nat} (htu : t ≤ u)
    (h : ∀ i, t ≤ i → i < u → f i = 0) : sumTo f u = sumTo f t := by
  induction u with
  | zero => rw [Nat.le_zero.1 htu]
  | succ u ih =>
    rcases Nat.lt_or_ge t (u + 1) with h' | h'
    · rw [sumTo, ih (by omega) (fun i hi hi' => h i hi (by omega)), h u (by omega) (by omega),
        Nat.add_zero]
    · rw [show t = u + 1 by omega]

/-- The `i`-th limb of `l`, zero past its end, as a number. -/
public def limbD (l : List UInt32) (i : Nat) : Nat := (l.getD i 0).toNat

/-- The products of column `k`, from `i = 0` to `t - 1`. -/
public def colPart (la lb : List UInt32) (k t : Nat) : Nat :=
  sumTo (fun i => limbD la i * limbD lb (k - i)) t

/-- The sum of column `k` of the product of `la` and `lb`. -/
public def colSum (la lb : List UInt32) (k : Nat) : Nat := colPart la lb k (k + 1)

/-- `Σ_{k < N} βᵏ colSum k`. -/
public def weighted (la lb : List UInt32) (N : Nat) : Nat :=
  sumTo (fun k => 2 ^ (32 * k) * colSum la lb k) N

private theorem sumTo_limbs (l : List UInt32) (N : Nat) (h : l.length ≤ N) :
    sumTo (fun k => 2 ^ (32 * k) * limbD l k) N = ofLimbs l := by
  induction l generalizing N with
  | nil =>
    rw [sumTo_extend (Nat.zero_le N) (fun i _ _ => by simp [limbD])]
    rfl
  | cons x l ih =>
    obtain ⟨N, rfl⟩ : ∃ N', N = N' + 1 := ⟨N - 1, by simp at h; omega⟩
    have hs : sumTo (fun i => 2 ^ (32 * (i + 1)) * limbD (x :: l) (i + 1)) N =
        sumTo (fun i => 2 ^ 32 * (2 ^ (32 * i) * limbD l i)) N :=
      sumTo_congr fun i _ => by
        simp only [limbD, List.getD_cons_succ]
        rw [Nat.mul_add, Nat.pow_add, Nat.mul_one, Nat.mul_comm (2 ^ (32 * i)) (2 ^ 32),
          Nat.mul_assoc]
    rw [sumTo_succ_left, hs, sumTo_mul_left, ih N (by simp at h; omega), ofLimbs_cons]
    simp [limbD]

private theorem colSum_cons_zero (x : UInt32) (la lb : List UInt32) :
    colSum (x :: la) lb 0 = x.toNat * limbD lb 0 := by
  simp [colSum, colPart, sumTo, limbD]

private theorem colSum_cons_succ (x : UInt32) (la lb : List UInt32) (k : Nat) :
    colSum (x :: la) lb (k + 1) = x.toNat * limbD lb (k + 1) + colSum la lb k := by
  rw [colSum, colPart, sumTo_succ_left, colSum, colPart]
  have hs : sumTo (fun i => limbD (x :: la) (i + 1) * limbD lb (k + 1 - (i + 1))) (k + 1) =
      sumTo (fun i => limbD la i * limbD lb (k - i)) (k + 1) :=
    sumTo_congr fun i _ => by
      simp only [limbD, List.getD_cons_succ]
      rw [show k + 1 - (i + 1) = k - i by omega]
  rw [hs]
  simp [limbD]

private theorem colSum_nil (lb : List UInt32) (k : Nat) : colSum [] lb k = 0 := by
  rw [colSum, colPart, sumTo_extend (t := 0) (Nat.zero_le _) (fun i _ _ => by simp [limbD])]
  rfl

/-- The columns of a product, weighted by their place, add up to the product. -/
public theorem weighted_eq (la lb : List UInt32) (N : Nat) (h : la.length + lb.length ≤ N + 1) :
    weighted la lb N = ofLimbs la * ofLimbs lb := by
  induction la generalizing N with
  | nil =>
    rw [weighted, sumTo_extend (t := 0) (Nat.zero_le N) (fun k _ _ => by
      rw [colSum_nil, Nat.mul_zero])]
    simp [sumTo]
  | cons x la ih =>
    rcases N with _ | N
    · -- No column at all: `lb` is empty.
      have : lb = [] := List.eq_nil_of_length_eq_zero (by simp at h; omega)
      subst this
      simp [weighted, sumTo]
    · have hs : sumTo (fun k => 2 ^ (32 * (k + 1)) * colSum (x :: la) lb (k + 1)) N =
          x.toNat * sumTo (fun k => 2 ^ (32 * (k + 1)) * limbD lb (k + 1)) N +
            2 ^ 32 * weighted la lb N := by
        rw [weighted, ← sumTo_mul_left, ← sumTo_mul_left, ← sumTo_add]
        apply sumTo_congr
        intro i _
        rw [colSum_cons_succ]
        have e : 2 ^ (32 * (i + 1)) = 2 ^ 32 * 2 ^ (32 * i) := by
          rw [← Nat.pow_add]; congr 1; omega
        rw [e]
        generalize 2 ^ 32 = B
        generalize 2 ^ (32 * i) = P
        generalize limbD lb (i + 1) = y
        generalize colSum la lb i = c
        rw [Nat.mul_add, Nat.mul_left_comm (B * P), Nat.mul_assoc B P c]
      have hl := sumTo_limbs lb (N + 1) (by simp at h; omega)
      rw [sumTo_succ_left] at hl
      simp only [Nat.mul_zero, Nat.pow_zero, Nat.one_mul] at hl
      rw [weighted, sumTo_succ_left, colSum_cons_zero, hs, ih N (by simp at h; omega),
        ofLimbs_cons, ← hl]
      simp only [Nat.mul_zero, Nat.pow_zero, Nat.one_mul]
      generalize sumTo (fun k => 2 ^ (32 * (k + 1)) * limbD lb (k + 1)) N = S
      generalize limbD lb 0 = y
      generalize ofLimbs la = A
      generalize (2 : Nat) ^ 32 = B
      rw [Nat.add_mul, Nat.mul_add, Nat.mul_assoc, ← Nat.add_assoc]
      simp only [Nat.mul_add]

/-! ## The compiled loops -/

/--
Writes the column total `lo + β hi` into limbs `k`, `k + 1` and `k + 2` of `r`: the limb of the
column and, above it, the carry into the next column.
-/
@[inline] def writeCol (r : UInt32Array) (k : USize) (hrs : r.size < USize.size)
    (hk : k.toNat + 2 < r.size) (lo hi : UInt64) : UInt32Array :=
  let c := (lo >>> 32) + hi
  ((r.uset k lo.toUInt32 (by omega)).uset (k + 1) c.toUInt32
      (by rw [UInt32Array.size_uset, toNat_add_usize (by simp; omega)]; simp; omega)).uset (k + 2)
    (c >>> 32).toUInt32
    (by rw [UInt32Array.size_uset, UInt32Array.size_uset, toNat_add_usize (by simp; omega)]
        simp; omega)

private theorem writeCol_eq (r : UInt32Array) (k : USize) (hrs : r.size < USize.size)
    (hk : k.toNat + 2 < r.size) (lo hi : UInt64) :
    writeCol r k hrs hk lo hi =
      ((r.set k.toNat lo.toUInt32 (by omega)).set (k.toNat + 1) ((lo >>> 32) + hi).toUInt32
        (by simp; omega)).set (k.toNat + 2) (((lo >>> 32) + hi) >>> 32).toUInt32
        (by simp; omega) := by
  have hk1 : (k + 1).toNat = k.toNat + 1 := by rw [toNat_add_usize (by simp; omega)]; simp
  have hk2 : (k + 2).toNat = k.toNat + 2 := by rw [toNat_add_usize (by simp; omega)]; simp
  have h₀ : ∀ (a : UInt32Array) v h, a.uset k v h = a.set k.toNat v h :=
    fun a v h => uset_eq_set a k _ rfl v h
  have h₁ : ∀ (a : UInt32Array) v h, a.uset (k + 1) v h = a.set (k.toNat + 1) v (hk1 ▸ h) :=
    fun a v h => uset_eq_set a _ _ hk1 v h
  have h₂ : ∀ (a : UInt32Array) v h, a.uset (k + 2) v h = a.set (k.toNat + 2) v (hk2 ▸ h) :=
    fun a v h => uset_eq_set a _ _ hk2 v h
  simp only [writeCol, h₀, h₁, h₂]

private theorem writeCol_spec (r : UInt32Array) (k : USize) (hrs : r.size < USize.size)
    (hk : k.toNat + 2 < r.size) (lo hi : UInt64)
    (hfit : lo.toNat + 2 ^ 32 * hi.toNat < 2 ^ 96) (_hhi : hi.toNat + 2 ^ 32 ≤ 2 ^ 64) :
    (writeCol r k hrs hk lo hi).size = r.size ∧
      (∀ j, k.toNat + 3 ≤ j → ∀ (hj' : j < r.size),
        (writeCol r k hrs hk lo hi)[j]'(by simp only [writeCol_eq]; simpa using hj') = r[j]) ∧
      ofLimbs (writeCol r k hrs hk lo hi).toList +
          2 ^ (32 * k.toNat) * (r[k.toNat].toNat + 2 ^ 32 * (r[k.toNat + 1]'(by omega)).toNat +
            2 ^ 64 * (r[k.toNat + 2]'(by omega)).toNat) =
        ofLimbs r.toList + 2 ^ (32 * k.toNat) * (lo.toNat + 2 ^ 32 * hi.toNat) := by
  simp only [writeCol_eq]
  refine ⟨by simp, fun j hj hj' => ?_, ?_⟩
  · simp only [UInt32Array.getElem_set]
    rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega)]
  · -- The three limbs written are the digits of `lo + β hi`.
    have hlo := lo.toNat_lt
    have hc : ((lo >>> 32) + hi).toNat = lo.toNat / 2 ^ 32 + hi.toNat := by
      rw [UInt64.toNat_add, UInt64.toNat_shiftRight]
      simp only [UInt64.reduceToNat, Nat.reduceMod, Nat.shiftRight_eq_div_pow]
      exact Nat.mod_eq_of_lt (by omega)
    have hcβ : lo.toNat / 2 ^ 32 + hi.toNat < 2 ^ 64 := by omega
    have hd0 : lo.toUInt32.toNat = lo.toNat % 2 ^ 32 := UInt64.toNat_toUInt32 _
    have hd1 : ((lo >>> 32) + hi).toUInt32.toNat = (lo.toNat / 2 ^ 32 + hi.toNat) % 2 ^ 32 := by
      rw [UInt64.toNat_toUInt32, hc]
    have hd2 : (((lo >>> 32) + hi) >>> 32).toUInt32.toNat =
        (lo.toNat / 2 ^ 32 + hi.toNat) / 2 ^ 32 := by
      rw [UInt64.toNat_toUInt32, UInt64.toNat_shiftRight, hc]
      simp only [UInt64.reduceToNat, Nat.reduceMod, Nat.shiftRight_eq_div_pow]
      exact Nat.mod_eq_of_lt (by omega)
    have hsum : lo.toNat % 2 ^ 32 + 2 ^ 32 * ((lo.toNat / 2 ^ 32 + hi.toNat) % 2 ^ 32) +
        2 ^ 64 * ((lo.toNat / 2 ^ 32 + hi.toNat) / 2 ^ 32) = lo.toNat + 2 ^ 32 * hi.toNat := by
      have h₁ := Nat.div_add_mod lo.toNat (2 ^ 32)
      have h₂ := Nat.div_add_mod (lo.toNat / 2 ^ 32 + hi.toNat) (2 ^ 32)
      generalize hq : lo.toNat / 2 ^ 32 = q at h₁ h₂ ⊢
      generalize hcd : q + hi.toNat = c at h₂ ⊢
      omega
    simp only [UInt32Array.toList_set]
    have e₁ := ofLimbs_set r.toList k.toNat lo.toUInt32 (by simp; omega)
    have e₂ := ofLimbs_set (r.toList.set k.toNat lo.toUInt32) (k.toNat + 1)
      ((lo >>> 32) + hi).toUInt32 (by simp; omega)
    have e₃ := ofLimbs_set ((r.toList.set k.toNat lo.toUInt32).set (k.toNat + 1)
      ((lo >>> 32) + hi).toUInt32) (k.toNat + 2) (((lo >>> 32) + hi) >>> 32).toUInt32
      (by simp; omega)
    simp only [List.getElem_set_ne (show k.toNat ≠ k.toNat + 1 by omega),
      List.getElem_set_ne (show k.toNat ≠ k.toNat + 2 by omega),
      List.getElem_set_ne (show k.toNat + 1 ≠ k.toNat + 2 by omega),
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
halves in `hi`, then written into `r` by `writeCol`. The limbs of `a` are `aa[sa ...]` and those
of `b` are `bb[sb ...]`, read with `limbU`.
-/
def combaCol (aa : UInt32Array) (sa na : USize) (ha : aa.size < USize.size)
    (hA : sa.toNat + na.toNat ≤ aa.size) (bb : UInt32Array) (sb nb : USize)
    (hb : bb.size < USize.size) (hB : sb.toNat + nb.toNat ≤ bb.size)
    (k iEnd : USize) (hiE : iEnd.toNat ≤ na.toNat) (hiEk : iEnd.toNat ≤ k.toNat + 1)
    (r : UInt32Array) (hrs : r.size < USize.size) (hr : k.toNat + 2 < r.size)
    (i : USize) (_hii : i.toNat ≤ iEnd.toNat) (hst : k.toNat + 1 ≤ nb.toNat + i.toNat)
    (lo hi : UInt64) : UInt32Array :=
  if h : i < iEnd then
    have h' : i.toNat < iEnd.toNat := h
    let x := limbU aa sa na ha hA i (by omega)
    let y := limbU bb sb nb hb hB (k - i)
      (by rw [USize.toNat_sub_of_le _ _ (USize.le_iff_toNat_le.2 (by omega))]; omega)
    let p := x.toUInt64 * y.toUInt64
    combaCol aa sa na ha hA bb sb nb hb hB k iEnd hiE hiEk r hrs hr (i + 1)
      (by rw [toNat_add_usize (by simp; omega)]; simp; omega)
      (by rw [toNat_add_usize (by simp; omega)]; simp; omega)
      (lo + (p &&& 0xFFFFFFFF)) (hi + (p >>> 32))
  else
    writeCol r k hrs hr lo hi
termination_by iEnd.toNat - i.toNat
decreasing_by
  rw [toNat_add_usize (by simp; omega)]; simp; omega

private theorem combaCol_spec (aa : UInt32Array) (sa na : USize) (ha : aa.size < USize.size)
    (hA : sa.toNat + na.toNat ≤ aa.size) (bb : UInt32Array) (sb nb : USize)
    (hb : bb.size < USize.size) (hB : sb.toNat + nb.toNat ≤ bb.size)
    (k iEnd : USize) (hiE : iEnd.toNat ≤ na.toNat) (hiEk : iEnd.toNat ≤ k.toNat + 1)
    (r : UInt32Array) (hrs : r.size < USize.size) (hr : k.toNat + 2 < r.size)
    (la lb : List UInt32)
    (hxa : ∀ j (hj : j < na.toNat), (aa[sa.toNat + j]'(by omega)).toNat = limbD la j)
    (hxb : ∀ j (hj : j < nb.toNat), (bb[sb.toNat + j]'(by omega)).toNat = limbD lb j)
    (c₀ : Nat) (i : USize) (hii : i.toNat ≤ iEnd.toNat) (hst : k.toNat + 1 ≤ nb.toNat + i.toNat)
    (lo hi : UInt64)
    (hacc : lo.toNat + 2 ^ 32 * hi.toNat = c₀ + colPart la lb k.toNat i.toNat)
    (hlo : lo.toNat + (iEnd.toNat - i.toNat) * 2 ^ 32 < 2 ^ 64)
    (hhi : hi.toNat + (iEnd.toNat - i.toNat + 1) * 2 ^ 32 ≤ 2 ^ 64) :
    ∃ lo' hi' : UInt64, combaCol aa sa na ha hA bb sb nb hb hB k iEnd hiE hiEk r hrs hr i hii hst
        lo hi = writeCol r k hrs hr lo' hi' ∧
      lo'.toNat + 2 ^ 32 * hi'.toNat = c₀ + colPart la lb k.toNat iEnd.toNat ∧
      hi'.toNat + 2 ^ 32 ≤ 2 ^ 64 := by
  induction hd : iEnd.toNat - i.toNat generalizing i lo hi with
  | zero =>
    have hie : i.toNat = iEnd.toNat := by omega
    rw [combaCol, dite_eq_right (by rw [USize.lt_iff_toNat_lt]; omega)]
    exact ⟨lo, hi, rfl, by rw [hacc, hie], by omega⟩
  | succ d ih =>
    have h' : i.toNat < iEnd.toNat := by omega
    rw [combaCol, dite_eq_left (show i < iEnd from h')]
    dsimp only
    have hi1 : (i + 1).toNat = i.toNat + 1 := by rw [toNat_add_usize (by simp; omega)]; simp
    have hki : (k - i).toNat = k.toNat - i.toNat :=
      USize.toNat_sub_of_le _ _ (USize.le_iff_toNat_le.2 (by omega))
    -- The two limbs and their product.
    have hx : (limbU aa sa na ha hA i (by omega)).toNat = limbD la i.toNat := by
      rw [limbU_eq_getElem _ _ _ _ _ _ _ _ rfl, hxa _ (by omega)]
    have hy : (limbU bb sb nb hb hB (k - i) (by rw [hki]; omega)).toNat =
        limbD lb (k.toNat - i.toNat) := by
      rw [limbU_eq_getElem _ _ _ _ _ _ _ _ rfl]
      simp only [hki]
      rw [hxb _ (by omega)]
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
      rw [UInt64.toNat_add, hpl]; exact Nat.mod_eq_of_lt (by omega)
    have hhi' : (hi + ((x.toUInt64 * y.toUInt64) >>> 32)).toNat =
        hi.toNat + x.toNat * y.toNat / 2 ^ 32 := by
      rw [UInt64.toNat_add, hph]; exact Nat.mod_eq_of_lt (by omega)
    apply ih
    · -- One more product in the column.
      rw [hlo', hhi', hi1, colPart, sumTo, ← colPart, ← hx, ← hy, Nat.mul_add]
      have := Nat.div_add_mod (x.toNat * y.toNat) (2 ^ 32)
      omega
    · rw [hlo', hi1]; omega
    · rw [hhi', hi1]; omega
    · rw [hi1]; omega

private theorem size_combaCol (aa : UInt32Array) (sa na : USize) (ha : aa.size < USize.size)
    (hA : sa.toNat + na.toNat ≤ aa.size) (bb : UInt32Array) (sb nb : USize)
    (hb : bb.size < USize.size) (hB : sb.toNat + nb.toNat ≤ bb.size)
    (k iEnd : USize) (hiE : iEnd.toNat ≤ na.toNat) (hiEk : iEnd.toNat ≤ k.toNat + 1)
    (r : UInt32Array) (hrs : r.size < USize.size) (hr : k.toNat + 2 < r.size)
    (i : USize) (hii : i.toNat ≤ iEnd.toNat) (hst : k.toNat + 1 ≤ nb.toNat + i.toNat)
    (lo hi : UInt64) :
    (combaCol aa sa na ha hA bb sb nb hb hB k iEnd hiE hiEk r hrs hr i hii hst lo hi).size =
      r.size := by
  induction hd : iEnd.toNat - i.toNat generalizing i lo hi with
  | zero =>
    rw [combaCol, dite_eq_right (by rw [USize.lt_iff_toNat_lt]; omega)]
    simp only [writeCol_eq, UInt32Array.size_set]
  | succ d ih =>
    have h' : i.toNat < iEnd.toNat := by omega
    rw [combaCol, dite_eq_left (show i < iEnd from h')]
    dsimp only
    apply ih
    rw [toNat_add_usize (by simp; omega)]; simp; omega

/-- The end of the products of column `k`: `min (k + 1) na`. -/
@[inline] def colEnd (k na : USize) : USize := if k + 1 < na then k + 1 else na

/-- The start of the products of column `k`: `k + 1 - nb`, or `0`. -/
@[inline] def colStart (k nb : USize) : USize := if nb ≤ k then k + 1 - nb else 0

private theorem toNat_colEnd (k na : USize) (hk : k.toNat + 1 < USize.size) :
    (colEnd k na).toNat = min (k.toNat + 1) na.toNat := by
  have h1 : (k + 1).toNat = k.toNat + 1 := by rw [toNat_add_usize (by simp; omega)]; simp
  unfold colEnd
  split
  · rename_i h; rw [USize.lt_iff_toNat_lt, h1] at h; rw [h1]; omega
  · rename_i h; rw [USize.lt_iff_toNat_lt, h1] at h; omega

private theorem toNat_colStart (k nb : USize) (hk : k.toNat + 1 < USize.size) :
    (colStart k nb).toNat = k.toNat + 1 - nb.toNat := by
  have h1 : (k + 1).toNat = k.toNat + 1 := by rw [toNat_add_usize (by simp; omega)]; simp
  unfold colStart
  split
  · rename_i h
    rw [USize.le_iff_toNat_le] at h
    rw [USize.toNat_sub_of_le _ _ (by rw [USize.le_iff_toNat_le, h1]; omega), h1]
  · rename_i h
    rw [USize.le_iff_toNat_le] at h
    simp; omega

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
    have hk1 : k.toNat + 1 < USize.size := by omega
    let lo := (r.uget k (by omega)).toUInt64
    let hi := (r.uget (k + 1) (by rw [toNat_add_usize (by simp; omega)]; simp; omega)).toUInt64
    let r' := combaCol aa sa na ha hA bb sb nb hb hB k (colEnd k na)
      (by rw [toNat_colEnd _ _ hk1]; omega) (by rw [toNat_colEnd _ _ hk1]; omega) r hrs
      (by omega) (colStart k nb)
      (by rw [toNat_colEnd _ _ hk1, toNat_colStart _ _ hk1]; omega)
      (by rw [toNat_colStart _ _ hk1]; omega) lo hi
    combaOuter aa sa na ha hA bb sb nb hb hB kEnd hkE r'
      (by rw [size_combaCol]; exact hrs) (by rw [size_combaCol]; exact hr) (k + 1)
      (by rw [toNat_add_usize (by simp; omega)]; simp; omega)
  else
    r
termination_by kEnd.toNat - k.toNat
decreasing_by
  rw [toNat_add_usize (by simp; omega)]; simp; omega

private theorem limbD_of_length_le {l : List UInt32} {j : Nat} (h : l.length ≤ j) :
    limbD l j = 0 := by
  simp [limbD, List.getD_eq_getElem?_getD, List.getElem?_eq_none h]

private theorem limbD_lt (l : List UInt32) (j : Nat) : limbD l j < 2 ^ 32 :=
  UInt32.toNat_lt _

private theorem colPart_le (la lb : List UInt32) (k t : Nat) :
    colPart la lb k t ≤ t * 2 ^ 64 := by
  induction t with
  | zero => simp [colPart, sumTo]
  | succ t ih =>
    rw [colPart, sumTo, ← colPart, Nat.succ_mul]
    have := Nat.mul_le_mul (Nat.le_of_lt (limbD_lt la t)) (Nat.le_of_lt (limbD_lt lb (k - t)))
    have : (2 : Nat) ^ 32 * 2 ^ 32 = 2 ^ 64 := by decide
    omega

/-- The products of column `k` below `k + 1 - nb` read limbs of `lb` past its end. -/
private theorem colPart_start (la lb : List UInt32) (k : Nat) :
    colPart la lb k (k + 1 - lb.length) = 0 := by
  rw [colPart, sumTo_extend (t := 0) (Nat.zero_le _) (fun i _ hi => by
    rw [limbD_of_length_le (l := lb) (by omega), Nat.mul_zero])]
  rfl

/-- The products of column `k` from `la.length` on read limbs of `la` past its end. -/
private theorem colPart_end (la lb : List UInt32) (k : Nat) :
    colPart la lb k (min (k + 1) la.length) = colSum la lb k := by
  unfold colSum colPart
  exact (sumTo_extend (Nat.min_le_left _ _) (fun i hi _ => by
    rw [limbD_of_length_le (l := la) (by omega), Nat.zero_mul])).symm

private theorem combaOuter_spec (aa : UInt32Array) (sa na : USize) (ha : aa.size < USize.size)
    (hA : sa.toNat + na.toNat ≤ aa.size) (bb : UInt32Array) (sb nb : USize)
    (hb : bb.size < USize.size) (hB : sb.toNat + nb.toNat ≤ bb.size)
    (kEnd : USize) (hkE : kEnd.toNat + 1 = na.toNat + nb.toNat)
    (la lb : List UInt32) (hla : la.length = na.toNat) (hlb : lb.length = nb.toNat)
    (hxa : ∀ j (hj : j < na.toNat), (aa[sa.toNat + j]'(by omega)).toNat = limbD la j)
    (hxb : ∀ j (hj : j < nb.toNat), (bb[sb.toNat + j]'(by omega)).toNat = limbD lb j)
    (hna : na.toNat < 2 ^ 31)
    (r : UInt32Array) (hrs : r.size < USize.size) (hr : r.size = kEnd.toNat + 2)
    (k : USize) (hk : k.toNat ≤ kEnd.toNat)
    (hv : ofLimbs r.toList = weighted la lb k.toNat)
    (hz : ∀ j, k.toNat + 2 ≤ j → ∀ (hj' : j < r.size), r[j] = 0) :
    ofLimbs (combaOuter aa sa na ha hA bb sb nb hb hB kEnd hkE r hrs hr k hk).toList =
      weighted la lb kEnd.toNat := by
  induction hd : kEnd.toNat - k.toNat generalizing k r with
  | zero =>
    rw [combaOuter, dite_eq_right (by rw [USize.lt_iff_toNat_lt]; omega)]
    rw [hv, show k.toNat = kEnd.toNat by omega]
  | succ d ih =>
    have h' : k.toNat < kEnd.toNat := by omega
    have hk1 : k.toNat + 1 < USize.size := by omega
    have hk1' : (k + 1).toNat = k.toNat + 1 := by rw [toNat_add_usize (by simp; omega)]; simp
    rw [combaOuter, dite_eq_left (show k < kEnd from h')]
    dsimp only
    -- The carry in `r[k]`, `r[k + 1]`, and the column with `combaCol`.
    have hlo : ((r.uget k (by omega)).toUInt64).toNat = (r[k.toNat]'(by omega)).toNat := by
      rw [UInt32.toNat_toUInt64, uget_eq_getElem _ _ _ rfl]
    have hhi : ((r.uget (k + 1) (by rw [hk1']; omega)).toUInt64).toNat =
        (r[k.toNat + 1]'(by omega)).toNat := by
      rw [UInt32.toNat_toUInt64, uget_eq_getElem _ _ _ hk1']
    have hr₀ := (r[k.toNat]'(by omega)).toNat_lt
    have hr₁ := (r[k.toNat + 1]'(by omega)).toNat_lt
    have hr₂ : r[k.toNat + 2]'(by omega) = 0 := hz _ (Nat.le_refl _) (by omega)
    have hE := toNat_colEnd k na hk1
    have hS := toNat_colStart k nb hk1
    obtain ⟨lo', hi', heq, hacc, hhi'⟩ := combaCol_spec aa sa na ha hA bb sb nb hb hB k
      (colEnd k na) (by omega) (by omega) r hrs (by omega) la lb hxa hxb
      ((r[k.toNat]'(by omega)).toNat + 2 ^ 32 * (r[k.toNat + 1]'(by omega)).toNat)
      (colStart k nb) (by omega) (by omega) (r.uget k (by omega)).toUInt64
      (r.uget (k + 1) (by rw [hk1']; omega)).toUInt64
      (by rw [hlo, hhi, hS, ← hlb, colPart_start]; rfl)
      (by rw [hlo]; have := Nat.mul_le_mul_right (2 ^ 32) (show (colEnd k na).toNat -
            (colStart k nb).toNat ≤ 2 ^ 31 by omega); omega)
      (by rw [hhi]; have := Nat.mul_le_mul_right (2 ^ 32) (show (colEnd k na).toNat -
            (colStart k nb).toNat + 1 ≤ 2 ^ 31 by omega); omega)
    rw [hE, ← hla, colPart_end] at hacc
    have hcol : colSum la lb k.toNat ≤ na.toNat * 2 ^ 64 := by
      rw [← colPart_end, hla]
      exact Nat.le_trans (colPart_le _ _ _ _) (Nat.mul_le_mul_right _ (Nat.min_le_right _ _))
    obtain ⟨hs', hz', hv'⟩ := writeCol_spec r k hrs (by omega) lo' hi'
      (by rw [hacc]; have := Nat.mul_le_mul_right (2 ^ 64) (Nat.le_of_lt hna); omega) hhi'
    -- `weighted (k + 1) = weighted k + βᵏ colSum k`.
    simp only [heq]
    have hw : weighted la lb (k.toNat + 1) =
        weighted la lb k.toNat + 2 ^ (32 * k.toNat) * colSum la lb k.toNat := rfl
    apply ih
    · rw [hk1', hw, ← hv]
      simp only [hr₂, UInt32.toNat_zero, Nat.mul_zero, Nat.add_zero] at hv'
      rw [hacc] at hv'
      generalize (r[k.toNat]'(by omega)).toNat + 2 ^ 32 * (r[k.toNat + 1]'(by omega)).toNat = A
        at hv'
      rw [Nat.mul_add] at hv'
      omega
    · intro j hj hj'
      rw [hk1'] at hj
      rw [hz' j (by omega) (by rw [hs'] at hj'; exact hj')]
      exact hz j (by omega) _
    · rw [hk1']; omega

private theorem size_combaOuter (aa : UInt32Array) (sa na : USize) (ha : aa.size < USize.size)
    (hA : sa.toNat + na.toNat ≤ aa.size) (bb : UInt32Array) (sb nb : USize)
    (hb : bb.size < USize.size) (hB : sb.toNat + nb.toNat ≤ bb.size)
    (kEnd : USize) (hkE : kEnd.toNat + 1 = na.toNat + nb.toNat)
    (r : UInt32Array) (hrs : r.size < USize.size) (hr : r.size = kEnd.toNat + 2)
    (k : USize) (hk : k.toNat ≤ kEnd.toNat) :
    (combaOuter aa sa na ha hA bb sb nb hb hB kEnd hkE r hrs hr k hk).size = kEnd.toNat + 2 := by
  induction hd : kEnd.toNat - k.toNat generalizing k r with
  | zero =>
    rw [combaOuter, dite_eq_right (by rw [USize.lt_iff_toNat_lt]; omega)]
    exact hr
  | succ d ih =>
    have h' : k.toNat < kEnd.toNat := by omega
    rw [combaOuter, dite_eq_left (show k < kEnd from h')]
    dsimp only
    apply ih
    rw [toNat_add_usize (by simp; omega)]; simp; omega

private theorem mod_usize {n : Nat} (h : n < USize.size) : n % 2 ^ System.Platform.numBits = n :=
  Nat.mod_eq_of_lt (by rwa [← USize.size_eq_two_pow])

/-- The conditions under which `combaMul` runs: nonempty operands, and sizes that fit. -/
@[expose] public def CombaOK (a b : UInt32Array.Slice) : Prop :=
  0 < a.size ∧ 0 < b.size ∧ a.size + b.size < 2147483648 ∧ a.array.size < 4294967295 ∧
    b.array.size < 4294967295

public instance (a b : UInt32Array.Slice) : Decidable (CombaOK a b) := by
  unfold CombaOK; infer_instance

private theorem slice_size_le (a : UInt32Array.Slice) : a.size ≤ a.array.size := by
  have := a.stop_le_array_size; have := a.size_eq; omega

/--
All `a.size + b.size` limbs of `a * b` by Comba's method, one column at a time, into
`a.size + b.size + 1` limbs whose top limb, which only held a carry, is dropped.
-/
public def combaMul (a b : UInt32Array.Slice) (h : CombaOK a b) : UInt32Array :=
  have ha := lt_usizeSize h.2.2.2.1
  have hb := lt_usizeSize h.2.2.2.2
  have hla := slice_size_le a
  have hlb := slice_size_le b
  have hn : a.size + b.size + 1 < USize.size := lt_usizeSize (by have := h.2.2.1; omega)
  (combaOuter a.array a.start.toUSize a.size.toUSize ha (limbU_bound a ha)
      b.array b.start.toUSize b.size.toUSize hb (limbU_bound b hb)
      (a.size + b.size - 1).toUSize
      (by have := mod_usize (n := a.size + b.size - 1) (by omega)
          have := mod_usize (n := a.size) (by omega); have := mod_usize (n := b.size) (by omega)
          have := h.1; simp; omega)
      (.replicate (a.size + b.size + 1) 0) (by rw [UInt32Array.size_replicate]; exact hn)
      (by have := mod_usize (n := a.size + b.size - 1) (by omega); have := h.1; simp; omega)
      0 (by simp)).pop

/-- The limbs of a slice as `combaOuter` reads them. -/
private theorem limbs_read (a : UInt32Array.Slice) (has : a.array.size < USize.size) (j : Nat)
    (hj : j < a.size.toUSize.toNat) :
    (a.array[a.start.toUSize.toNat + j]'(by have := limbU_bound a has; omega)).toNat =
      limbD a.copy.toList j := by
  have hla := slice_size_le a
  have hst : a.start.toUSize.toNat = a.start := toNat_toUSize (by
    have := a.start_le_stop; have := a.stop_le_array_size; omega)
  have hsz : a.size.toUSize.toNat = a.size := toNat_toUSize (by omega)
  rw [hsz] at hj
  have := a.stop_le_array_size; have := a.size_eq; have := a.start_le_stop
  have e : ∀ i (hi : i < a.array.size), i = a.start + j →
      a.array[i] = a.array[a.start + j]'(by omega) := by
    intro i hi he; subst he; rfl
  rw [e _ _ (by rw [hst]), limbD, ← getD_eq_getD_toList_copy, UInt32Array.Slice.getD_eq,
    dite_eq_left hj, UInt32Array.Slice.getElem_eq]

public theorem combaMul_spec (a b : UInt32Array.Slice) (h : CombaOK a b) :
    (combaMul a b h).size = a.size + b.size ∧ toNat (combaMul a b h) = toNat a * toNat b := by
  have ha := lt_usizeSize h.2.2.2.1
  have hb := lt_usizeSize h.2.2.2.2
  have hla := slice_size_le a
  have hlb := slice_size_le b
  have hsa : a.size.toUSize.toNat = a.size := toNat_toUSize (by omega)
  have hsb : b.size.toUSize.toNat = b.size := toNat_toUSize (by omega)
  have hn : a.size + b.size + 1 < USize.size := lt_usizeSize (by have := h.2.2.1; omega)
  have hkE' : (a.size + b.size - 1).toUSize.toNat = a.size + b.size - 1 := toNat_toUSize (by omega)
  have hkE : (a.size + b.size - 1).toUSize.toNat + 1 = a.size.toUSize.toNat + b.size.toUSize.toNat :=
    by have := mod_usize (n := a.size + b.size - 1) (by omega)
       have := mod_usize (n := a.size) (by omega); have := mod_usize (n := b.size) (by omega)
       have := h.1; simp; omega
  have hrs : (UInt32Array.replicate (a.size + b.size + 1) 0).size < USize.size := by
    rw [UInt32Array.size_replicate]; exact hn
  have hr0 : (UInt32Array.replicate (a.size + b.size + 1) 0).size =
      (a.size + b.size - 1).toUSize.toNat + 2 := by
    have := mod_usize (n := a.size + b.size - 1) (by omega); have := h.1; simp; omega
  have hspec := combaOuter_spec a.array a.start.toUSize a.size.toUSize ha (limbU_bound a ha)
    b.array b.start.toUSize b.size.toUSize hb (limbU_bound b hb) (a.size + b.size - 1).toUSize hkE
    a.copy.toList b.copy.toList (by simp [hsa]) (by simp [hsb]) (limbs_read a ha)
    (limbs_read b hb) (by rw [hsa]; have := h.2.2.1; omega) _ hrs hr0 0 (by simp)
    (by simp [weighted, sumTo, UInt32Array.toList_replicate, ofLimbs_replicate_zero])
    (fun j _ _ => by simp)
  have hsize := size_combaOuter a.array a.start.toUSize a.size.toUSize ha (limbU_bound a ha)
    b.array b.start.toUSize b.size.toUSize hb (limbU_bound b hb) (a.size + b.size - 1).toUSize hkE
    _ hrs hr0 0 (by simp)
  have heq : combaMul a b h = (combaOuter a.array a.start.toUSize a.size.toUSize ha
      (limbU_bound a ha) b.array b.start.toUSize b.size.toUSize hb (limbU_bound b hb)
      (a.size + b.size - 1).toUSize hkE (UInt32Array.replicate (a.size + b.size + 1) 0) hrs hr0 0
      (by simp)).pop := rfl
  rw [heq]
  generalize combaOuter a.array a.start.toUSize a.size.toUSize _ _ b.array b.start.toUSize
    b.size.toUSize _ _ (a.size + b.size - 1).toUSize _ (UInt32Array.replicate (a.size + b.size + 1) 0)
    _ _ 0 _ = r at hspec hsize ⊢
  have hrsz : r.size = a.size + b.size + 1 := by
    rw [hsize]
    have := mod_usize (n := a.size + b.size - 1) (by omega); have := h.1; simp; omega
  have hv : ofLimbs r.toList = toNat a * toNat b := by
    rw [hspec, hkE', weighted_eq _ _ _ (by simp; omega)]
    rfl
  -- The top limb is zero: `a b < β^(a.size + b.size)`.
  have hlt : ofLimbs r.toList < 2 ^ (32 * (a.size + b.size)) := by
    rw [hv, Nat.mul_add, Nat.pow_add]
    have hA := toNat_lt a; have hB := toNat_lt b
    exact Nat.mul_lt_mul'' hA hB
  have htop := getElem_eq_zero_of_ofLimbs_lt (l := r.toList) (k := a.size + b.size)
    (by simp; omega) hlt
  have hne : r.toList ≠ [] := by
    intro h'; have := congrArg List.length h'; simp at this; omega
  have hlast : r.toList.getLast hne = 0 := by
    rw [List.getLast_eq_getElem]; simpa [hrsz] using htop
  refine ⟨by simp [hrsz], ?_⟩
  rw [toNat_toSlice, UInt32Array.toList_pop, ← hv]
  conv => rhs; rw [← List.dropLast_concat_getLast hne, hlast]
  rw [ofLimbs_concat, UInt32.toNat_zero, Nat.mul_zero, Nat.add_zero]

end Bignum
