/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import MPN.FFT.Transform
public import MPN.FFT.Roots
public import MPN.Poly
public import MPN.Mul.Toom

/-!
# FFT multiplication

Schönhage–Strassen multiplication of `a` by `b` on one flat array: their pieces of `m` limbs are
loaded into two blocks of `K = 2ᵏ` windows of `n + 1` limbs, transformed modulo `F = 2^(64 n) + 1`
with the root `2^σ`, `σ = 128 n / K`, multiplied pointwise, by `mulToom` and a reduction
modulo `F`, and transformed back. Divided by `K`, the windows are the coefficients of the product
of the polynomials of the pieces, which are less than `F` when `K 2^(128 m) ≤ 2^(64 n)`, so they
are exact; their sum at `2^(64 m)` is `a b`.
-/

open ScalarArray UInt64Array

namespace MPN.FFT

/-! ## Slices at `Nat` offsets -/

/-- The limbs `o` to `o + len - 1` of `arr`. -/
public def sl (arr : UInt64Array) (o len : Nat) : USlice := arr.uslice o.toUSize (o + len).toUSize

public theorem sl_spec (arr : UInt64Array) (o len : Nat) (h : o + len ≤ arr.size)
    (hS : arr.size < USize.size) :
    (sl arr o len).array = arr ∧ (sl arr o len).start.toNat = o ∧
      (sl arr o len).size.toNat = len ∧ (sl arr o len).toNat = arr.valAt o len := by
  have ho : o.toUSize.toNat = o := by rw [USize.toNat_ofNat', Nat.mod_eq_of_lt (by lia)]
  have hol : (o + len).toUSize.toNat = o + len := by
    rw [USize.toNat_ofNat', Nat.mod_eq_of_lt (by lia)]
  have hst := uslice_start arr o.toUSize (o + len).toUSize (USize.le_iff_toNat_le.2 (by lia))
    (by rw [hol]; exact h)
  have hsp := uslice_stop arr o.toUSize (o + len).toUSize (by rw [hol]; exact h)
  have hsz : (sl arr o len).size.toNat = len := by
    rw [USlice.toNat_size, sl, hst, hsp, ho, hol]; lia
  refine ⟨rfl, by rw [sl, hst, ho], hsz, ?_⟩
  rw [USlice.toNat_eq_valAt, hsz, sl, hst, ho]
  rfl

/-! ## Pieces -/

/-- Piece `i` of `a`: its limbs `i m` to `i m + m - 1`, or fewer at the end. -/
@[expose] public def piece (a : USlice) (m i : Nat) : Nat :=
  a.array.valAt (a.start.toNat + i * m) (min m (a.size.toNat - i * m))

/-- The first `L` pieces of `a`. -/
@[expose] public def pieces (a : USlice) (m L : Nat) : List Nat := (List.range L).map (piece a m)

public theorem piece_lt (a : USlice) (m i : Nat) : piece a m i < 2 ^ (64 * m) :=
  Nat.lt_of_lt_of_le (valAt_lt ..) (Nat.pow_le_pow_right (by decide) (by lia))

private theorem polyVal_pieces_from (a : USlice) (m : Nat) (L : Nat) :
    ∀ i, polyVal (2 ^ (64 * m)) ((List.range L).map fun j => piece a m (i + j)) =
      a.array.valAt (a.start.toNat + i * m) (min (L * m) (a.size.toNat - i * m)) := by
  induction L with
  | zero => intro i; simp [polyVal]
  | succ L ih =>
    intro i
    rw [List.range_succ_eq_map, List.map_cons, List.map_map, polyVal]
    have e : ((fun j => piece a m (i + j)) ∘ Nat.succ) = fun j => piece a m ((i + 1) + j) := by
      funext j; simp only [Function.comp, Nat.succ_eq_add_one]; congr 1; lia
    rw [e, ih (i + 1), Nat.add_zero, piece]
    -- Split the limbs of the pieces `i` to `i + L` after the first.
    rcases Nat.le_total (a.size.toNat - i * m) m with h | h
    · rw [Nat.min_eq_right h, show a.size.toNat - (i + 1) * m = 0 by rw [Nat.add_mul]; lia,
        Nat.min_zero, valAt_zero, Nat.mul_zero, Nat.add_zero,
        Nat.min_eq_right (show a.size.toNat - i * m ≤ (L + 1) * m by rw [Nat.add_mul]; lia)]
    · rw [Nat.min_eq_left h, show (L + 1) * m = m + L * m by rw [Nat.add_mul]; lia,
        show min (m + L * m) (a.size.toNat - i * m) = m + min (L * m) (a.size.toNat - (i + 1) * m)
          by rw [Nat.add_mul]; lia, UInt64Array.valAt_add,
        show a.start.toNat + i * m + m = a.start.toNat + (i + 1) * m by rw [Nat.add_mul]; lia]

/-- The pieces of `a` are its digits in base `2^(64 m)`. -/
public theorem polyVal_pieces (a : USlice) (m L : Nat) (hL : a.size.toNat ≤ L * m) :
    polyVal (2 ^ (64 * m)) (pieces a m L) = a.toNat := by
  have := polyVal_pieces_from a m L 0
  simp only [Nat.zero_add, Nat.zero_mul, Nat.add_zero, Nat.sub_zero,
    Nat.min_eq_right hL] at this
  rw [pieces, this, USlice.toNat_eq_valAt]

public theorem length_pieces (a : USlice) (m L : Nat) : (pieces a m L).length = L := by
  simp [pieces]

public theorem getD_pieces (a : USlice) (m L i : Nat) :
    (pieces a m L).getD i 0 = if i < L then piece a m i else 0 := by
  rw [pieces, List.getD_eq_getElem?_getD, List.getElem?_map]
  split
  · rename_i h; simp [h]
  · rename_i h; simp [h]

/-! ## Loading the pieces -/

/-- Adds `b` to the limbs `o` to `o + len - 1` of `arr`, with the carry out. -/
public def addAt (arr : UInt64Array) (o len : Nat) (b : USlice) : UInt64Array × UInt64 :=
  addInto (sl arr o len) b 0

public theorem addAt_spec (arr : UInt64Array) (o len : Nat) (b : USlice) (h : o + len ≤ arr.size)
    (hS : arr.size < USize.size) (hb : b.size.toNat ≤ len) :
    (addAt arr o len b).1.size = arr.size ∧
      (∀ i, (i < o ∨ o + len ≤ i) → (addAt arr o len b).1[i]! = arr[i]!) ∧
      (addAt arr o len b).1.valAt o len + 2 ^ (64 * len) * (addAt arr o len b).2.toNat =
        arr.valAt o len + b.toNat := by
  obtain ⟨s₁, s₂, s₃, s₄⟩ := sl_spec arr o len h hS
  have hb' : b.size ≤ (sl arr o len).size := USize.le_iff_toNat_le.2 (by rw [s₃]; exact hb)
  refine ⟨by rw [addAt, size_addInto, s₁], fun i hi => ?_, ?_⟩
  · rw [addAt, getElem!_addInto _ _ _ i (by rw [s₂, s₃]; exact hi), s₁]
  · have := valAt_addInto (sl arr o len) b 0 hb'
    rw [s₂, s₃, s₁, UInt64.toNat_zero, Nat.add_zero] at this
    exact this

/-- The slice of piece `i` of `a`. -/
public def pieceSl (a : USlice) (m i : Nat) : USlice :=
  sl a.array (a.start.toNat + min (i * m) a.size.toNat) (min m (a.size.toNat - i * m))

public theorem pieceSl_spec (a : USlice) (m i : Nat) (hS : a.array.size < USize.size) :
    (pieceSl a m i).size.toNat = min m (a.size.toNat - i * m) ∧
      (pieceSl a m i).toNat = piece a m i := by
  have := a.toNat_size
  have := a.stop_le_size
  have := USize.le_iff_toNat_le.1 a.start_le_stop
  obtain ⟨-, -, s₃, s₄⟩ := sl_spec a.array (a.start.toNat + min (i * m) a.size.toNat)
    (min m (a.size.toNat - i * m)) (by lia) hS
  refine ⟨s₃, ?_⟩
  rw [pieceSl, s₄, piece]
  rcases Nat.le_total (i * m) a.size.toNat with h | h
  · rw [Nat.min_eq_left h]
  · rw [show a.size.toNat - i * m = 0 by lia, Nat.min_zero, valAt_zero, valAt_zero]

/-- Loads pieces `i` to `i + cnt - 1` of `a` into the windows of the block at `o`. -/
public def loadLoop (o n m : Nat) (a : USlice) : UInt64Array → Nat → Nat → UInt64Array
  | arr, _, 0 => arr
  | arr, i, cnt + 1 =>
    loadLoop o n m a (addAt arr (o + i * (n + 1)) (n + 1) (pieceSl a m i)).1 (i + 1) cnt

public theorem loadLoop_spec (o n m : Nat) (a : USlice) (hm : m ≤ n + 1)
    (haS : a.array.size < USize.size) (cnt : Nat) :
    ∀ arr i, arr.size < USize.size → o + (i + cnt) * (n + 1) ≤ arr.size →
      (∀ p, i ≤ p → p < i + cnt → coef arr n o p = 0) →
      (loadLoop o n m a arr i cnt).size = arr.size ∧
      (∀ j, (j < o + i * (n + 1) ∨ o + (i + cnt) * (n + 1) ≤ j) →
        (loadLoop o n m a arr i cnt)[j]! = arr[j]!) ∧
      (∀ p, i ≤ p → p < i + cnt → coef (loadLoop o n m a arr i cnt) n o p = piece a m p) := by
  induction cnt with
  | zero => intro arr i _ _ _; exact ⟨rfl, fun _ _ => rfl, fun p h₁ h₂ => absurd h₂ (by lia)⟩
  | succ cnt ih =>
    intro arr i hS hB hz
    have hw := Nat.mul_le_mul_right (n + 1) (show i + 1 ≤ i + (cnt + 1) by lia)
    rw [Nat.add_mul, Nat.one_mul] at hw
    obtain ⟨p₁, p₂⟩ := pieceSl_spec a m i haS
    obtain ⟨a₁, a₂, a₃⟩ := addAt_spec arr (o + i * (n + 1)) (n + 1) (pieceSl a m i) (by lia) hS
      (by rw [p₁]; lia)
    rw [loadLoop]
    generalize addAt arr (o + i * (n + 1)) (n + 1) (pieceSl a m i) = q at *
    obtain ⟨i₁, i₂, i₃⟩ := ih q.1 (i + 1) (by lia) (by rw [a₁]; lia) fun p h₁ h₂ => by
      have d := Nat.mul_le_mul_right (n + 1) h₁
      rw [Nat.add_mul, Nat.one_mul] at d
      rw [← hz p (by lia) (by lia)]
      exact win_congr fun j _ _ => a₂ j (by lia)
    have hq : coef q.1 n o i = piece a m i := by
      have h₀ := hz i (Nat.le_refl _) (by lia)
      have hlt := piece_lt a m i
      have hX : 2 ^ (64 * m) ≤ 2 ^ (64 * (n + 1)) := Nat.pow_le_pow_right (by decide) (by lia)
      have hc : q.2.toNat = 0 := by
        rcases Nat.eq_zero_or_pos q.2.toNat with e | e
        · exact e
        · have := Nat.mul_le_mul_left (2 ^ (64 * (n + 1))) e
          simp only [coef, win] at h₀
          lia
      simp only [coef, win] at h₀ ⊢
      rw [hc, Nat.mul_zero, Nat.add_zero, h₀, p₂, Nat.zero_add] at a₃
      exact a₃
    refine ⟨i₁.trans a₁, fun j hj => ?_, fun p h₁ h₂ => ?_⟩
    · rw [i₂ j (by rw [Nat.add_mul, Nat.one_mul]; lia), a₂ j (by lia)]
    · by_cases e : p = i
      · subst e
        rw [← hq]
        have d := Nat.mul_le_mul_right (n + 1) (Nat.le_refl (p + 1))
        exact win_congr fun j _ _ => i₂ j (by rw [Nat.add_mul, Nat.one_mul]; lia)
      · exact i₃ p (by lia) (by lia)

/-! ## Pointwise products -/

/-- `normAt` with `Nat` offsets, which checks its bounds. -/
public def normG (arr : UInt64Array) (n d : Nat) : UInt64Array :=
  if h : Win arr n.toUSize d.toUSize then normAt arr n.toUSize d.toUSize h else arr

public theorem normG_spec (arr : UInt64Array) (n d : Nat) (hS : arr.size < USize.size)
    (hd : d + n + 1 ≤ arr.size) (hn : 1 ≤ n) :
    (normG arr n d).size = arr.size ∧
      (∀ i, (i < d ∨ d + n + 1 ≤ i) → (normG arr n d)[i]! = arr[i]!) ∧
      win (normG arr n d) n d = win arr n d % fermat n := by
  have hn' : n.toUSize.toNat = n := by rw [USize.toNat_ofNat', Nat.mod_eq_of_lt (by lia)]
  have hd' : d.toUSize.toNat = d := by rw [USize.toNat_ofNat', Nat.mod_eq_of_lt (by lia)]
  have w : Win arr n.toUSize d.toUSize := ⟨by rw [hn', hd']; exact hd, hS⟩
  rw [normG, dite_eq_left w]
  have := normAt_spec arr n.toUSize d.toUSize w (by lia)
  simp only [hn', hd'] at this
  exact this

/-- The value of `reduceAt`: `P_lo - P_mid + P_hi`, plus a multiple of `F`. -/
private theorem reduce_eq {V Plo Pmid c H Bn : Nat} (h : V + Pmid = Plo + Bn * c) (hc : c ≤ 1)
    (hH : H ≤ 1) (hV : V < Bn) :
    Plo + Bn * Pmid + Bn * Bn * H = V + (c + H) + (Bn + 1) * (Pmid - c + H * (Bn - 1)) := by
  obtain ⟨B', rfl⟩ : ∃ B', Bn = B' + 1 := ⟨Bn - 1, by lia⟩
  rcases Nat.lt_or_ge c 1 with ec | ec <;> rcases Nat.lt_or_ge H 1 with eH | eH
  · obtain rfl : c = 0 := by lia
    obtain rfl : H = 0 := by lia
    grind
  · obtain rfl : c = 0 := by lia
    obtain rfl : H = 1 := by lia
    grind
  · obtain rfl : c = 1 := by lia
    obtain rfl : H = 0 := by lia
    obtain ⟨P', rfl⟩ : ∃ P', Pmid = P' + 1 := ⟨Pmid - 1, by lia⟩
    grind
  · obtain rfl : c = 1 := by lia
    obtain rfl : H = 1 := by lia
    obtain ⟨P', rfl⟩ : ∃ P', Pmid = P' + 1 := ⟨Pmid - 1, by lia⟩
    grind

/-- Writes `P % F` into the window at `d`, for `P` of `2 n + 2` limbs: `P_lo - P_mid + P_hi`. -/
public def reduceAt (arr : UInt64Array) (n d : Nat) (P : UInt64Array) : UInt64Array :=
  let q := subN (sl arr d n) (sl P 0 n) (sl P n n) 0
  -- The carry first, so that the pair is dead when the array is written.
  let c := q.2 + P[2 * n]!
  let a := q.1
  let a := if h : (d + n).toUSize.toNat < a.size then a.uset (d + n).toUSize 0 h else a
  let a := if h : LoopBound a d.toUSize (n + 1).toUSize
    then (incrAt a d.toUSize (n + 1).toUSize h 0 c).1 else a
  normG a n d

set_option maxHeartbeats 400000 in
public theorem reduceAt_spec (arr : UInt64Array) (n d : Nat) (P : UInt64Array)
    (hS : arr.size < USize.size) (hd : d + n + 1 ≤ arr.size) (hn : 1 ≤ n)
    (hP : P.size = 2 * n + 2) (hPS : P.size < USize.size)
    (hPv : P.valAt 0 (2 * n + 2) ≤ 2 ^ (64 * n) * 2 ^ (64 * n)) :
    (reduceAt arr n d P).size = arr.size ∧
      (∀ i, (i < d ∨ d + n + 1 ≤ i) → (reduceAt arr n d P)[i]! = arr[i]!) ∧
      win (reduceAt arr n d P) n d = P.valAt 0 (2 * n + 2) % fermat n := by
  obtain ⟨r₁, r₂, r₃, -⟩ := sl_spec arr d n (by lia) hS
  obtain ⟨a₁, a₂, a₃, -⟩ := sl_spec P 0 n (by lia) hPS
  obtain ⟨b₁, b₂, b₃, -⟩ := sl_spec P n n (by lia) hPS
  have hdn : (d + n).toUSize.toNat = d + n := by rw [USize.toNat_ofNat', Nat.mod_eq_of_lt (by lia)]
  have hd' : d.toUSize.toNat = d := by rw [USize.toNat_ofNat', Nat.mod_eq_of_lt (by lia)]
  have hn1 : (n + 1).toUSize.toNat = n + 1 := by
    rw [USize.toNat_ofNat', Nat.mod_eq_of_lt (by lia)]
  -- `P_lo - P_mid`.
  have hs₁ := size_subN (sl arr d n) (sl P 0 n) (sl P n n) 0
  have hs₂ := valAt_subN (sl arr d n) (sl P 0 n) (sl P n n) 0
  simp only [r₂, r₃, a₁, a₂, a₃, b₁, b₂, b₃, Nat.min_self, UInt64.toNat_zero, Nat.add_zero,
    r₁] at hs₁ hs₂
  have hs₃ := fun i hi => getElem!_subN (sl arr d n) (sl P 0 n) (sl P n n) 0 i hi
  simp only [r₂, r₃, a₃, b₃, Nat.min_self, r₁] at hs₃
  dsimp only [reduceAt]
  generalize subN (sl arr d n) (sl P 0 n) (sl P n n) 0 = q at *
  -- The top limb.
  have hidx : (d + n).toUSize.toNat < q.1.size := by rw [hdn, hs₁]; lia
  rw [dite_eq_left hidx]
  have t₁ : (q.1.uset (d + n).toUSize 0 hidx).valAt d (n + 1) = q.1.valAt d n := by
    rw [valAt_top, getElem!_uset, valAt_uset_of _ _ _ _ _ _ (by rw [hdn]; lia)]
    simp only [hdn, ↓reduceIte, UInt64.toNat_zero, Nat.mul_zero, Nat.add_zero]
  have hlb : LoopBound (q.1.uset (d + n).toUSize 0 hidx) d.toUSize (n + 1).toUSize := by
    constructor <;> simp only [size_uset, hd', hn1, hs₁] <;> lia
  rw [dite_eq_left hlb]
  -- The increment by the borrow and `P_hi`.
  have hP₃ := valAt_lt P 0 n
  have hP₄ := valAt_lt P n n
  have hPv' : P.valAt 0 (2 * n + 2) = P.valAt 0 n + 2 ^ (64 * n) * P.valAt n n +
      2 ^ (64 * n) * 2 ^ (64 * n) * (P[2 * n]!.toNat + 2 ^ 64 * P[2 * n + 1]!.toNat) := by
    have e₁ := UInt64Array.valAt_add P 0 n (n + 2)
    have e₂ := UInt64Array.valAt_add P n n 2
    have e₃ := valAt_succ P (n + n) 1
    have e₄ := valAt_one P (n + n + 1)
    rw [show n + (n + 2) = 2 * n + 2 by lia, Nat.zero_add] at e₁
    rw [e₂, e₃, e₄, show n + n = 2 * n by lia] at e₁
    rw [e₁]
    grind
  have hB : 1 ≤ 2 ^ (64 * n) := Nat.one_le_two_pow
  have hhi : P[2 * n]!.toNat + 2 ^ 64 * P[2 * n + 1]!.toNat ≤ 1 := by
    rcases Nat.lt_or_ge (P[2 * n]!.toNat + 2 ^ 64 * P[2 * n + 1]!.toNat) 2 with e | e
    · lia
    · have := Nat.mul_le_mul_left (2 ^ (64 * n) * 2 ^ (64 * n)) e
      have : 1 ≤ 2 ^ (64 * n) * 2 ^ (64 * n) := Nat.mul_le_mul hB hB
      lia
  have hP₁ : P[2 * n + 1]!.toNat = 0 := by
    rcases Nat.eq_zero_or_pos P[2 * n + 1]!.toNat with e | e
    · exact e
    · have := Nat.mul_le_mul_left (2 ^ 64) e; lia
  simp only [hP₁, Nat.mul_zero, Nat.add_zero] at hPv' hhi
  have hc₁ : q.2.toNat ≤ 1 := by
    rcases Nat.lt_or_ge q.2.toNat 2 with e | e
    · lia
    · have := Nat.mul_le_mul_left (2 ^ (64 * n)) e
      have := valAt_lt q.1 d n
      lia
  have hc : (q.2 + P[2 * n]!).toNat = q.2.toNat + P[2 * n]!.toNat := by
    rw [UInt64.toNat_add, Nat.mod_eq_of_lt (by lia)]
  obtain ⟨i₁, i₂, i₃⟩ := incrAt_spec _ d.toUSize (n + 1).toUSize hlb 0 (q.2 + P[2 * n]!)
  simp only [USize.toNat_zero, Nat.add_zero, Nat.sub_zero, hd', hn1, size_uset] at i₁ i₂ i₃
  rw [t₁, hc] at i₃
  generalize incrAt _ d.toUSize (n + 1).toUSize hlb 0 (q.2 + P[2 * n]!) = q' at *
  -- No carry out of the window.
  have hq' := valAt_lt q.1 d n
  have hB1 : 2 ^ (64 * (n + 1)) = 2 ^ (64 * n) * 2 ^ 64 := by rw [Nat.mul_succ, Nat.pow_add]
  have hc' : q'.2.toNat = 0 := by
    rcases Nat.eq_zero_or_pos q'.2.toNat with e | e
    · exact e
    · have := Nat.mul_le_mul_left (2 ^ (64 * (n + 1))) e
      rw [hB1] at this
      have : 2 ^ (64 * n) * 2 ≤ 2 ^ (64 * n) * 2 ^ 64 := Nat.mul_le_mul_left _ (by decide)
      lia
  rw [hc', Nat.mul_zero, Nat.add_zero] at i₃
  obtain ⟨n₁, n₂, n₃⟩ := normG_spec q'.1 n d (by rw [i₁, hs₁]; exact hS) (by rw [i₁, hs₁]; exact hd)
    hn
  refine ⟨by rw [n₁, i₁, hs₁], fun i hi => ?_, ?_⟩
  · rw [n₂ i hi, i₂ i hi, getElem!_uset, ite_eq_right_iff.2 (fun e => by rw [hdn] at e; lia),
      hs₃ i (by lia)]
  · rw [n₃, win, i₃]
    simp only [fermat]
    rw [hPv']
    generalize P[2 * n]!.toNat = H at *
    generalize P.valAt 0 n = Plo at *
    generalize P.valAt n n = Pmid at *
    generalize q.1.valAt d n = V at *
    generalize q.2.toNat = c at *
    generalize 2 ^ (64 * n) = Bn at *
    rw [reduce_eq hs₂ hc₁ hhi hq', Nat.add_mul_mod_self_left]

/--
The pointwise products of windows `p` to `p + cnt - 1` of the blocks at `oA` and `oB`, into the
first, through the array `P` of `2 n + 2` limbs.
-/
public def pointLoop (n oA oB : Nat) : UInt64Array → UInt64Array → Nat → Nat → UInt64Array
  | arr, _, _, 0 => arr
  | arr, P, p, cnt + 1 =>
    let P := mulToom P.toUSlice (sl arr (oA + p * (n + 1)) (n + 1))
      (sl arr (oB + p * (n + 1)) (n + 1))
    pointLoop n oA oB (reduceAt arr n (oA + p * (n + 1)) P) P (p + 1) cnt

public theorem pointLoop_spec (n oA oB : Nat) (hn : 1 ≤ n) (cnt : Nat) :
    ∀ arr P p, P.size = 2 * n + 2 → P.size < USize.size → arr.size < USize.size →
      oA + (p + cnt) * (n + 1) ≤ oB → oB + (p + cnt) * (n + 1) ≤ arr.size →
      (∀ q, p ≤ q → q < p + cnt → coef arr n oA q < fermat n ∧ coef arr n oB q < fermat n) →
      (pointLoop n oA oB arr P p cnt).size = arr.size ∧
      (∀ j, (j < oA + p * (n + 1) ∨ oA + (p + cnt) * (n + 1) ≤ j) →
        (pointLoop n oA oB arr P p cnt)[j]! = arr[j]!) ∧
      (∀ q, p ≤ q → q < p + cnt →
        coef (pointLoop n oA oB arr P p cnt) n oA q =
          coef arr n oA q * coef arr n oB q % fermat n) := by
  induction cnt with
  | zero =>
    intro arr P p _ _ _ _ _ _
    exact ⟨rfl, fun _ _ => rfl, fun q h₁ h₂ => absurd h₂ (by lia)⟩
  | succ cnt ih =>
    intro arr P p hP hPS hS hAB hB hv
    have hw := Nat.mul_le_mul_right (n + 1) (show p + 1 ≤ p + (cnt + 1) by lia)
    rw [Nat.add_mul, Nat.one_mul] at hw
    obtain ⟨x₁, x₂, x₃, x₄⟩ := sl_spec arr (oA + p * (n + 1)) (n + 1) (by lia) hS
    obtain ⟨y₁, y₂, y₃, y₄⟩ := sl_spec arr (oB + p * (n + 1)) (n + 1) (by lia) hS
    have hPs := size_toUSlice P hPS
    have hx₀ : 0 < (sl arr (oA + p * (n + 1)) (n + 1)).size :=
      USize.lt_iff_toNat_lt.2 (by rw [x₃, USize.toNat_zero]; lia)
    have hy₀ : 0 < (sl arr (oB + p * (n + 1)) (n + 1)).size :=
      USize.lt_iff_toNat_lt.2 (by rw [y₃, USize.toNat_zero]; lia)
    have m₁ := size_mulToom P.toUSlice (sl arr (oA + p * (n + 1)) (n + 1))
      (sl arr (oB + p * (n + 1)) (n + 1))
    have m₂ := valAt_mulToom P.toUSlice (sl arr (oA + p * (n + 1)) (n + 1))
      (sl arr (oB + p * (n + 1)) (n + 1)) hx₀ hy₀ (by rw [x₃, y₃, hPs]; lia)
    rw [x₃, y₃, x₄, y₄, start_toUSlice, USize.toNat_zero, show n + 1 + (n + 1) = 2 * n + 2 by lia]
      at m₂
    rw [array_toUSlice] at m₁
    rw [pointLoop]
    generalize mulToom P.toUSlice (sl arr (oA + p * (n + 1)) (n + 1))
      (sl arr (oB + p * (n + 1)) (n + 1)) = P' at *
    obtain ⟨hvA, hvB⟩ := hv p (Nat.le_refl _) (by lia)
    simp only [coef, win, fermat] at hvA hvB
    obtain ⟨r₁, r₂, r₃⟩ := reduceAt_spec arr n (oA + p * (n + 1)) P' hS (by lia) hn (by rw [m₁, hP])
      (by rw [m₁]; exact hPS) (by rw [m₂]; exact Nat.mul_le_mul (by lia) (by lia))
    generalize reduceAt arr n (oA + p * (n + 1)) P' = a₁ at *
    have hu : ∀ q, p + 1 ≤ q → q < p + (cnt + 1) →
        coef a₁ n oA q = coef arr n oA q ∧ coef a₁ n oB q = coef arr n oB q := by
      intro q h₁ h₂
      have d := Nat.mul_le_mul_right (n + 1) h₁
      have d' := Nat.mul_le_mul_right (n + 1) (show q + 1 ≤ p + (cnt + 1) by lia)
      rw [Nat.add_mul, Nat.one_mul] at d d'
      exact ⟨win_congr fun j _ _ => r₂ j (by lia), win_congr fun j _ _ => r₂ j (by lia)⟩
    obtain ⟨i₁, i₂, i₃⟩ := ih a₁ P' (p + 1) (by rw [m₁, hP]) (by rw [m₁]; exact hPS)
      (by rw [r₁]; exact hS) (by lia) (by rw [r₁]; lia) fun q h₁ h₂ => by
        rw [(hu q h₁ (by lia)).1, (hu q h₁ (by lia)).2]; exact hv q (by lia) (by lia)
    refine ⟨i₁.trans r₁, fun j hj => ?_, fun q h₁ h₂ => ?_⟩
    · rw [i₂ j (by rw [Nat.add_mul, Nat.one_mul]; lia), r₂ j (by lia)]
    · by_cases e : q = p
      · subst e
        have : coef (pointLoop n oA oB a₁ P' (q + 1) cnt) n oA q = coef a₁ n oA q :=
          win_congr fun j _ _ => i₂ j (by lia)
        rw [this]
        exact r₃.trans (by rw [m₂])
      · rw [i₃ q (by lia) (by lia), (hu q (by lia) h₂).1, (hu q (by lia) h₂).2]

/-! ## Scaling -/

/--
Divides windows `l` to `l + cnt - 1` of the block at `o` by `2ᵏ`, modulo `F`: multiplies them by
`2^(N - k)` into the scratch window `t`, then subtracts that from the zero window `z`, since
`2^(-k) ≡ -2^(N - k)`.
-/
public def scaleLoop (n o t z k : Nat) : UInt64Array → Nat → Nat → UInt64Array
  | arr, _, 0 => arr
  | arr, l, cnt + 1 =>
    scaleLoop n o t z k (subModG (mulPow2G arr n t (o + l * (n + 1)) (64 * n - k)) n
      (o + l * (n + 1)) z t) (l + 1) cnt

public theorem scaleLoop_spec (n o t z k : Nat) (hn : 1 ≤ n) (hk : 1 ≤ k)
    (h64 : 64 * n < USize.size) (cnt : Nat) :
    ∀ arr l, arr.size < USize.size → o + (l + cnt) * (n + 1) ≤ arr.size →
      t + n + 1 ≤ arr.size → z + n + 1 ≤ arr.size →
      (t + n + 1 ≤ o + l * (n + 1) ∨ o + (l + cnt) * (n + 1) ≤ t) →
      (z + n + 1 ≤ o + l * (n + 1) ∨ o + (l + cnt) * (n + 1) ≤ z) →
      (t + n + 1 ≤ z ∨ z + n + 1 ≤ t) → win arr n z = 0 →
      (∀ q, l ≤ q → q < l + cnt → coef arr n o q < fermat n) →
      (scaleLoop n o t z k arr l cnt).size = arr.size ∧
      (∀ j, (j < o + l * (n + 1) ∨ o + (l + cnt) * (n + 1) ≤ j) → (j < t ∨ t + n + 1 ≤ j) →
        (scaleLoop n o t z k arr l cnt)[j]! = arr[j]!) ∧
      (∀ q, l ≤ q → q < l + cnt → coef (scaleLoop n o t z k arr l cnt) n o q =
        (fermat n - coef arr n o q * 2 ^ (64 * n - k) % fermat n) % fermat n) := by
  induction cnt with
  | zero =>
    intro arr l _ _ _ _ _ _ _ _ _
    exact ⟨rfl, fun _ _ _ => rfl, fun q h₁ h₂ => absurd h₂ (by lia)⟩
  | succ cnt ih =>
    intro arr l hS hB ht hz htd hzd htz hz0 hv
    rw [scaleLoop]
    have hF : 0 < fermat n := by simp [fermat]
    have hw := Nat.mul_le_mul_right (n + 1) (show l + 1 ≤ l + (cnt + 1) by lia)
    rw [Nat.add_mul, Nat.one_mul] at hw
    obtain ⟨m₁, m₂, m₃⟩ := mulPow2G_spec arr n t (o + l * (n + 1)) (64 * n - k) hS ht (by lia) hn
      (by lia) (by lia) (by lia) (hv l (Nat.le_refl _) (by lia))
    generalize mulPow2G arr n t (o + l * (n + 1)) (64 * n - k) = a₁ at *
    have z₁ := win_of_untouched m₂ (o := z) (by lia)
    have x₁ := win_of_untouched m₂ (o := o + l * (n + 1)) (by lia)
    obtain ⟨s₁, s₂, s₃⟩ := subModG_spec a₁ n (o + l * (n + 1)) z t (by lia) (by lia) (by lia)
      (by lia) hn (by lia) (by lia) (by rw [z₁, hz0]; exact hF) (by rw [m₃]; exact Nat.mod_lt _ hF)
    generalize subModG a₁ n (o + l * (n + 1)) z t = a₂ at *
    have hu : ∀ q, l + 1 ≤ q → q < l + (cnt + 1) → coef a₂ n o q = coef arr n o q := by
      intro q h₁ h₂
      have d := Nat.mul_le_mul_right (n + 1) h₁
      have d' := Nat.mul_le_mul_right (n + 1) (show q + 1 ≤ l + (cnt + 1) by lia)
      rw [Nat.add_mul, Nat.one_mul] at d d'
      show win a₂ n _ = win arr n _
      rw [win_of_untouched s₂ (by lia), win_of_untouched m₂ (by lia)]
    have z₂ := win_of_untouched s₂ (o := z) (by lia)
    obtain ⟨i₁, i₂, i₃⟩ := ih a₂ (l + 1) (by lia) (by lia) (by lia) (by lia) (by lia) (by lia) htz
      (by rw [z₂, z₁, hz0]) fun q h₁ h₂ => by rw [hu q h₁ (by lia)]; exact hv q (by lia) (by lia)
    refine ⟨by rw [i₁, s₁, m₁], fun j h₁ h₂ => ?_, fun q h₁ h₂ => ?_⟩
    · rw [i₂ j (by lia) h₂, s₂ j (by lia), m₂ j h₂]
    · by_cases e : q = l
      · subst e
        have : coef (scaleLoop n o t z k a₂ (q + 1) cnt) n o q = coef a₂ n o q :=
          win_congr fun j _ _ => i₂ j (by lia) (by lia)
        rw [this]
        show win a₂ n _ = _
        rw [s₃, z₁, hz0, Nat.zero_add, m₃]
      · rw [i₃ q (by lia) (by lia), hu q (by lia) h₂]

/-! ## Recombination -/

/-- The algebra of `addCoef`: the carry out of the region is zero. -/
private theorem add_coef_eq {L₀ W R W' R' V c c' Po Pl Pr : Nat}
    (hw : W' + Pl * c = W + V) (hr : R' + Pr * c' = R + c)
    (hlt : L₀ + Po * (W + Pl * R) + Po * V < Po * Pl * Pr) :
    L₀ + Po * (W' + Pl * R') = L₀ + Po * (W + Pl * R) + Po * V := by
  have hc' : c' = 0 := by
    rcases Nat.eq_zero_or_pos c' with e | e
    · exact e
    · exfalso
      have h₁ : Po * (Pl * Pr) ≤ Po * (Pl * (Pr * c')) :=
        Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ (Nat.le_mul_of_pos_right _ e))
      have h₂ : Po * (W + Pl * R) + Po * V = Po * (W' + Pl * R') + Po * (Pl * (Pr * c')) := by
        grind
      grind
  subst hc'
  grind

/--
Adds the window of `len₀` limbs at `so` of `src` to the region of `T` limbs at `o` of `arr`, from
its limb `off` on, with the carry out of the window into the rest of the region, stopping as soon
as it is zero. Only the limbs of the window inside the region are added.
-/
public def addCoef (arr : UInt64Array) (o T off : Nat) (src : UInt64Array) (so len₀ : Nat) :
    UInt64Array :=
  let len := min len₀ (T - off)
  let q := addAt arr (o + off) len (sl src so len)
  -- The carry first, so that the pair is dead when the array is written.
  let c := q.2
  let a := q.1
  if h : LoopBound a (o + off + len).toUSize (T - off - len).toUSize
  then (incrAt a (o + off + len).toUSize (T - off - len).toUSize h 0 c).1 else a

set_option maxHeartbeats 400000 in
public theorem addCoef_spec (arr : UInt64Array) (o T off : Nat) (src : UInt64Array) (so len₀ : Nat)
    (hS : arr.size < USize.size) (hT : o + T ≤ arr.size) (hoff : off ≤ T)
    (hsS : src.size < USize.size) (hs : so + len₀ ≤ src.size)
    (hV : arr.valAt o T + 2 ^ (64 * off) * src.valAt so len₀ < 2 ^ (64 * T)) :
    (addCoef arr o T off src so len₀).size = arr.size ∧
      (∀ i, (i < o ∨ o + T ≤ i) → (addCoef arr o T off src so len₀)[i]! = arr[i]!) ∧
      (addCoef arr o T off src so len₀).valAt o T =
        arr.valAt o T + 2 ^ (64 * off) * src.valAt so len₀ := by
  -- Only the limbs inside the region count.
  have hsplitT : 2 ^ (64 * T) = 2 ^ (64 * off) * 2 ^ (64 * (T - off)) := by
    rw [← Nat.pow_add]; congr 1; lia
  have hVr : src.valAt so len₀ < 2 ^ (64 * (T - off)) := by
    rw [hsplitT] at hV
    rcases Nat.lt_or_ge (src.valAt so len₀) (2 ^ (64 * (T - off))) with e | e
    · exact e
    · have := Nat.mul_le_mul_left (2 ^ (64 * off)) e; lia
  have hV' : src.valAt so (min len₀ (T - off)) = src.valAt so len₀ := by
    rcases Nat.le_total len₀ (T - off) with h | h
    · rw [Nat.min_eq_left h]
    · rw [Nat.min_eq_right h]
      have e := UInt64Array.valAt_add src so (T - off) (len₀ - (T - off))
      rw [show T - off + (len₀ - (T - off)) = len₀ by lia] at e
      have hP := Nat.two_pow_pos (64 * (T - off))
      rcases Nat.eq_zero_or_pos (src.valAt (so + (T - off)) (len₀ - (T - off))) with e₀ | e₀
      · rw [e, e₀, Nat.mul_zero, Nat.add_zero]
      · have := Nat.mul_le_mul_left (2 ^ (64 * (T - off))) e₀; lia
  obtain ⟨b₁, -, -, b₄⟩ := sl_spec src so (min len₀ (T - off)) (by lia) hsS
  obtain ⟨a₁, a₂, a₃⟩ := addAt_spec arr (o + off) (min len₀ (T - off))
    (sl src so (min len₀ (T - off))) (by lia) hS
    (by rw [(sl_spec src so _ (by lia) hsS).2.2.1]; exact Nat.le_refl _)
  rw [b₄, hV'] at a₃
  dsimp only [addCoef]
  generalize addAt arr (o + off) (min len₀ (T - off)) (sl src so (min len₀ (T - off))) = q at *
  have ho₁ : (o + off + min len₀ (T - off)).toUSize.toNat = o + off + min len₀ (T - off) := by
    rw [USize.toNat_ofNat', Nat.mod_eq_of_lt (by lia)]
  have ho₂ : (T - off - min len₀ (T - off)).toUSize.toNat = T - off - min len₀ (T - off) := by
    rw [USize.toNat_ofNat', Nat.mod_eq_of_lt (by lia)]
  have hlb : LoopBound q.1 (o + off + min len₀ (T - off)).toUSize
      (T - off - min len₀ (T - off)).toUSize := by
    refine ⟨?_, ?_⟩
    · rw [ho₁, ho₂, a₁]; lia
    · rw [ho₁, ho₂]; lia
  rw [dite_eq_left hlb]
  obtain ⟨i₁, i₂, i₃⟩ := incrAt_spec q.1 _ _ hlb 0 q.2
  simp only [USize.toNat_zero, Nat.add_zero, Nat.sub_zero, ho₁, ho₂] at i₁ i₂ i₃
  refine ⟨by rw [i₁, a₁], fun i hi => by rw [i₂ i (by lia), a₂ i (by lia)], ?_⟩
  -- The region in three parts: below `off`, the window, and the rest.
  have hreg : ∀ a : UInt64Array, a.valAt o T = a.valAt o off + 2 ^ (64 * off) *
      (a.valAt (o + off) (min len₀ (T - off)) + 2 ^ (64 * min len₀ (T - off)) *
        a.valAt (o + off + min len₀ (T - off)) (T - off - min len₀ (T - off))) := by
    intro a
    rw [← UInt64Array.valAt_add, ← UInt64Array.valAt_add]
    congr 1; lia
  have hlo₁ : (incrAt q.1 _ _ hlb 0 q.2).1.valAt o off = arr.valAt o off :=
    UInt64Array.valAt_congr _ fun i _ _ => by rw [i₂ i (by lia), a₂ i (by lia)]
  have hw₁ : (incrAt q.1 _ _ hlb 0 q.2).1.valAt (o + off) (min len₀ (T - off)) =
      q.1.valAt (o + off) (min len₀ (T - off)) :=
    UInt64Array.valAt_congr _ fun i _ _ => i₂ i (by lia)
  have hr₁ : q.1.valAt (o + off + min len₀ (T - off)) (T - off - min len₀ (T - off)) =
      arr.valAt (o + off + min len₀ (T - off)) (T - off - min len₀ (T - off)) :=
    UInt64Array.valAt_congr _ fun i _ _ => a₂ i (by lia)
  rw [hr₁] at i₃
  rw [hreg, hreg arr, hlo₁, hw₁]
  have hsplit2 : 2 ^ (64 * (T - off)) = 2 ^ (64 * min len₀ (T - off)) *
      2 ^ (64 * (T - off - min len₀ (T - off))) := by rw [← Nat.pow_add]; congr 1; lia
  rw [hsplitT, hsplit2, ← Nat.mul_assoc, hreg arr] at hV
  exact add_coef_eq a₃ i₃ hV

/--
Adds windows `l` to `l + cnt - 1` of the block at `oA` of `src`, the coefficients, to the region
of `T` limbs at `o` of `arr`, window `i` from limb `i m` on.
-/
public def recLoop (T m n oA : Nat) (src : UInt64Array) : UInt64Array → Nat → Nat → Nat →
    UInt64Array
  | arr, _, _, 0 => arr
  | arr, o, l, cnt + 1 =>
    recLoop T m n oA src
      (if l * m ≤ T then addCoef arr o T (l * m) src (oA + l * (n + 1)) (n + 1) else arr) o (l + 1)
      cnt

public theorem recLoop_spec (T m n oA : Nat) (src : UInt64Array) (hsS : src.size < USize.size)
    (cnt : Nat) :
    ∀ arr o l, arr.size < USize.size → o + T ≤ arr.size → oA + (l + cnt) * (n + 1) ≤ src.size →
      arr.valAt o T + sumRange (fun i => 2 ^ (64 * ((l + i) * m)) * coef src n oA (l + i)) cnt <
        2 ^ (64 * T) →
      (recLoop T m n oA src arr o l cnt).size = arr.size ∧
      (∀ j, (j < o ∨ o + T ≤ j) → (recLoop T m n oA src arr o l cnt)[j]! = arr[j]!) ∧
      (recLoop T m n oA src arr o l cnt).valAt o T = arr.valAt o T +
        sumRange (fun i => 2 ^ (64 * ((l + i) * m)) * coef src n oA (l + i)) cnt := by
  induction cnt with
  | zero => intro arr o l _ _ _ _; exact ⟨rfl, fun _ _ => rfl, by simp [recLoop]⟩
  | succ cnt ih =>
    intro arr o l hS hT hsrc hsum
    rw [sumRange_succ_left] at hsum ⊢
    simp only [Nat.add_zero] at hsum ⊢
    have hw := Nat.mul_le_mul_right (n + 1) (show l + 1 ≤ l + (cnt + 1) by lia)
    rw [Nat.add_mul, Nat.one_mul] at hw
    have hs' : sumRange (fun i => 2 ^ (64 * ((l + (i + 1)) * m)) * coef src n oA (l + (i + 1)))
        cnt = sumRange (fun i => 2 ^ (64 * ((l + 1 + i) * m)) * coef src n oA (l + 1 + i)) cnt :=
      sumRange_congr fun i _ => by rw [show l + (i + 1) = l + 1 + i by lia]
    rw [hs'] at hsum ⊢
    rw [recLoop]
    split
    · rename_i hl
      obtain ⟨c₁, c₂, c₃⟩ := addCoef_spec arr o T (l * m) src (oA + l * (n + 1)) (n + 1) hS hT hl
        hsS (by lia) (by simp only [coef, win] at hsum; lia)
      generalize addCoef arr o T (l * m) src (oA + l * (n + 1)) (n + 1) = a₁ at *
      obtain ⟨i₁, i₂, i₃⟩ := ih a₁ o (l + 1) (by lia) (by lia) (by lia)
        (by rw [c₃]; simp only [coef, win] at hsum ⊢; lia)
      refine ⟨i₁.trans c₁, fun j hj => by rw [i₂ j hj, c₂ j hj], ?_⟩
      rw [i₃, c₃]
      simp only [coef, win]
      lia
    · rename_i hl
      -- The coefficient starts past the region, so it is zero.
      have hc : coef src n oA l = 0 := by
        rcases Nat.eq_zero_or_pos (coef src n oA l) with h | h
        · exact h
        · have := Nat.mul_le_mul_left (2 ^ (64 * (l * m))) h
          have : 2 ^ (64 * T) ≤ 2 ^ (64 * (l * m)) := Nat.pow_le_pow_right (by decide) (by lia)
          lia
      obtain ⟨i₁, i₂, i₃⟩ := ih arr o (l + 1) hS hT (by lia) (by rw [hc] at hsum; lia)
      refine ⟨i₁, i₂, ?_⟩
      rw [i₃, hc]
      lia

/-! ## The coefficients -/

private theorem sum_eq_polyVal (αL : List Nat) (σ q K : Nat) (h : αL.length ≤ K) :
    sumRange (fun i => αL.getD i 0 * 2 ^ (σ * i * q)) K = polyVal (2 ^ (σ * q)) αL := by
  rw [polyVal_eq_sumRange _ αL K h]
  exact sumRange_congr fun i _ => by rw [← Nat.pow_mul]; congr 2; grind

/--
The coefficients from the transforms: the forward transforms of `α` and `β`, their pointwise
products, the inverse transform and the division by `2ᵏ` give the coefficients of `α β`, exactly
when they are less than `F`.
-/
public theorem fft_coef (αL βL : List Nat) (k n σ X : Nat) (hk : 1 ≤ k)
    (hσ : σ * 2 ^ k = 2 * (64 * n)) (hlen : αL.length + βL.length ≤ 2 ^ k + 1) (hβ : βL ≠ [])
    (hαX : ∀ a ∈ αL, a < X) (hβX : ∀ b ∈ βL, b < X) (hbits : 2 ^ k * (X * X) ≤ 2 ^ (64 * n))
    (hαK : αL.length ≤ 2 ^ k) (hβK : βL.length ≤ 2 ^ k) (l : Nat) (hl : l < 2 ^ k) :
    (fermat n - sumRange (fun p =>
        sumRange (fun i => αL.getD i 0 * 2 ^ (σ * i * rev k p)) (2 ^ k) % fermat n *
          (sumRange (fun i => βL.getD i 0 * 2 ^ (σ * i * rev k p)) (2 ^ k) % fermat n) %
            fermat n * 2 ^ ((2 * (64 * n) - σ) * rev k p * l)) (2 ^ k) % fermat n *
        2 ^ (64 * n - k) % fermat n) % fermat n = (polyMul αL βL).getD l 0 := by
  have hF : fermat n = 2 ^ (64 * n) + 1 := rfl
  have hF₀ : 0 < fermat n := by simp [fermat]
  generalize hZ : polyMul αL βL = Z
  have hZK : Z.length ≤ 2 ^ k := by
    rw [← hZ]; have := length_polyMul αL βL hβ; lia
  -- `σ 2ᵏ⁻¹ = N`, and `τ = 2 N - σ` is the inverse root.
  have hk₁ : 2 ^ k = 2 * 2 ^ (k - 1) := by
    rw [← Nat.pow_succ']; congr 1; lia
  have hσN : σ * 2 ^ (k - 1) = 64 * n := by rw [hk₁] at hσ; lia
  have hσle : σ ≤ 2 * (64 * n) := by
    rw [← hσ]; exact Nat.le_mul_of_pos_right _ (Nat.two_pow_pos _)
  -- The pointwise products are the values of `Z`.
  have hP : ∀ p, MEq (fermat n)
      (sumRange (fun i => αL.getD i 0 * 2 ^ (σ * i * rev k p)) (2 ^ k) % fermat n *
        (sumRange (fun i => βL.getD i 0 * 2 ^ (σ * i * rev k p)) (2 ^ k) % fermat n) % fermat n)
      (polyVal (2 ^ (σ * rev k p)) Z) := by
    intro p
    rw [sum_eq_polyVal _ _ _ _ hαK, sum_eq_polyVal _ _ _ _ hβK, ← hZ, polyVal_polyMul]
    exact (MEq.mod _ _).trans (MEq.mul (MEq.mod _ _) (MEq.mod _ _))
  -- The inverse transform, reindexed by `rev`.
  have hV : MEq (fermat n) (sumRange (fun p =>
      sumRange (fun i => αL.getD i 0 * 2 ^ (σ * i * rev k p)) (2 ^ k) % fermat n *
        (sumRange (fun i => βL.getD i 0 * 2 ^ (σ * i * rev k p)) (2 ^ k) % fermat n) %
          fermat n * 2 ^ ((2 * (64 * n) - σ) * rev k p * l)) (2 ^ k) % fermat n)
      (2 ^ k * Z.getD l 0) := by
    refine (MEq.mod _ _).trans ?_
    refine (MEq.sum fun p _ => MEq.mul (hP p) (MEq.refl _ _)).trans ?_
    rw [sumRange_rev (fun q => polyVal (2 ^ (σ * q)) Z * 2 ^ ((2 * (64 * n) - σ) * q * l)) k]
    have e : sumRange (fun q => polyVal (2 ^ (σ * q)) Z * 2 ^ ((2 * (64 * n) - σ) * q * l))
        (2 ^ k) = sumRange (fun j => sumRange (fun i => Z.getD i 0 * (2 ^ σ) ^ (i * j)) (2 ^ k) *
          (2 ^ (2 * (64 * n) - σ)) ^ (j * l)) (2 ^ k) := by
      refine sumRange_congr fun q _ => ?_
      rw [polyVal_eq_sumRange _ Z _ hZK, ← Nat.pow_mul, Nat.mul_assoc]
      congr 1
      exact sumRange_congr fun i _ => by rw [← Nat.pow_mul, ← Nat.pow_mul]; congr 2; grind
    rw [e]
    refine inverse_mod (2 ^ σ) (2 ^ (2 * (64 * n) - σ)) (fermat n) k hk ?_ ?_ _ l hl
    · rw [← Nat.pow_mul, hσN]; simp [fermat]
    · rw [← Nat.pow_add, show σ + (2 * (64 * n) - σ) = 2 * (64 * n) by lia]
      exact pow_two_N hF
  -- Dividing by `2ᵏ`: `-2^(N - k) 2ᵏ = -2ᴺ ≡ 1`.
  have hc : MEq (fermat n) ((fermat n - sumRange (fun p =>
      sumRange (fun i => αL.getD i 0 * 2 ^ (σ * i * rev k p)) (2 ^ k) % fermat n *
        (sumRange (fun i => βL.getD i 0 * 2 ^ (σ * i * rev k p)) (2 ^ k) % fermat n) %
          fermat n * 2 ^ ((2 * (64 * n) - σ) * rev k p * l)) (2 ^ k) % fermat n *
        2 ^ (64 * n - k) % fermat n) % fermat n) (Z.getD l 0) := by
    have hk64 : k ≤ 64 * n := by
      have : 2 ^ k ≤ 2 ^ (64 * n) := Nat.le_trans (Nat.le_mul_of_pos_right _ (by
        have : 0 < X := by
          rcases βL with _ | ⟨b, _⟩
          · exact absurd rfl hβ
          · exact Nat.lt_of_le_of_lt (Nat.zero_le _) (hβX b (by simp))
        exact Nat.mul_pos this this)) hbits
      exact (Nat.pow_le_pow_iff_right (by decide)).1 this
    refine (MEq.mod _ _).trans ?_
    rw [show fermat n - _ = 0 + fermat n - _ by rw [Nat.zero_add]]
    refine (neg_eq hF _ _ (Nat.le_of_lt (Nat.mod_lt _ hF₀))).trans ?_
    rw [Nat.zero_add]
    refine (MEq.mul ((MEq.mod _ _).trans (MEq.mul hV (MEq.refl _ _))) (MEq.refl _ _)).trans ?_
    rw [show 2 ^ k * Z.getD l 0 * 2 ^ (64 * n - k) = Z.getD l 0 * 2 ^ (64 * n) by
      rw [Nat.mul_comm (2 ^ k), Nat.mul_assoc, ← Nat.pow_add,
        show k + (64 * n - k) = 64 * n by lia]]
    exact pow_N_pow_N hF _
  -- Both are less than `F`.
  have hZl : Z.getD l 0 < fermat n := by
    have h₁ := getD_polyMul_le αL βL (X - 1) (X - 1) (fun a h => by have := hαX a h; lia)
      (fun b h => by have := hβX b h; lia) l
    rw [hZ] at h₁
    have h₂ : (X - 1) * (X - 1) < X * X ∨ X = 0 := by
      rcases Nat.eq_zero_or_pos X with e | e
      · exact .inr e
      · exact .inl (Nat.mul_lt_mul'' (by lia) (by lia))
    have h₃ : αL.length * ((X - 1) * (X - 1)) ≤ 2 ^ k * (X * X) := by
      rcases h₂ with h | h
      · exact Nat.mul_le_mul hαK (Nat.le_of_lt h)
      · subst h; simp
    simp only [fermat]
    lia
  rw [← Nat.mod_eq_of_lt hZl]
  exact (Nat.mod_mod _ _).symm.trans hc

/-! ## The multiplication -/

/--
`a b` into the first `a.size + b.size` limbs of `r`, with `K = 2ᵏ` windows of `n + 1` limbs for
the pieces of `m` limbs of each operand. The layout of the flat array: the block of `a` at `0`,
the block of `b` at `K (n + 1)`, the scratch window, and a zero window.
-/
public def fftMulAt (r a b : USlice) (k m n : Nat) : UInt64Array :=
  let K := 2 ^ k
  let oB := K * (n + 1)
  let t := 2 * K * (n + 1)
  let z := t + (n + 1)
  let σ := 2 * (64 * n) / K
  let FA := loadLoop 0 n m a (UInt64Array.replicate (z + (n + 1)) 0) 0 K
  let FA := loadLoop oB n m b FA 0 K
  let FA := fwd n t k FA 0 σ
  let FA := fwd n t k FA oB σ
  let FA := pointLoop n 0 oB FA (UInt64Array.replicate (2 * n + 2) 0) 0 K
  let FA := inv n t k FA 0 σ
  let FA := scaleLoop n 0 t z k FA 0 K
  recLoop (a.size.toNat + b.size.toNat) m n 0 FA
    (zeroInto (r.slice 0 (a.size + b.size))) r.start.toNat 0 K

/-- The parameters of `fftMulAt` for which it computes `a b`. -/
public structure FFTParams (r a b : USlice) (k m n : Nat) : Prop where
  hk : 1 ≤ k
  hn : 1 ≤ n
  hm : 1 ≤ m
  hmn : m ≤ n
  hdiv : 2 * (64 * n) % 2 ^ k = 0
  ha : 0 < a.size.toNat
  hb : 0 < b.size.toNat
  hpieces : (a.size.toNat + m - 1) / m + (b.size.toNat + m - 1) / m ≤ 2 ^ k + 1
  hbits : 2 ^ k * 2 ^ (128 * m) ≤ 2 ^ (64 * n)
  hr : a.size.toNat + b.size.toNat ≤ r.size.toNat
  hS : (2 * 2 ^ k + 2) * (n + 1) < USize.size
  h64 : 64 * n < USize.size
  haS : a.array.size < USize.size
  hbS : b.array.size < USize.size
  hrS : r.array.size < USize.size

public theorem piece_eq_zero (a : USlice) (m i : Nat) (h : a.size.toNat ≤ i * m) :
    piece a m i = 0 := by
  rw [piece, show a.size.toNat - i * m = 0 by lia, Nat.min_zero, valAt_zero]

/-- Enough pieces of `m` limbs to cover `x` limbs. -/
private theorem cover (x m : Nat) (hm : 1 ≤ m) : x ≤ (x + m - 1) / m * m := by
  have h₁ := Nat.div_add_mod (x + m - 1) m
  have h₂ := Nat.mod_lt (x + m - 1) (show 0 < m by lia)
  rw [Nat.mul_comm] at h₁
  lia

private theorem coef_pieces (a : USlice) (m L K i : Nat) (hL : a.size.toNat ≤ L * m) :
    (if i < K then piece a m i else 0) = (pieces a m L).getD i 0 ∨ K ≤ i := by
  rcases Nat.lt_or_ge i K with h | h
  · left
    rw [ite_eq_left h, getD_pieces]
    split
    · rfl
    · rename_i h'
      exact piece_eq_zero a m i (Nat.le_trans hL (Nat.mul_le_mul_right m (by lia)))
  · exact .inr h

set_option maxHeartbeats 800000 in
public theorem fftMulAt_spec (r a b : USlice) (k m n : Nat) (hp : FFTParams r a b k m n) :
    (fftMulAt r a b k m n).size = r.array.size ∧
      (∀ i, (i < r.start.toNat ∨ r.start.toNat + a.size.toNat + b.size.toNat ≤ i) →
        (fftMulAt r a b k m n)[i]! = r.array[i]!) ∧
      (fftMulAt r a b k m n).valAt r.start.toNat (a.size.toNat + b.size.toNat) =
        a.toNat * b.toNat := by
  obtain ⟨hk, hn, hm, hmn, hdiv, ha, hb, hpc, hbits, hr, hS, h64, haS, hbS, hrS⟩ := hp
  have hF₀ : 0 < fermat n := by simp [fermat]
  have hK1 : 2 ≤ 2 ^ k := by
    have := Nat.pow_le_pow_right (show 0 < 2 by decide) hk; simpa using this
  have hσ : 2 * (64 * n) / 2 ^ k * 2 ^ k = 2 * (64 * n) :=
    Nat.div_mul_cancel (Nat.dvd_of_mod_eq_zero hdiv)
  dsimp only [fftMulAt]
  generalize 2 * (64 * n) / 2 ^ k = σ at *
  -- The layout.
  have hw := Nat.mul_le_mul_right (n + 1) (show 2 ^ k ≤ 2 * 2 ^ k by lia)
  have hsz : (UInt64Array.replicate (2 * 2 ^ k * (n + 1) + (n + 1) + (n + 1)) 0).size =
      2 * 2 ^ k * (n + 1) + (n + 1) + (n + 1) := by simp
  have hSz : 2 * 2 ^ k * (n + 1) + (n + 1) + (n + 1) < USize.size := by
    rw [show 2 * 2 ^ k * (n + 1) + (n + 1) + (n + 1) = (2 * 2 ^ k + 2) * (n + 1) by
      rw [Nat.add_mul]; lia]
    exact hS
  have hBB : 2 ^ k * (n + 1) + 2 ^ k * (n + 1) = 2 * 2 ^ k * (n + 1) := by rw [Nat.mul_assoc]; lia
  generalize hS₀ : 2 * 2 ^ k * (n + 1) + (n + 1) + (n + 1) = S at *
  -- Loading `a`.
  obtain ⟨l₁, l₂, l₃⟩ := loadLoop_spec 0 n m a (by lia) haS (2 ^ k)
    (UInt64Array.replicate S 0) 0 (by rw [hsz]; exact hSz) (by rw [hsz]; lia)
    (fun p _ _ => valAt_replicate_zero ..)
  generalize loadLoop 0 n m a (UInt64Array.replicate S 0) 0 (2 ^ k) = A₁ at *
  rw [hsz] at l₁
  -- Loading `b`.
  obtain ⟨m₁, m₂, m₃⟩ := loadLoop_spec (2 ^ k * (n + 1)) n m b (by lia) hbS (2 ^ k) A₁ 0
    (by rw [l₁]; exact hSz) (by rw [l₁]; lia) (fun p _ hp => by
      have := win_in (2 ^ k * (n + 1)) n p (2 ^ k) (by lia)
      show win A₁ n _ = 0
      rw [win_congr fun j _ _ => l₂ j (by lia)]
      exact valAt_replicate_zero ..)
  generalize loadLoop (2 ^ k * (n + 1)) n m b A₁ 0 (2 ^ k) = A₂ at *
  rw [l₁] at m₁
  have cA : ∀ p < 2 ^ k, coef A₂ n 0 p = piece a m p := by
    intro p hp
    have := win_in 0 n p (2 ^ k) hp
    rw [← l₃ p (by lia) (by lia)]
    exact win_congr fun j _ _ => m₂ j (by lia)
  have cB : ∀ p < 2 ^ k, coef A₂ n (2 ^ k * (n + 1)) p = piece b m p :=
    fun p hp => m₃ p (by lia) (by lia)
  have hXF : 2 ^ (64 * m) < fermat n := by
    simp only [fermat]
    have : 2 ^ (64 * m) ≤ 2 ^ (64 * n) := Nat.pow_le_pow_right (by decide) (by lia)
    lia
  -- The forward transforms.
  obtain ⟨f₁, f₂, f₃⟩ := fwd_spec n (2 * 2 ^ k * (n + 1)) hn h64 k A₂ 0 σ hσ
    ⟨by rw [m₁]; exact hSz, by rw [m₁]; lia, by rw [m₁]; lia, by lia⟩
    (fun p hp => by rw [cA p hp]; exact Nat.lt_trans (piece_lt ..) hXF)
  generalize fwd n (2 * 2 ^ k * (n + 1)) k A₂ 0 σ = A₃ at *
  have cB₃ : ∀ p < 2 ^ k, coef A₃ n (2 ^ k * (n + 1)) p = piece b m p := by
    intro p hp
    have := win_in (2 ^ k * (n + 1)) n p (2 ^ k) hp
    rw [← cB p hp]
    exact win_congr fun j _ _ => f₂ j (by lia) (by lia)
  obtain ⟨g₁, g₂, g₃⟩ := fwd_spec n (2 * 2 ^ k * (n + 1)) hn h64 k A₃ (2 ^ k * (n + 1)) σ hσ
    ⟨by rw [f₁, m₁]; exact hSz, by rw [f₁, m₁]; lia, by rw [f₁, m₁]; lia, by lia⟩
    (fun p hp => by rw [cB₃ p hp]; exact Nat.lt_trans (piece_lt ..) hXF)
  generalize fwd n (2 * 2 ^ k * (n + 1)) k A₃ (2 ^ k * (n + 1)) σ = A₄ at *
  have cA₄ : ∀ p < 2 ^ k, coef A₄ n 0 p = coef A₃ n 0 p := by
    intro p hp
    have := win_in 0 n p (2 ^ k) hp
    exact win_congr fun j _ _ => g₂ j (by lia) (by lia)
  -- The pointwise products.
  obtain ⟨p₁, p₂, p₃⟩ := pointLoop_spec n 0 (2 ^ k * (n + 1)) hn (2 ^ k) A₄
    (UInt64Array.replicate (2 * n + 2) 0) 0 (by simp) (by simp; lia) (by rw [g₁, f₁, m₁]; exact hSz)
    (by lia) (by rw [g₁, f₁, m₁]; lia) (fun q _ hq => by
      rw [cA₄ q (by lia), f₃ q (by lia), g₃ q (by lia)]
      exact ⟨Nat.mod_lt _ hF₀, Nat.mod_lt _ hF₀⟩)
  generalize pointLoop n 0 (2 ^ k * (n + 1)) A₄ (UInt64Array.replicate (2 * n + 2) 0) 0 (2 ^ k) =
    A₅ at *
  -- The inverse transform.
  obtain ⟨v₁, v₂, v₃⟩ := inv_spec n (2 * 2 ^ k * (n + 1)) hn h64 k A₅ 0 σ hσ
    ⟨by rw [p₁, g₁, f₁, m₁]; exact hSz, by rw [p₁, g₁, f₁, m₁]; lia, by rw [p₁, g₁, f₁, m₁]; lia,
      by lia⟩ (fun q hq => by rw [p₃ q (by lia) (by lia)]; exact Nat.mod_lt _ hF₀)
  generalize inv n (2 * 2 ^ k * (n + 1)) k A₅ 0 σ = A₆ at *
  -- The zero window is untouched.
  have hz : win A₆ n (2 * 2 ^ k * (n + 1) + (n + 1)) = 0 := by
    have : win A₆ n (2 * 2 ^ k * (n + 1) + (n + 1)) =
        win (UInt64Array.replicate S 0) n (2 * 2 ^ k * (n + 1) + (n + 1)) :=
      win_congr fun j _ _ => by
        rw [v₂ j (by lia) (by lia), p₂ j (by lia), g₂ j (by lia) (by lia), f₂ j (by lia) (by lia),
          m₂ j (by lia), l₂ j (by lia)]
    rw [this]
    exact valAt_replicate_zero ..
  -- The division by `2ᵏ`.
  have hsz₆ : A₆.size = S := by rw [v₁, p₁, g₁, f₁, m₁]
  obtain ⟨s₁, -, s₃⟩ := scaleLoop_spec n 0 (2 * 2 ^ k * (n + 1)) (2 * 2 ^ k * (n + 1) + (n + 1)) k
    hn hk h64 (2 ^ k) A₆ 0 (by rw [hsz₆]; exact hSz) (by rw [hsz₆]; lia) (by rw [hsz₆]; lia)
    (by rw [hsz₆]; lia) (by lia) (by lia) (by lia) hz
    (fun q _ hq => by rw [v₃ q (by lia)]; exact Nat.mod_lt _ hF₀)
  generalize scaleLoop n 0 (2 * 2 ^ k * (n + 1)) (2 * 2 ^ k * (n + 1) + (n + 1)) k A₆ 0 (2 ^ k) =
    A₇ at *
  -- The coefficients are those of the product of the pieces.
  have hla := cover a.size.toNat m hm
  have hlb := cover b.size.toNat m hm
  have hla₁ : 1 ≤ (a.size.toNat + m - 1) / m := (Nat.le_div_iff_mul_le (by lia)).2 (by lia)
  have hlb₁ : 1 ≤ (b.size.toNat + m - 1) / m := (Nat.le_div_iff_mul_le (by lia)).2 (by lia)
  generalize (a.size.toNat + m - 1) / m = la at *
  generalize (b.size.toNat + m - 1) / m = lb at *
  have hαL : ∀ i < 2 ^ k, coef A₂ n 0 i = (pieces a m la).getD i 0 := fun i hi => by
    rw [cA i hi]
    rcases coef_pieces a m la (2 ^ k) i hla with h | h
    · rw [← h, ite_eq_left hi]
    · lia
  have hβL : ∀ i < 2 ^ k, coef A₂ n (2 ^ k * (n + 1)) i = (pieces b m lb).getD i 0 :=
    fun i hi => by
      rw [cB i hi]
      rcases coef_pieces b m lb (2 ^ k) i hlb with h | h
      · rw [← h, ite_eq_left hi]
      · lia
  have hβne : pieces b m lb ≠ [] := by
    intro h; have := congrArg List.length h; rw [length_pieces] at this; simp at this; lia
  have hc : ∀ l < 2 ^ k, coef A₇ n 0 l = (polyMul (pieces a m la) (pieces b m lb)).getD l 0 := by
    intro l hl
    rw [s₃ l (by lia) (by lia), v₃ l hl]
    rw [← fft_coef (pieces a m la) (pieces b m lb) k n σ (2 ^ (64 * m)) hk hσ
      (by rw [length_pieces, length_pieces]; lia) hβne
      (fun x hx => by
        simp only [pieces, List.mem_map, List.mem_range] at hx
        obtain ⟨i, -, rfl⟩ := hx; exact piece_lt ..)
      (fun x hx => by
        simp only [pieces, List.mem_map, List.mem_range] at hx
        obtain ⟨i, -, rfl⟩ := hx; exact piece_lt ..)
      (by rw [← Nat.pow_add, show 64 * m + 64 * m = 128 * m by lia]; exact hbits)
      (by rw [length_pieces]; lia) (by rw [length_pieces]; lia) l hl]
    have hα : ∀ q, sumRange (fun i => coef A₂ n 0 i * 2 ^ (σ * i * rev k q)) (2 ^ k) =
        sumRange (fun i => (pieces a m la).getD i 0 * 2 ^ (σ * i * rev k q)) (2 ^ k) :=
      fun q => sumRange_congr fun i hi => by rw [hαL i hi]
    have hβ : ∀ q, sumRange (fun i => coef A₃ n (2 ^ k * (n + 1)) i * 2 ^ (σ * i * rev k q))
        (2 ^ k) = sumRange (fun i => (pieces b m lb).getD i 0 * 2 ^ (σ * i * rev k q)) (2 ^ k) :=
      fun q => sumRange_congr fun i hi => by rw [cB₃ i hi, ← cB i hi, hβL i hi]
    have hsum : sumRange (fun p => coef A₅ n 0 p * 2 ^ ((2 * (64 * n) - σ) * rev k p * l))
        (2 ^ k) = sumRange (fun p =>
          sumRange (fun i => (pieces a m la).getD i 0 * 2 ^ (σ * i * rev k p)) (2 ^ k) %
            fermat n * (sumRange (fun i => (pieces b m lb).getD i 0 * 2 ^ (σ * i * rev k p))
              (2 ^ k) % fermat n) % fermat n * 2 ^ ((2 * (64 * n) - σ) * rev k p * l)) (2 ^ k) :=
      sumRange_congr fun q hq => by
        rw [p₃ q (by lia) (by lia), cA₄ q hq, f₃ q hq, g₃ q hq, hα, hβ]
    rw [hsum]
  -- The value of the coefficients at `2^(64 m)`.
  generalize hZ : polyMul (pieces a m la) (pieces b m lb) = Z at hc
  have hZK : Z.length ≤ 2 ^ k := by
    rw [← hZ]; have := length_polyMul (pieces a m la) (pieces b m lb) hβne
    rw [length_pieces, length_pieces] at this; lia
  have hab : sumRange (fun i => 2 ^ (64 * ((0 + i) * m)) * coef A₇ n 0 (0 + i)) (2 ^ k) =
      a.toNat * b.toNat := by
    rw [← polyVal_pieces a m la hla, ← polyVal_pieces b m lb hlb, ← polyVal_polyMul, hZ,
      polyVal_eq_sumRange _ Z _ hZK]
    exact sumRange_congr fun i hi => by
      rw [Nat.zero_add, hc i hi, Nat.mul_comm, ← Nat.pow_mul]; congr 2; lia
  have hablt : a.toNat * b.toNat < 2 ^ (64 * (a.size.toNat + b.size.toNat)) := by
    rw [Nat.mul_add, Nat.pow_add]
    have h₁ : a.toNat < 2 ^ (64 * a.size.toNat) := by rw [USlice.toNat_eq_valAt]; exact valAt_lt ..
    have h₂ : b.toNat < 2 ^ (64 * b.size.toNat) := by rw [USlice.toNat_eq_valAt]; exact valAt_lt ..
    exact Nat.mul_lt_mul'' h₁ h₂
  -- Zeroing the result, and adding the coefficients.
  have hT : (a.size + b.size).toNat = a.size.toNat + b.size.toNat :=
    USize.toNat_add_of_lt (by have := r.size.toNat_lt_size; lia)
  have hrs := r.toNat_size
  have hrst := r.stop_le_size
  have hrle := USize.le_iff_toNat_le.1 r.start_le_stop
  have e₁ := r.start_slice (i := 0) (j := a.size + b.size) (by simp) (by rw [hT]; exact hr)
  have e₂ := r.size_slice (i := 0) (j := a.size + b.size) (by simp) (by rw [hT]; exact hr)
  rw [USize.toNat_zero, Nat.add_zero] at e₁
  rw [USize.toNat_zero, Nat.sub_zero, hT] at e₂
  obtain ⟨z₁, z₂, z₃⟩ := zeroInto_spec (r.slice 0 (a.size + b.size))
  simp only [USlice.array_slice, e₁, e₂] at z₁ z₂ z₃
  generalize zeroInto (r.slice 0 (a.size + b.size)) = R₀ at *
  have hsz₇ : A₇.size = S := by rw [s₁, hsz₆]
  obtain ⟨c₁, c₂, c₃⟩ := recLoop_spec (a.size.toNat + b.size.toNat) m n 0 A₇
    (by rw [hsz₇]; exact hSz) (2 ^ k) R₀ r.start.toNat 0 (by rw [z₁]; exact hrS) (by rw [z₁]; lia)
    (by rw [hsz₇]; lia) (by rw [z₃, Nat.zero_add, hab]; exact hablt)
  refine ⟨by rw [c₁, z₁], fun i hi => ?_, ?_⟩
  · rw [c₂ i (by lia), z₂ i (by lia)]
  · rw [c₃, z₃, Nat.zero_add, hab]

/-! ## The parameters -/

/--
The parameters for `T` limbs and `K = 2ᵏ` pieces: pieces of `m = ⌈T / (K - 1)⌉` limbs, so that
the two operands have at most `K + 1`, and residues of `n` limbs, `2 m + 1` rounded up to a
multiple of `K / 128`, so that the root `2^(128 n / K)` is a power of two.
-/
public def fftParams (T k : Nat) : Nat × Nat :=
  let m := (T + 2 ^ k - 2) / (2 ^ k - 1)
  let q := max 1 (2 ^ k / 128)
  (m, (2 * m + 1 + q - 1) / q * q)

/--
The number of pieces, `2ᵏ`, for `T` limbs: the least `k` with `4ᵏ ≥ 10 T`. From a sweep of
`k = 4, …, 11` at 1024 to 65536 limbs per operand (Zen 3, 2026-10-23): the best `K = 2ᵏ` has
`K² / T` between 8 and 32, and this choice is within 6% of the best at every size measured.
-/
public def fftK (T : Nat) : Nat := min 30 ((Nat.log2 (10 * T - 1) + 2) / 2)

/-- The conditions of `FFTParams`, decidably, with `k + 128 m ≤ 64 n` for the bound. -/
public abbrev FFTCheck (r a b : USlice) (k m n : Nat) : Prop :=
  1 ≤ k ∧ k ≤ 64 ∧ 1 ≤ n ∧ 1 ≤ m ∧ m ≤ n ∧ 2 * (64 * n) % 2 ^ k = 0 ∧ 0 < a.size.toNat ∧
    0 < b.size.toNat ∧ (a.size.toNat + m - 1) / m + (b.size.toNat + m - 1) / m ≤ 2 ^ k + 1 ∧
    k + 128 * m ≤ 64 * n ∧ a.size.toNat + b.size.toNat ≤ r.size.toNat ∧
    (2 * 2 ^ k + 2) * (n + 1) < USize.size ∧ 64 * n < USize.size ∧
    a.array.size < USize.size ∧ b.array.size < USize.size ∧ r.array.size < USize.size

private theorem FFTCheck.params {r a b : USlice} {k m n : Nat} (h : FFTCheck r a b k m n) :
    FFTParams r a b k m n := by
  obtain ⟨h₁, h₂, h₃, h₄, h₅, h₆, h₇, h₈, h₉, h₁₀, h₁₁, h₁₂, h₁₃, h₁₄, h₁₅, h₁₆⟩ := h
  exact ⟨h₁, h₃, h₄, h₅, h₆, h₇, h₈, h₉,
    by rw [← Nat.pow_add]; exact Nat.pow_le_pow_right (by decide) (by lia), h₁₁, h₁₂, h₁₃, h₁₄,
    h₁₅, h₁₆⟩

/--
Writes the `a.size + b.size` limbs of `a b` into `r`, by the FFT with `2ᵏ` pieces, or by
`mulToom` when the parameters of `fftParams` do not suit the sizes.
-/
public def fftMul (r a b : USlice) (k : Nat) : UInt64Array :=
  let p := fftParams (a.size.toNat + b.size.toNat) k
  if FFTCheck r a b k p.1 p.2 then fftMulAt r a b k p.1 p.2 else mulToom r a b

private theorem fftMul_spec (r a b : USlice) (k : Nat) :
    (fftMul r a b k).size = r.array.size ∧
      (∀ i, (i < r.start.toNat ∨ r.start.toNat + a.size.toNat + b.size.toNat ≤ i) →
        (fftMul r a b k)[i]! = r.array[i]!) ∧
      (0 < a.size → 0 < b.size → a.size.toNat + b.size.toNat ≤ r.size.toNat →
        (fftMul r a b k).valAt r.start.toNat (a.size.toNat + b.size.toNat) =
          a.toNat * b.toNat) := by
  rw [fftMul]
  split
  · rename_i h
    obtain ⟨s₁, s₂, s₃⟩ := fftMulAt_spec r a b k _ _ h.params
    exact ⟨s₁, s₂, fun _ _ _ => s₃⟩
  · exact ⟨size_mulToom r a b, getElem!_mulToom r a b, valAt_mulToom r a b⟩

@[simp] public theorem size_fftMul (r a b : USlice) (k : Nat) :
    (fftMul r a b k).size = r.array.size :=
  (fftMul_spec r a b k).1

/-- `fftMul` leaves the limbs of `r` outside the ones it writes unchanged. -/
public theorem getElem!_fftMul (r a b : USlice) (k : Nat) (i : Nat)
    (hi : i < r.start.toNat ∨ r.start.toNat + a.size.toNat + b.size.toNat ≤ i) :
    (fftMul r a b k)[i]! = r.array[i]! :=
  (fftMul_spec r a b k).2.1 i hi

public theorem valAt_fftMul (r a b : USlice) (k : Nat) (ha : 0 < a.size) (hb : 0 < b.size)
    (hr : a.size.toNat + b.size.toNat ≤ r.size.toNat) :
    (fftMul r a b k).valAt r.start.toNat (a.size.toNat + b.size.toNat) = a.toNat * b.toNat :=
  (fftMul_spec r a b k).2.2 ha hb hr

end MPN.FFT

namespace MPN

open FFT

/-- The total size, in limbs, from which `mul` uses the FFT, measured on Zen 3 (2026-10-23). -/
public def fftThreshold : Nat := 5120

/-- The size of the smaller operand below which `mul` does not use the FFT. -/
public def fftMinSmall : Nat := 512

/--
Writes the `a.size + b.size` limbs of `a b` into `r`: by `fftMul` from `fftThreshold` limbs in
all when the smaller operand has `fftMinSmall` limbs, by `mulToom` otherwise, which uses Toom-3,
Toom-3 by 2, Toom-4 by 2, Karatsuba and the schoolbook method by the sizes. It requires
`0 < a.size`, `0 < b.size` and `a.size + b.size ≤ r.size`.
-/
public def mul (r a b : USlice) : UInt64Array :=
  if fftThreshold ≤ a.size.toNat + b.size.toNat ∧ fftMinSmall ≤ min a.size.toNat b.size.toNat then
    fftMul r a b (fftK (a.size.toNat + b.size.toNat))
  else mulToom r a b

@[simp] public theorem size_mul (r a b : USlice) : (mul r a b).size = r.array.size := by
  rw [mul]; split <;> simp

/-- `mul` leaves the limbs of `r` outside the ones it writes unchanged. -/
public theorem getElem!_mul (r a b : USlice) (i : Nat)
    (hi : i < r.start.toNat ∨ r.start.toNat + a.size.toNat + b.size.toNat ≤ i) :
    (mul r a b)[i]! = r.array[i]! := by
  rw [mul]; split
  · exact getElem!_fftMul r a b _ i hi
  · exact getElem!_mulToom r a b i hi

public theorem valAt_mul (r a b : USlice) (ha : 0 < a.size) (hb : 0 < b.size)
    (hr : a.size.toNat + b.size.toNat ≤ r.size.toNat) :
    (mul r a b).valAt r.start.toNat (a.size.toNat + b.size.toNat) = a.toNat * b.toNat := by
  rw [mul]; split
  · exact valAt_fftMul r a b _ ha hb hr
  · exact valAt_mulToom r a b ha hb hr

end MPN
