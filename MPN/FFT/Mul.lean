/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import MPN.FFT.Transform
public import MPN.FFT.Roots
public import MPN.Poly
public import MPN.FFT.Algebra
public import MPN.Basic
public import MPN.Mul.Basecase

/-!
# FFT multiplication

Schönhage–Strassen multiplication of `a` by `b` on one flat array: their pieces of `m` limbs are
loaded into two blocks of `K = 2ᵏ` windows of `n + 1` limbs, transformed modulo `F = 2^(32 n) + 1`
with the root `2^σ`, `σ = 64 n / K`, multiplied pointwise, by a callback (the dispatcher's
`mulLimbsWith`) and a reduction modulo `F`, and transformed back. Divided by `K`, the windows are
the coefficients of the product of the polynomials of the pieces, which are less than `F` when
`K 2^(64 m) ≤ 2^(32 n)`, so they are exact; their sum at `2^(32 m)` is `a b`.

The design and the proofs are `main64`'s, on 32-bit limbs. `fftMul` and `fftSqr` at the end take
the library's slices and `MPN.toNat`, as the dispatcher does.
-/

open ScalarArray UInt32Array MPN.U

namespace MPN.FFT


/-! ## Slices at `Nat` offsets -/

/-- The limbs `o` to `o + len - 1` of `arr`. -/
public def sl (arr : UInt32Array) (o len : Nat) : USlice := arr.uslice o.toUSize (o + len).toUSize

public theorem sl_spec (arr : UInt32Array) (o len : Nat) (h : o + len ≤ arr.size)
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

public theorem piece_lt (a : USlice) (m i : Nat) : piece a m i < 2 ^ (32 * m) :=
  Nat.lt_of_lt_of_le (valAt_lt ..) (Nat.pow_le_pow_right (by decide) (by lia))

private theorem polyVal_pieces_from (a : USlice) (m : Nat) (L : Nat) :
    ∀ i, polyVal (2 ^ (32 * m)) ((List.range L).map fun j => piece a m (i + j)) =
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
          by rw [Nat.add_mul]; lia, UInt32Array.valAt_add,
        show a.start.toNat + i * m + m = a.start.toNat + (i + 1) * m by rw [Nat.add_mul]; lia]

/-- The pieces of `a` are its digits in base `2^(32 m)`. -/
public theorem polyVal_pieces (a : USlice) (m L : Nat) (hL : a.size.toNat ≤ L * m) :
    polyVal (2 ^ (32 * m)) (pieces a m L) = a.toNat := by
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
public def addAt (arr : UInt32Array) (o len : Nat) (b : USlice) : UInt32Array × UInt32 :=
  addInto (sl arr o len) b 0

public theorem addAt_spec (arr : UInt32Array) (o len : Nat) (b : USlice) (h : o + len ≤ arr.size)
    (hS : arr.size < USize.size) (hb : b.size.toNat ≤ len) :
    (addAt arr o len b).1.size = arr.size ∧
      (∀ i, (i < o ∨ o + len ≤ i) → (addAt arr o len b).1[i]! = arr[i]!) ∧
      (addAt arr o len b).1.valAt o len + 2 ^ (32 * len) * (addAt arr o len b).2.toNat =
        arr.valAt o len + b.toNat := by
  obtain ⟨s₁, s₂, s₃, s₄⟩ := sl_spec arr o len h hS
  have hb' : b.size ≤ (sl arr o len).size := USize.le_iff_toNat_le.2 (by rw [s₃]; exact hb)
  refine ⟨by rw [addAt, size_addInto, s₁], fun i hi => ?_, ?_⟩
  · rw [addAt, getElem!_addInto _ _ _ i (by rw [s₂, s₃]; exact hi), s₁]
  · have := valAt_addInto (sl arr o len) b 0 hb'
    rw [s₂, s₃, s₁, UInt32.toNat_zero, Nat.add_zero] at this
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
public def loadLoop (o n m : Nat) (a : USlice) : UInt32Array → Nat → Nat → UInt32Array
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
      have hX : 2 ^ (32 * m) ≤ 2 ^ (32 * (n + 1)) := Nat.pow_le_pow_right (by decide) (by lia)
      have hc : q.2.toNat = 0 := by
        rcases Nat.eq_zero_or_pos q.2.toNat with e | e
        · exact e
        · have := Nat.mul_le_mul_left (2 ^ (32 * (n + 1))) e
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
public def normG (arr : UInt32Array) (n d : Nat) : UInt32Array :=
  if h : Win arr n.toUSize d.toUSize then normAt arr n.toUSize d.toUSize h else arr

public theorem normG_spec (arr : UInt32Array) (n d : Nat) (hS : arr.size < USize.size)
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
public def reduceAt (arr : UInt32Array) (n d : Nat) (P : UInt32Array) : UInt32Array :=
  let q := subN (sl arr d n) (sl P 0 n) (sl P n n) 0
  -- The carry first, so that the pair is dead when the array is written.
  let c := q.2 + P[2 * n]!
  let a := q.1
  let a := if h : (d + n).toUSize.toNat < a.size then a.uset (d + n).toUSize 0 h else a
  let a := if h : LoopBound a d.toUSize (n + 1).toUSize
    then (incrAt a d.toUSize (n + 1).toUSize h 0 c).1 else a
  normG a n d

set_option maxHeartbeats 400000 in
public theorem reduceAt_spec (arr : UInt32Array) (n d : Nat) (P : UInt32Array)
    (hS : arr.size < USize.size) (hd : d + n + 1 ≤ arr.size) (hn : 1 ≤ n)
    (hP : P.size = 2 * n + 2) (hPS : P.size < USize.size)
    (hPv : P.valAt 0 (2 * n + 2) ≤ 2 ^ (32 * n) * 2 ^ (32 * n)) :
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
  simp only [r₂, r₃, a₁, a₂, a₃, b₁, b₂, b₃, Nat.min_self, UInt32.toNat_zero, Nat.add_zero,
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
    simp only [hdn, ↓reduceIte, UInt32.toNat_zero, Nat.mul_zero, Nat.add_zero]
  have hlb : LoopBound (q.1.uset (d + n).toUSize 0 hidx) d.toUSize (n + 1).toUSize := by
    constructor <;> simp only [size_uset, hd', hn1, hs₁] <;> lia
  rw [dite_eq_left hlb]
  -- The increment by the borrow and `P_hi`.
  have hP₃ := valAt_lt P 0 n
  have hP₄ := valAt_lt P n n
  have hPv' : P.valAt 0 (2 * n + 2) = P.valAt 0 n + 2 ^ (32 * n) * P.valAt n n +
      2 ^ (32 * n) * 2 ^ (32 * n) * (P[2 * n]!.toNat + 2 ^ 32 * P[2 * n + 1]!.toNat) := by
    have e₁ := UInt32Array.valAt_add P 0 n (n + 2)
    have e₂ := UInt32Array.valAt_add P n n 2
    have e₃ := valAt_succ P (n + n) 1
    have e₄ := valAt_one P (n + n + 1)
    rw [show n + (n + 2) = 2 * n + 2 by lia, Nat.zero_add] at e₁
    rw [e₂, e₃, e₄, show n + n = 2 * n by lia] at e₁
    rw [e₁]
    grind
  have hB : 1 ≤ 2 ^ (32 * n) := Nat.one_le_two_pow
  have hhi : P[2 * n]!.toNat + 2 ^ 32 * P[2 * n + 1]!.toNat ≤ 1 := by
    rcases Nat.lt_or_ge (P[2 * n]!.toNat + 2 ^ 32 * P[2 * n + 1]!.toNat) 2 with e | e
    · lia
    · have := Nat.mul_le_mul_left (2 ^ (32 * n) * 2 ^ (32 * n)) e
      have : 1 ≤ 2 ^ (32 * n) * 2 ^ (32 * n) := Nat.mul_le_mul hB hB
      lia
  have hP₁ : P[2 * n + 1]!.toNat = 0 := by
    rcases Nat.eq_zero_or_pos P[2 * n + 1]!.toNat with e | e
    · exact e
    · have := Nat.mul_le_mul_left (2 ^ 32) e; lia
  simp only [hP₁, Nat.mul_zero, Nat.add_zero] at hPv' hhi
  have hc₁ : q.2.toNat ≤ 1 := by
    rcases Nat.lt_or_ge q.2.toNat 2 with e | e
    · lia
    · have := Nat.mul_le_mul_left (2 ^ (32 * n)) e
      have := valAt_lt q.1 d n
      lia
  have hc : (q.2 + P[2 * n]!).toNat = q.2.toNat + P[2 * n]!.toNat := by
    rw [UInt32.toNat_add, Nat.mod_eq_of_lt (by lia)]
  obtain ⟨i₁, i₂, i₃⟩ := incrAt_spec _ d.toUSize (n + 1).toUSize hlb 0 (q.2 + P[2 * n]!)
  simp only [USize.toNat_zero, Nat.add_zero, Nat.sub_zero, hd', hn1, size_uset] at i₁ i₂ i₃
  rw [t₁, hc] at i₃
  generalize incrAt _ d.toUSize (n + 1).toUSize hlb 0 (q.2 + P[2 * n]!) = q' at *
  -- No carry out of the window.
  have hq' := valAt_lt q.1 d n
  have hB1 : 2 ^ (32 * (n + 1)) = 2 ^ (32 * n) * 2 ^ 32 := by rw [Nat.mul_succ, Nat.pow_add]
  have hc' : q'.2.toNat = 0 := by
    rcases Nat.eq_zero_or_pos q'.2.toNat with e | e
    · exact e
    · have := Nat.mul_le_mul_left (2 ^ (32 * (n + 1))) e
      rw [hB1] at this
      have : 2 ^ (32 * n) * 2 ≤ 2 ^ (32 * n) * 2 ^ 32 := Nat.mul_le_mul_left _ (by decide)
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
    generalize 2 ^ (32 * n) = Bn at *
    rw [reduce_eq hs₂ hc₁ hhi hq', Nat.add_mul_mod_self_left]

/-- A multiplication of slices of fewer than `N` limbs together, into a new array. -/
public abbrev MulN (N : Nat) : Type :=
  (x y : USlice) → x.size.toNat + y.size.toNat < N → UInt32Array

/-- `mul` multiplies: a new array of `x.size + y.size` limbs with the value `x y`. -/
public def IsMulN {N : Nat} (mul : MulN N) : Prop :=
  ∀ x y h, (mul x y h).size = x.size.toNat + y.size.toNat ∧
    (mul x y h).valAt 0 (x.size.toNat + y.size.toNat) = x.toNat * y.toNat

/-- A squaring of a slice of fewer than `N` limbs, into a new array. -/
public abbrev SqrN (N : Nat) : Type := (x : USlice) → x.size.toNat < N → UInt32Array

/-- `sqr` squares: a new array of `2 x.size` limbs with the value `x²`. -/
public def IsSqrN {N : Nat} (sqr : SqrN N) : Prop :=
  ∀ x h, (sqr x h).size = 2 * x.size.toNat ∧
    (sqr x h).valAt 0 (2 * x.size.toNat) = x.toNat * x.toNat

/--
The pointwise products of windows `p` to `p + cnt - 1` of the blocks at `oA` and `oB`, into the
first, by `mul` into a new array of `2 n + 2` limbs each.
-/
public def pointLoop (n oA oB N : Nat) (mul : MulN N) :
    UInt32Array → Nat → Nat → UInt32Array
  | arr, _, 0 => arr
  | arr, p, cnt + 1 =>
    let x := sl arr (oA + p * (n + 1)) (n + 1)
    let y := sl arr (oB + p * (n + 1)) (n + 1)
    let P := if h : x.size.toNat + y.size.toNat < N then mul x y h
      else UInt32Array.replicate (2 * n + 2) 0
    pointLoop n oA oB N mul (reduceAt arr n (oA + p * (n + 1)) P) (p + 1) cnt

public theorem pointLoop_spec (n oA oB N : Nat) (mul : MulN N) (hmul : IsMulN mul)
    (hN : 2 * n + 2 < N) (hn : 1 ≤ n) (cnt : Nat) :
    ∀ arr p, arr.size < USize.size →
      oA + (p + cnt) * (n + 1) ≤ oB → oB + (p + cnt) * (n + 1) ≤ arr.size →
      (∀ q, p ≤ q → q < p + cnt → coef arr n oA q < fermat n ∧ coef arr n oB q < fermat n) →
      (pointLoop n oA oB N mul arr p cnt).size = arr.size ∧
      (∀ j, (j < oA + p * (n + 1) ∨ oA + (p + cnt) * (n + 1) ≤ j) →
        (pointLoop n oA oB N mul arr p cnt)[j]! = arr[j]!) ∧
      (∀ q, p ≤ q → q < p + cnt →
        coef (pointLoop n oA oB N mul arr p cnt) n oA q =
          coef arr n oA q * coef arr n oB q % fermat n) := by
  induction cnt with
  | zero =>
    intro arr p _ _ _ _
    exact ⟨rfl, fun _ _ => rfl, fun q h₁ h₂ => absurd h₂ (by lia)⟩
  | succ cnt ih =>
    intro arr p hS hAB hB hv
    have hw := Nat.mul_le_mul_right (n + 1) (show p + 1 ≤ p + (cnt + 1) by lia)
    rw [Nat.add_mul, Nat.one_mul] at hw
    obtain ⟨x₁, x₂, x₃, x₄⟩ := sl_spec arr (oA + p * (n + 1)) (n + 1) (by lia) hS
    obtain ⟨y₁, y₂, y₃, y₄⟩ := sl_spec arr (oB + p * (n + 1)) (n + 1) (by lia) hS
    have hxy : (sl arr (oA + p * (n + 1)) (n + 1)).size.toNat +
        (sl arr (oB + p * (n + 1)) (n + 1)).size.toNat < N := by rw [x₃, y₃]; lia
    obtain ⟨m₁, m₂⟩ := hmul _ _ hxy
    rw [x₃, y₃, x₄, y₄, show n + 1 + (n + 1) = 2 * n + 2 by lia] at m₂
    rw [x₃, y₃, show n + 1 + (n + 1) = 2 * n + 2 by lia] at m₁
    rw [pointLoop, dite_eq_left hxy]
    generalize mul (sl arr (oA + p * (n + 1)) (n + 1)) (sl arr (oB + p * (n + 1)) (n + 1)) hxy
      = P' at *
    obtain ⟨hvA, hvB⟩ := hv p (Nat.le_refl _) (by lia)
    simp only [coef, win, fermat] at hvA hvB
    obtain ⟨r₁, r₂, r₃⟩ := reduceAt_spec arr n (oA + p * (n + 1)) P' hS (by lia) hn m₁
      (by rw [m₁]; lia) (by rw [m₂]; exact Nat.mul_le_mul (by lia) (by lia))
    generalize reduceAt arr n (oA + p * (n + 1)) P' = a₁ at *
    have hu : ∀ q, p + 1 ≤ q → q < p + (cnt + 1) →
        coef a₁ n oA q = coef arr n oA q ∧ coef a₁ n oB q = coef arr n oB q := by
      intro q h₁ h₂
      have d := Nat.mul_le_mul_right (n + 1) h₁
      have d' := Nat.mul_le_mul_right (n + 1) (show q + 1 ≤ p + (cnt + 1) by lia)
      rw [Nat.add_mul, Nat.one_mul] at d d'
      exact ⟨win_congr fun j _ _ => r₂ j (by lia), win_congr fun j _ _ => r₂ j (by lia)⟩
    obtain ⟨i₁, i₂, i₃⟩ := ih a₁ (p + 1) (by rw [r₁]; exact hS) (by lia) (by rw [r₁]; lia)
      fun q h₁ h₂ => by
        rw [(hu q h₁ (by lia)).1, (hu q h₁ (by lia)).2]; exact hv q (by lia) (by lia)
    refine ⟨i₁.trans r₁, fun j hj => ?_, fun q h₁ h₂ => ?_⟩
    · rw [i₂ j (by rw [Nat.add_mul, Nat.one_mul]; lia), r₂ j (by lia)]
    · by_cases e : q = p
      · subst e
        have : coef (pointLoop n oA oB N mul a₁ (q + 1) cnt) n oA q = coef a₁ n oA q :=
          win_congr fun j _ _ => i₂ j (by lia)
        rw [this]
        exact r₃.trans (by rw [m₂])
      · rw [i₃ q (by lia) (by lia), (hu q (by lia) h₂).1, (hu q (by lia) h₂).2]

/--
The pointwise squares of windows `p` to `p + cnt - 1` of the block at `oA`, by `sqr` into a new
array of `2 n + 2` limbs each.
-/
public def pointSqrLoop (n oA N : Nat) (sqr : SqrN N) :
    UInt32Array → Nat → Nat → UInt32Array
  | arr, _, 0 => arr
  | arr, p, cnt + 1 =>
    let x := sl arr (oA + p * (n + 1)) (n + 1)
    let P := if h : x.size.toNat < N then sqr x h else UInt32Array.replicate (2 * n + 2) 0
    pointSqrLoop n oA N sqr (reduceAt arr n (oA + p * (n + 1)) P) (p + 1) cnt

public theorem pointSqrLoop_spec (n oA N : Nat) (sqr : SqrN N) (hsqr : IsSqrN sqr)
    (hN : n + 1 < N) (hn : 1 ≤ n) (h2 : 2 * n + 2 < USize.size) (cnt : Nat) :
    ∀ arr p, arr.size < USize.size →
      oA + (p + cnt) * (n + 1) ≤ arr.size →
      (∀ q, p ≤ q → q < p + cnt → coef arr n oA q < fermat n) →
      (pointSqrLoop n oA N sqr arr p cnt).size = arr.size ∧
      (∀ j, (j < oA + p * (n + 1) ∨ oA + (p + cnt) * (n + 1) ≤ j) →
        (pointSqrLoop n oA N sqr arr p cnt)[j]! = arr[j]!) ∧
      (∀ q, p ≤ q → q < p + cnt →
        coef (pointSqrLoop n oA N sqr arr p cnt) n oA q =
          coef arr n oA q * coef arr n oA q % fermat n) := by
  induction cnt with
  | zero =>
    intro arr p _ _ _
    exact ⟨rfl, fun _ _ => rfl, fun q h₁ h₂ => absurd h₂ (by lia)⟩
  | succ cnt ih =>
    intro arr p hS hB hv
    have hw := Nat.mul_le_mul_right (n + 1) (show p + 1 ≤ p + (cnt + 1) by lia)
    rw [Nat.add_mul, Nat.one_mul] at hw
    obtain ⟨x₁, x₂, x₃, x₄⟩ := sl_spec arr (oA + p * (n + 1)) (n + 1) (by lia) hS
    have hx : (sl arr (oA + p * (n + 1)) (n + 1)).size.toNat < N := by rw [x₃]; lia
    obtain ⟨m₁, m₂⟩ := hsqr _ hx
    rw [x₃, x₄, show 2 * (n + 1) = 2 * n + 2 by lia] at m₂
    rw [x₃, show 2 * (n + 1) = 2 * n + 2 by lia] at m₁
    rw [pointSqrLoop, dite_eq_left hx]
    generalize sqr (sl arr (oA + p * (n + 1)) (n + 1)) hx = P' at *
    have hvA := hv p (Nat.le_refl _) (by lia)
    simp only [coef, win, fermat] at hvA
    obtain ⟨r₁, r₂, r₃⟩ := reduceAt_spec arr n (oA + p * (n + 1)) P' hS (by lia) hn m₁
      (by rw [m₁]; lia) (by rw [m₂]; exact Nat.mul_le_mul (by lia) (by lia))
    generalize reduceAt arr n (oA + p * (n + 1)) P' = a₁ at *
    have hu : ∀ q, p + 1 ≤ q → q < p + (cnt + 1) → coef a₁ n oA q = coef arr n oA q := by
      intro q h₁ h₂
      have d := Nat.mul_le_mul_right (n + 1) h₁
      have d' := Nat.mul_le_mul_right (n + 1) (show q + 1 ≤ p + (cnt + 1) by lia)
      rw [Nat.add_mul, Nat.one_mul] at d d'
      exact win_congr fun j _ _ => r₂ j (by lia)
    obtain ⟨i₁, i₂, i₃⟩ := ih a₁ (p + 1) (by rw [r₁]; exact hS) (by rw [r₁]; lia)
      fun q h₁ h₂ => by rw [hu q h₁ (by lia)]; exact hv q (by lia) (by lia)
    refine ⟨i₁.trans r₁, fun j hj => ?_, fun q h₁ h₂ => ?_⟩
    · rw [i₂ j (by rw [Nat.add_mul, Nat.one_mul]; lia), r₂ j (by lia)]
    · by_cases e : q = p
      · subst e
        have : coef (pointSqrLoop n oA N sqr a₁ (q + 1) cnt) n oA q = coef a₁ n oA q :=
          win_congr fun j _ _ => i₂ j (by lia)
        rw [this]
        exact r₃.trans (by rw [m₂])
      · rw [i₃ q (by lia) (by lia), hu q (by lia) h₂]

/-! ## Scaling -/

/--
Divides windows `l` to `l + cnt - 1` of the block at `o` by `2ᵏ`, modulo `F`: multiplies them by
`2^(N - k)` into the scratch window `t`, then subtracts that from the zero window `z`, since
`2^(-k) ≡ -2^(N - k)`.
-/
public def scaleLoop (n o t z k : Nat) : UInt32Array → Nat → Nat → UInt32Array
  | arr, _, 0 => arr
  | arr, l, cnt + 1 =>
    scaleLoop n o t z k (subModG (mulPow2G arr n t (o + l * (n + 1)) (32 * n - k)) n
      (o + l * (n + 1)) z t) (l + 1) cnt

public theorem scaleLoop_spec (n o t z k : Nat) (hn : 1 ≤ n) (hk : 1 ≤ k)
    (hN32 : 32 * n < USize.size) (cnt : Nat) :
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
        (fermat n - coef arr n o q * 2 ^ (32 * n - k) % fermat n) % fermat n) := by
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
    obtain ⟨m₁, m₂, m₃⟩ := mulPow2G_spec arr n t (o + l * (n + 1)) (32 * n - k) hS ht (by lia) hn
      (by lia) (by lia) (by lia) (hv l (Nat.le_refl _) (by lia))
    generalize mulPow2G arr n t (o + l * (n + 1)) (32 * n - k) = a₁ at *
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
public def addCoef (arr : UInt32Array) (o T off : Nat) (src : UInt32Array) (so len₀ : Nat) :
    UInt32Array :=
  let len := min len₀ (T - off)
  let q := addAt arr (o + off) len (sl src so len)
  -- The carry first, so that the pair is dead when the array is written.
  let c := q.2
  let a := q.1
  if h : LoopBound a (o + off + len).toUSize (T - off - len).toUSize
  then (incrAt a (o + off + len).toUSize (T - off - len).toUSize h 0 c).1 else a

set_option maxHeartbeats 400000 in
public theorem addCoef_spec (arr : UInt32Array) (o T off : Nat) (src : UInt32Array) (so len₀ : Nat)
    (hS : arr.size < USize.size) (hT : o + T ≤ arr.size) (hoff : off ≤ T)
    (hsS : src.size < USize.size) (hs : so + len₀ ≤ src.size)
    (hV : arr.valAt o T + 2 ^ (32 * off) * src.valAt so len₀ < 2 ^ (32 * T)) :
    (addCoef arr o T off src so len₀).size = arr.size ∧
      (∀ i, (i < o ∨ o + T ≤ i) → (addCoef arr o T off src so len₀)[i]! = arr[i]!) ∧
      (addCoef arr o T off src so len₀).valAt o T =
        arr.valAt o T + 2 ^ (32 * off) * src.valAt so len₀ := by
  -- Only the limbs inside the region count.
  have hsplitT : 2 ^ (32 * T) = 2 ^ (32 * off) * 2 ^ (32 * (T - off)) := by
    rw [← Nat.pow_add]; congr 1; lia
  have hVr : src.valAt so len₀ < 2 ^ (32 * (T - off)) := by
    rw [hsplitT] at hV
    rcases Nat.lt_or_ge (src.valAt so len₀) (2 ^ (32 * (T - off))) with e | e
    · exact e
    · have := Nat.mul_le_mul_left (2 ^ (32 * off)) e; lia
  have hV' : src.valAt so (min len₀ (T - off)) = src.valAt so len₀ := by
    rcases Nat.le_total len₀ (T - off) with h | h
    · rw [Nat.min_eq_left h]
    · rw [Nat.min_eq_right h]
      have e := UInt32Array.valAt_add src so (T - off) (len₀ - (T - off))
      rw [show T - off + (len₀ - (T - off)) = len₀ by lia] at e
      have hP := Nat.two_pow_pos (32 * (T - off))
      rcases Nat.eq_zero_or_pos (src.valAt (so + (T - off)) (len₀ - (T - off))) with e₀ | e₀
      · rw [e, e₀, Nat.mul_zero, Nat.add_zero]
      · have := Nat.mul_le_mul_left (2 ^ (32 * (T - off))) e₀; lia
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
  have hreg : ∀ a : UInt32Array, a.valAt o T = a.valAt o off + 2 ^ (32 * off) *
      (a.valAt (o + off) (min len₀ (T - off)) + 2 ^ (32 * min len₀ (T - off)) *
        a.valAt (o + off + min len₀ (T - off)) (T - off - min len₀ (T - off))) := by
    intro a
    rw [← UInt32Array.valAt_add, ← UInt32Array.valAt_add]
    congr 1; lia
  have hlo₁ : (incrAt q.1 _ _ hlb 0 q.2).1.valAt o off = arr.valAt o off :=
    UInt32Array.valAt_congr _ fun i _ _ => by rw [i₂ i (by lia), a₂ i (by lia)]
  have hw₁ : (incrAt q.1 _ _ hlb 0 q.2).1.valAt (o + off) (min len₀ (T - off)) =
      q.1.valAt (o + off) (min len₀ (T - off)) :=
    UInt32Array.valAt_congr _ fun i _ _ => i₂ i (by lia)
  have hr₁ : q.1.valAt (o + off + min len₀ (T - off)) (T - off - min len₀ (T - off)) =
      arr.valAt (o + off + min len₀ (T - off)) (T - off - min len₀ (T - off)) :=
    UInt32Array.valAt_congr _ fun i _ _ => a₂ i (by lia)
  rw [hr₁] at i₃
  rw [hreg, hreg arr, hlo₁, hw₁]
  have hsplit2 : 2 ^ (32 * (T - off)) = 2 ^ (32 * min len₀ (T - off)) *
      2 ^ (32 * (T - off - min len₀ (T - off))) := by rw [← Nat.pow_add]; congr 1; lia
  rw [hsplitT, hsplit2, ← Nat.mul_assoc, hreg arr] at hV
  exact add_coef_eq a₃ i₃ hV

/--
Adds windows `l` to `l + cnt - 1` of the block at `oA` of `src`, the coefficients, to the region
of `T` limbs at `o` of `arr`, window `i` from limb `i m` on.
-/
public def recLoop (T m n oA : Nat) (src : UInt32Array) : UInt32Array → Nat → Nat → Nat →
    UInt32Array
  | arr, _, _, 0 => arr
  | arr, o, l, cnt + 1 =>
    recLoop T m n oA src
      (if l * m ≤ T then addCoef arr o T (l * m) src (oA + l * (n + 1)) (n + 1) else arr) o (l + 1)
      cnt

public theorem recLoop_spec (T m n oA : Nat) (src : UInt32Array) (hsS : src.size < USize.size)
    (cnt : Nat) :
    ∀ arr o l, arr.size < USize.size → o + T ≤ arr.size → oA + (l + cnt) * (n + 1) ≤ src.size →
      arr.valAt o T + sumRange (fun i => 2 ^ (32 * ((l + i) * m)) * coef src n oA (l + i)) cnt <
        2 ^ (32 * T) →
      (recLoop T m n oA src arr o l cnt).size = arr.size ∧
      (∀ j, (j < o ∨ o + T ≤ j) → (recLoop T m n oA src arr o l cnt)[j]! = arr[j]!) ∧
      (recLoop T m n oA src arr o l cnt).valAt o T = arr.valAt o T +
        sumRange (fun i => 2 ^ (32 * ((l + i) * m)) * coef src n oA (l + i)) cnt := by
  induction cnt with
  | zero => intro arr o l _ _ _ _; exact ⟨rfl, fun _ _ => rfl, by simp [recLoop]⟩
  | succ cnt ih =>
    intro arr o l hS hT hsrc hsum
    rw [sumRange_succ_left] at hsum ⊢
    simp only [Nat.add_zero] at hsum ⊢
    have hw := Nat.mul_le_mul_right (n + 1) (show l + 1 ≤ l + (cnt + 1) by lia)
    rw [Nat.add_mul, Nat.one_mul] at hw
    have hs' : sumRange (fun i => 2 ^ (32 * ((l + (i + 1)) * m)) * coef src n oA (l + (i + 1)))
        cnt = sumRange (fun i => 2 ^ (32 * ((l + 1 + i) * m)) * coef src n oA (l + 1 + i)) cnt :=
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
        · have := Nat.mul_le_mul_left (2 ^ (32 * (l * m))) h
          have : 2 ^ (32 * T) ≤ 2 ^ (32 * (l * m)) := Nat.pow_le_pow_right (by decide) (by lia)
          lia
      obtain ⟨i₁, i₂, i₃⟩ := ih arr o (l + 1) hS hT (by lia) (by rw [hc] at hsum; lia)
      refine ⟨i₁, i₂, ?_⟩
      rw [i₃, hc]
      lia

/-! ## The multiplication -/

/--
`a b` into the first `a.size + b.size` limbs of `r`, with `K = 2ᵏ` windows of `n + 1` limbs for
the pieces of `m` limbs of each operand. The layout of the flat array: the block of `a` at `0`,
the block of `b` at `K (n + 1)`, the scratch window, and a zero window.
-/
public def fftMulAt (N : Nat) (mul : MulN N) (r a b : USlice) (k m n : Nat) : UInt32Array :=
  let K := 2 ^ k
  let oB := K * (n + 1)
  let t := 2 * K * (n + 1)
  let z := t + (n + 1)
  let σ := 2 * (32 * n) / K
  let FA := loadLoop 0 n m a (UInt32Array.replicate (z + (n + 1)) 0) 0 K
  let FA := loadLoop oB n m b FA 0 K
  let FA := fwd n t k FA 0 σ
  let FA := fwd n t k FA oB σ
  let FA := pointLoop n 0 oB N mul FA 0 K
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
  hdiv : 2 * (32 * n) % 2 ^ k = 0
  ha : 0 < a.size.toNat
  hb : 0 < b.size.toNat
  hpieces : (a.size.toNat + m - 1) / m + (b.size.toNat + m - 1) / m ≤ 2 ^ k + 1
  hbits : 2 ^ k * 2 ^ (64 * m) ≤ 2 ^ (32 * n)
  hr : a.size.toNat + b.size.toNat ≤ r.size.toNat
  hS : (2 * 2 ^ k + 2) * (n + 1) < USize.size
  hN32 : 32 * n < USize.size
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
public theorem fftMulAt_spec (N : Nat) (mul : MulN N) (hmul : IsMulN mul) (r a b : USlice)
    (k m n : Nat) (hN : 2 * n + 2 < N) (hp : FFTParams r a b k m n) :
    (fftMulAt N mul r a b k m n).size = r.array.size ∧
      (∀ i, (i < r.start.toNat ∨ r.start.toNat + a.size.toNat + b.size.toNat ≤ i) →
        (fftMulAt N mul r a b k m n)[i]! = r.array[i]!) ∧
      (fftMulAt N mul r a b k m n).valAt r.start.toNat (a.size.toNat + b.size.toNat) =
        a.toNat * b.toNat := by
  obtain ⟨hk, hn, hm, hmn, hdiv, ha, hb, hpc, hbits, hr, hS, hN32, haS, hbS, hrS⟩ := hp
  have hF₀ : 0 < fermat n := by simp [fermat]
  have hK1 : 2 ≤ 2 ^ k := by
    have := Nat.pow_le_pow_right (show 0 < 2 by decide) hk; simpa using this
  have hσ : 2 * (32 * n) / 2 ^ k * 2 ^ k = 2 * (32 * n) :=
    Nat.div_mul_cancel (Nat.dvd_of_mod_eq_zero hdiv)
  dsimp only [fftMulAt]
  generalize 2 * (32 * n) / 2 ^ k = σ at *
  -- The layout.
  have hw := Nat.mul_le_mul_right (n + 1) (show 2 ^ k ≤ 2 * 2 ^ k by lia)
  have hsz : (UInt32Array.replicate (2 * 2 ^ k * (n + 1) + (n + 1) + (n + 1)) 0).size =
      2 * 2 ^ k * (n + 1) + (n + 1) + (n + 1) := by simp
  have hSz : 2 * 2 ^ k * (n + 1) + (n + 1) + (n + 1) < USize.size := by
    rw [show 2 * 2 ^ k * (n + 1) + (n + 1) + (n + 1) = (2 * 2 ^ k + 2) * (n + 1) by
      rw [Nat.add_mul]; lia]
    exact hS
  have hBB : 2 ^ k * (n + 1) + 2 ^ k * (n + 1) = 2 * 2 ^ k * (n + 1) := by rw [Nat.mul_assoc]; lia
  generalize hS₀ : 2 * 2 ^ k * (n + 1) + (n + 1) + (n + 1) = S at *
  -- Loading `a`.
  obtain ⟨l₁, l₂, l₃⟩ := loadLoop_spec 0 n m a (by lia) haS (2 ^ k)
    (UInt32Array.replicate S 0) 0 (by rw [hsz]; exact hSz) (by rw [hsz]; lia)
    (fun p _ _ => valAt_replicate_zero ..)
  generalize loadLoop 0 n m a (UInt32Array.replicate S 0) 0 (2 ^ k) = A₁ at *
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
  have hXF : 2 ^ (32 * m) < fermat n := by
    simp only [fermat]
    have : 2 ^ (32 * m) ≤ 2 ^ (32 * n) := Nat.pow_le_pow_right (by decide) (by lia)
    lia
  -- The forward transforms.
  obtain ⟨f₁, f₂, f₃⟩ := fwd_spec n (2 * 2 ^ k * (n + 1)) hn hN32 k A₂ 0 σ hσ
    ⟨by rw [m₁]; exact hSz, by rw [m₁]; lia, by rw [m₁]; lia, by lia⟩
    (fun p hp => by rw [cA p hp]; exact Nat.lt_trans (piece_lt ..) hXF)
  generalize fwd n (2 * 2 ^ k * (n + 1)) k A₂ 0 σ = A₃ at *
  have cB₃ : ∀ p < 2 ^ k, coef A₃ n (2 ^ k * (n + 1)) p = piece b m p := by
    intro p hp
    have := win_in (2 ^ k * (n + 1)) n p (2 ^ k) hp
    rw [← cB p hp]
    exact win_congr fun j _ _ => f₂ j (by lia) (by lia)
  obtain ⟨g₁, g₂, g₃⟩ := fwd_spec n (2 * 2 ^ k * (n + 1)) hn hN32 k A₃ (2 ^ k * (n + 1)) σ hσ
    ⟨by rw [f₁, m₁]; exact hSz, by rw [f₁, m₁]; lia, by rw [f₁, m₁]; lia, by lia⟩
    (fun p hp => by rw [cB₃ p hp]; exact Nat.lt_trans (piece_lt ..) hXF)
  generalize fwd n (2 * 2 ^ k * (n + 1)) k A₃ (2 ^ k * (n + 1)) σ = A₄ at *
  have cA₄ : ∀ p < 2 ^ k, coef A₄ n 0 p = coef A₃ n 0 p := by
    intro p hp
    have := win_in 0 n p (2 ^ k) hp
    exact win_congr fun j _ _ => g₂ j (by lia) (by lia)
  -- The pointwise products.
  obtain ⟨p₁, p₂, p₃⟩ := pointLoop_spec n 0 (2 ^ k * (n + 1)) N mul hmul hN hn (2 ^ k) A₄ 0
    (by rw [g₁, f₁, m₁]; exact hSz)
    (by lia) (by rw [g₁, f₁, m₁]; lia) (fun q _ hq => by
      rw [cA₄ q (by lia), f₃ q (by lia), g₃ q (by lia)]
      exact ⟨Nat.mod_lt _ hF₀, Nat.mod_lt _ hF₀⟩)
  generalize pointLoop n 0 (2 ^ k * (n + 1)) N mul A₄ 0 (2 ^ k) =
    A₅ at *
  -- The inverse transform.
  obtain ⟨v₁, v₂, v₃⟩ := inv_spec n (2 * 2 ^ k * (n + 1)) hn hN32 k A₅ 0 σ hσ
    ⟨by rw [p₁, g₁, f₁, m₁]; exact hSz, by rw [p₁, g₁, f₁, m₁]; lia, by rw [p₁, g₁, f₁, m₁]; lia,
      by lia⟩ (fun q hq => by rw [p₃ q (by lia) (by lia)]; exact Nat.mod_lt _ hF₀)
  generalize inv n (2 * 2 ^ k * (n + 1)) k A₅ 0 σ = A₆ at *
  -- The zero window is untouched.
  have hz : win A₆ n (2 * 2 ^ k * (n + 1) + (n + 1)) = 0 := by
    have : win A₆ n (2 * 2 ^ k * (n + 1) + (n + 1)) =
        win (UInt32Array.replicate S 0) n (2 * 2 ^ k * (n + 1) + (n + 1)) :=
      win_congr fun j _ _ => by
        rw [v₂ j (by lia) (by lia), p₂ j (by lia), g₂ j (by lia) (by lia), f₂ j (by lia) (by lia),
          m₂ j (by lia), l₂ j (by lia)]
    rw [this]
    exact valAt_replicate_zero ..
  -- The division by `2ᵏ`.
  have hsz₆ : A₆.size = S := by rw [v₁, p₁, g₁, f₁, m₁]
  obtain ⟨s₁, -, s₃⟩ := scaleLoop_spec n 0 (2 * 2 ^ k * (n + 1)) (2 * 2 ^ k * (n + 1) + (n + 1)) k
    hn hk hN32 (2 ^ k) A₆ 0 (by rw [hsz₆]; exact hSz) (by rw [hsz₆]; lia) (by rw [hsz₆]; lia)
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
    rw [← fft_coef (pieces a m la) (pieces b m lb) k (32 * n) σ (2 ^ (32 * m)) (F := fermat n) rfl
      hk hσ
      (by rw [length_pieces, length_pieces]; lia) hβne
      (fun x hx => by
        simp only [pieces, List.mem_map, List.mem_range] at hx
        obtain ⟨i, -, rfl⟩ := hx; exact piece_lt ..)
      (fun x hx => by
        simp only [pieces, List.mem_map, List.mem_range] at hx
        obtain ⟨i, -, rfl⟩ := hx; exact piece_lt ..)
      (by rw [← Nat.pow_add, show 32 * m + 32 * m = 64 * m by lia]; exact hbits)
      (by rw [length_pieces]; lia) (by rw [length_pieces]; lia) l hl]
    have hα : ∀ q, sumRange (fun i => coef A₂ n 0 i * 2 ^ (σ * i * rev k q)) (2 ^ k) =
        sumRange (fun i => (pieces a m la).getD i 0 * 2 ^ (σ * i * rev k q)) (2 ^ k) :=
      fun q => sumRange_congr fun i hi => by rw [hαL i hi]
    have hβ : ∀ q, sumRange (fun i => coef A₃ n (2 ^ k * (n + 1)) i * 2 ^ (σ * i * rev k q))
        (2 ^ k) = sumRange (fun i => (pieces b m lb).getD i 0 * 2 ^ (σ * i * rev k q)) (2 ^ k) :=
      fun q => sumRange_congr fun i hi => by rw [cB₃ i hi, ← cB i hi, hβL i hi]
    have hsum : sumRange (fun p => coef A₅ n 0 p * 2 ^ ((2 * (32 * n) - σ) * rev k p * l))
        (2 ^ k) = sumRange (fun p =>
          sumRange (fun i => (pieces a m la).getD i 0 * 2 ^ (σ * i * rev k p)) (2 ^ k) %
            fermat n * (sumRange (fun i => (pieces b m lb).getD i 0 * 2 ^ (σ * i * rev k p))
              (2 ^ k) % fermat n) % fermat n * 2 ^ ((2 * (32 * n) - σ) * rev k p * l)) (2 ^ k) :=
      sumRange_congr fun q hq => by
        rw [p₃ q (by lia) (by lia), cA₄ q hq, f₃ q hq, g₃ q hq, hα, hβ]
    rw [hsum]
  -- The value of the coefficients at `2^(32 m)`.
  generalize hZ : polyMul (pieces a m la) (pieces b m lb) = Z at hc
  have hZK : Z.length ≤ 2 ^ k := by
    rw [← hZ]; have := length_polyMul (pieces a m la) (pieces b m lb) hβne
    rw [length_pieces, length_pieces] at this; lia
  have hab : sumRange (fun i => 2 ^ (32 * ((0 + i) * m)) * coef A₇ n 0 (0 + i)) (2 ^ k) =
      a.toNat * b.toNat := by
    rw [← polyVal_pieces a m la hla, ← polyVal_pieces b m lb hlb, ← polyVal_polyMul, hZ,
      polyVal_eq_sumRange _ Z _ hZK]
    exact sumRange_congr fun i hi => by
      rw [Nat.zero_add, hc i hi, Nat.mul_comm, ← Nat.pow_mul]; congr 2; lia
  have hablt : a.toNat * b.toNat < 2 ^ (32 * (a.size.toNat + b.size.toNat)) := by
    rw [Nat.mul_add, Nat.pow_add]
    have h₁ : a.toNat < 2 ^ (32 * a.size.toNat) := by rw [USlice.toNat_eq_valAt]; exact valAt_lt ..
    have h₂ : b.toNat < 2 ^ (32 * b.size.toNat) := by rw [USlice.toNat_eq_valAt]; exact valAt_lt ..
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

/-! ## The product modulo `β^N - 1` -/

/--
`a b` modulo `2^(32 N) - 1`, for `N = m 2ᵏ`, into the first `N + n + 1` limbs of `r`, like
`fftMulAt` but with the pieces of each operand wrapping around: `K = 2ᵏ` pieces of `m` limbs of
each, the cyclic convolution of the transforms, and the coefficients added at `2^(32 m)`, whose
sum is `≡ a b` modulo `2^(32 N) - 1` since `2^(32 m K) ≡ 1`. Like GMP's `mpn_mulmod_bnm1`, it
costs about half a product of the same operands.
-/
public def fftMulModAt (N : Nat) (mul : MulN N) (r a b : USlice) (k m n : Nat) : UInt32Array :=
  let K := 2 ^ k
  let oB := K * (n + 1)
  let t := 2 * K * (n + 1)
  let z := t + (n + 1)
  let σ := 2 * (32 * n) / K
  let FA := loadLoop 0 n m a (UInt32Array.replicate (z + (n + 1)) 0) 0 K
  let FA := loadLoop oB n m b FA 0 K
  let FA := fwd n t k FA 0 σ
  let FA := fwd n t k FA oB σ
  let FA := pointLoop n 0 oB N mul FA 0 K
  let FA := inv n t k FA 0 σ
  let FA := scaleLoop n 0 t z k FA 0 K
  recLoop (m * K + n + 1) m n 0 FA (zeroInto (r.slice 0 (m * K + n + 1).toUSize)) r.start.toNat 0 K

/-- The parameters of `fftMulModAt` for which it computes `a b` modulo `2^(32 m 2ᵏ) - 1`. -/
public structure FFTModParams (r a b : USlice) (k m n : Nat) : Prop where
  hk : 1 ≤ k
  hn : 1 ≤ n
  hm : 1 ≤ m
  hmn : m ≤ n
  hdiv : 2 * (32 * n) % 2 ^ k = 0
  ha : 0 < a.size.toNat
  hb : 0 < b.size.toNat
  hla : a.size.toNat ≤ m * 2 ^ k
  hlb : b.size.toNat ≤ m * 2 ^ k
  hbits : 2 * 2 ^ k * 2 ^ (64 * m) ≤ 2 ^ (32 * n)
  hr : m * 2 ^ k + n + 1 ≤ r.size.toNat
  hS : (2 * 2 ^ k + 2) * (n + 1) < USize.size
  hN32 : 32 * n < USize.size
  haS : a.array.size < USize.size
  hbS : b.array.size < USize.size
  hrS : r.array.size < USize.size

/-- A geometric bound: `∑_{i<K} c_i Xⁱ < (C + 1) X^K` for `c_i ≤ C` and `X ≥ 2`. -/
private theorem sum_pow_lt (c : Nat → Nat) (C X K : Nat) (hX : 2 ≤ X) (hc : ∀ i < K, c i ≤ C) :
    sumRange (fun i => X ^ i * c i) K < (C + 1) * X ^ K := by
  induction K with
  | zero => simp [sumRange]
  | succ K ih =>
    rw [sumRange_succ]
    have h₁ := ih fun i hi => hc i (by lia)
    have h₂ := Nat.mul_le_mul_left (X ^ K) (hc K (by lia))
    have h₃ : (C + 1) * X ^ K + X ^ K * C ≤ (C + 1) * X ^ (K + 1) := by
      rw [Nat.pow_succ]
      have := Nat.mul_le_mul_left ((C + 1) * X ^ K) hX
      rw [Nat.mul_comm (X ^ K) C]
      lia
    lia

set_option maxHeartbeats 800000 in
public theorem fftMulModAt_spec (N : Nat) (mul : MulN N) (hmul : IsMulN mul) (r a b : USlice)
    (k m n : Nat) (hN : 2 * n + 2 < N) (hp : FFTModParams r a b k m n) :
    (fftMulModAt N mul r a b k m n).size = r.array.size ∧
      (∀ i, (i < r.start.toNat ∨ r.start.toNat + (m * 2 ^ k + n + 1) ≤ i) →
        (fftMulModAt N mul r a b k m n)[i]! = r.array[i]!) ∧
      (fftMulModAt N mul r a b k m n).valAt r.start.toNat (m * 2 ^ k + n + 1) %
          (2 ^ (32 * (m * 2 ^ k)) - 1) =
        a.toNat * b.toNat % (2 ^ (32 * (m * 2 ^ k)) - 1) := by
  obtain ⟨hk, hn, hm, hmn, hdiv, ha, hb, hpa, hpb, hbits, hr, hS, hN32, haS, hbS, hrS⟩ := hp
  have hF₀ : 0 < fermat n := by simp [fermat]
  have hK1 : 2 ≤ 2 ^ k := by
    have := Nat.pow_le_pow_right (show 0 < 2 by decide) hk; simpa using this
  have hσ : 2 * (32 * n) / 2 ^ k * 2 ^ k = 2 * (32 * n) :=
    Nat.div_mul_cancel (Nat.dvd_of_mod_eq_zero hdiv)
  dsimp only [fftMulModAt]
  generalize 2 * (32 * n) / 2 ^ k = σ at *
  -- The layout.
  have hw := Nat.mul_le_mul_right (n + 1) (show 2 ^ k ≤ 2 * 2 ^ k by lia)
  have hsz : (UInt32Array.replicate (2 * 2 ^ k * (n + 1) + (n + 1) + (n + 1)) 0).size =
      2 * 2 ^ k * (n + 1) + (n + 1) + (n + 1) := by simp
  have hSz : 2 * 2 ^ k * (n + 1) + (n + 1) + (n + 1) < USize.size := by
    rw [show 2 * 2 ^ k * (n + 1) + (n + 1) + (n + 1) = (2 * 2 ^ k + 2) * (n + 1) by
      rw [Nat.add_mul]; lia]
    exact hS
  have hBB : 2 ^ k * (n + 1) + 2 ^ k * (n + 1) = 2 * 2 ^ k * (n + 1) := by rw [Nat.mul_assoc]; lia
  generalize hS₀ : 2 * 2 ^ k * (n + 1) + (n + 1) + (n + 1) = S at *
  -- Loading `a`.
  obtain ⟨l₁, l₂, l₃⟩ := loadLoop_spec 0 n m a (by lia) haS (2 ^ k)
    (UInt32Array.replicate S 0) 0 (by rw [hsz]; exact hSz) (by rw [hsz]; lia)
    (fun p _ _ => valAt_replicate_zero ..)
  generalize loadLoop 0 n m a (UInt32Array.replicate S 0) 0 (2 ^ k) = A₁ at *
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
  have hXF : 2 ^ (32 * m) < fermat n := by
    simp only [fermat]
    have : 2 ^ (32 * m) ≤ 2 ^ (32 * n) := Nat.pow_le_pow_right (by decide) (by lia)
    lia
  -- The forward transforms.
  obtain ⟨f₁, f₂, f₃⟩ := fwd_spec n (2 * 2 ^ k * (n + 1)) hn hN32 k A₂ 0 σ hσ
    ⟨by rw [m₁]; exact hSz, by rw [m₁]; lia, by rw [m₁]; lia, by lia⟩
    (fun p hp => by rw [cA p hp]; exact Nat.lt_trans (piece_lt ..) hXF)
  generalize fwd n (2 * 2 ^ k * (n + 1)) k A₂ 0 σ = A₃ at *
  have cB₃ : ∀ p < 2 ^ k, coef A₃ n (2 ^ k * (n + 1)) p = piece b m p := by
    intro p hp
    have := win_in (2 ^ k * (n + 1)) n p (2 ^ k) hp
    rw [← cB p hp]
    exact win_congr fun j _ _ => f₂ j (by lia) (by lia)
  obtain ⟨g₁, g₂, g₃⟩ := fwd_spec n (2 * 2 ^ k * (n + 1)) hn hN32 k A₃ (2 ^ k * (n + 1)) σ hσ
    ⟨by rw [f₁, m₁]; exact hSz, by rw [f₁, m₁]; lia, by rw [f₁, m₁]; lia, by lia⟩
    (fun p hp => by rw [cB₃ p hp]; exact Nat.lt_trans (piece_lt ..) hXF)
  generalize fwd n (2 * 2 ^ k * (n + 1)) k A₃ (2 ^ k * (n + 1)) σ = A₄ at *
  have cA₄ : ∀ p < 2 ^ k, coef A₄ n 0 p = coef A₃ n 0 p := by
    intro p hp
    have := win_in 0 n p (2 ^ k) hp
    exact win_congr fun j _ _ => g₂ j (by lia) (by lia)
  -- The pointwise products.
  obtain ⟨p₁, p₂, p₃⟩ := pointLoop_spec n 0 (2 ^ k * (n + 1)) N mul hmul hN hn (2 ^ k) A₄ 0
    (by rw [g₁, f₁, m₁]; exact hSz)
    (by lia) (by rw [g₁, f₁, m₁]; lia) (fun q _ hq => by
      rw [cA₄ q (by lia), f₃ q (by lia), g₃ q (by lia)]
      exact ⟨Nat.mod_lt _ hF₀, Nat.mod_lt _ hF₀⟩)
  generalize pointLoop n 0 (2 ^ k * (n + 1)) N mul A₄ 0 (2 ^ k) =
    A₅ at *
  -- The inverse transform.
  obtain ⟨v₁, v₂, v₃⟩ := inv_spec n (2 * 2 ^ k * (n + 1)) hn hN32 k A₅ 0 σ hσ
    ⟨by rw [p₁, g₁, f₁, m₁]; exact hSz, by rw [p₁, g₁, f₁, m₁]; lia, by rw [p₁, g₁, f₁, m₁]; lia,
      by lia⟩ (fun q hq => by rw [p₃ q (by lia) (by lia)]; exact Nat.mod_lt _ hF₀)
  generalize inv n (2 * 2 ^ k * (n + 1)) k A₅ 0 σ = A₆ at *
  -- The zero window is untouched.
  have hz : win A₆ n (2 * 2 ^ k * (n + 1) + (n + 1)) = 0 := by
    have : win A₆ n (2 * 2 ^ k * (n + 1) + (n + 1)) =
        win (UInt32Array.replicate S 0) n (2 * 2 ^ k * (n + 1) + (n + 1)) :=
      win_congr fun j _ _ => by
        rw [v₂ j (by lia) (by lia), p₂ j (by lia), g₂ j (by lia) (by lia), f₂ j (by lia) (by lia),
          m₂ j (by lia), l₂ j (by lia)]
    rw [this]
    exact valAt_replicate_zero ..
  -- The division by `2ᵏ`.
  have hsz₆ : A₆.size = S := by rw [v₁, p₁, g₁, f₁, m₁]
  obtain ⟨s₁, -, s₃⟩ := scaleLoop_spec n 0 (2 * 2 ^ k * (n + 1)) (2 * 2 ^ k * (n + 1) + (n + 1)) k
    hn hk hN32 (2 ^ k) A₆ 0 (by rw [hsz₆]; exact hSz) (by rw [hsz₆]; lia) (by rw [hsz₆]; lia)
    (by rw [hsz₆]; lia) (by lia) (by lia) (by lia) hz
    (fun q _ hq => by rw [v₃ q (by lia)]; exact Nat.mod_lt _ hF₀)
  generalize scaleLoop n 0 (2 * 2 ^ k * (n + 1)) (2 * 2 ^ k * (n + 1) + (n + 1)) k A₆ 0 (2 ^ k) =
    A₇ at *
  -- The coefficients are those of the product of the pieces.
  have hla := cover a.size.toNat m hm
  have hlb := cover b.size.toNat m hm
  have hla₁ : 1 ≤ (a.size.toNat + m - 1) / m := (Nat.le_div_iff_mul_le (by lia)).2 (by lia)
  have hlb₁ : 1 ≤ (b.size.toNat + m - 1) / m := (Nat.le_div_iff_mul_le (by lia)).2 (by lia)
  have hlaK : (a.size.toNat + m - 1) / m ≤ 2 ^ k :=
    (Nat.div_le_iff_le_mul_add_pred (by lia)).2 (by rw [Nat.mul_comm] at hpa; lia)
  have hlbK : (b.size.toNat + m - 1) / m ≤ 2 ^ k :=
    (Nat.div_le_iff_le_mul_add_pred (by lia)).2 (by rw [Nat.mul_comm] at hpb; lia)
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
  have hc : ∀ l < 2 ^ k, coef A₇ n 0 l =
      (cyc (polyMul (pieces a m la) (pieces b m lb)) (2 ^ k)).getD l 0 := by
    intro l hl
    rw [getD_cyc _ _ _ hl, s₃ l (by lia) (by lia), v₃ l hl]
    rw [← fft_coef_cyc (pieces a m la) (pieces b m lb) k (32 * n) σ (2 ^ (32 * m)) (F := fermat n)
      rfl hk hσ hβne
      (fun x hx => by
        simp only [pieces, List.mem_map, List.mem_range] at hx
        obtain ⟨i, -, rfl⟩ := hx; exact piece_lt ..)
      (fun x hx => by
        simp only [pieces, List.mem_map, List.mem_range] at hx
        obtain ⟨i, -, rfl⟩ := hx; exact piece_lt ..)
      (by rw [← Nat.pow_add, show 32 * m + 32 * m = 64 * m by lia]; exact hbits)
      (by rw [length_pieces]; lia) (by rw [length_pieces]; lia) l hl]
    have hα : ∀ q, sumRange (fun i => coef A₂ n 0 i * 2 ^ (σ * i * rev k q)) (2 ^ k) =
        sumRange (fun i => (pieces a m la).getD i 0 * 2 ^ (σ * i * rev k q)) (2 ^ k) :=
      fun q => sumRange_congr fun i hi => by rw [hαL i hi]
    have hβ : ∀ q, sumRange (fun i => coef A₃ n (2 ^ k * (n + 1)) i * 2 ^ (σ * i * rev k q))
        (2 ^ k) = sumRange (fun i => (pieces b m lb).getD i 0 * 2 ^ (σ * i * rev k q)) (2 ^ k) :=
      fun q => sumRange_congr fun i hi => by rw [cB₃ i hi, ← cB i hi, hβL i hi]
    have hsum : sumRange (fun p => coef A₅ n 0 p * 2 ^ ((2 * (32 * n) - σ) * rev k p * l))
        (2 ^ k) = sumRange (fun p =>
          sumRange (fun i => (pieces a m la).getD i 0 * 2 ^ (σ * i * rev k p)) (2 ^ k) %
            fermat n * (sumRange (fun i => (pieces b m lb).getD i 0 * 2 ^ (σ * i * rev k p))
              (2 ^ k) % fermat n) % fermat n * 2 ^ ((2 * (32 * n) - σ) * rev k p * l)) (2 ^ k) :=
      sumRange_congr fun q hq => by
        rw [p₃ q (by lia) (by lia), cA₄ q hq, f₃ q hq, g₃ q hq, hα, hβ]
    rw [hsum]
  have hcF : ∀ l < 2 ^ k, coef A₇ n 0 l ≤ 2 ^ (32 * n) := by
    intro l hl
    rw [s₃ l (by lia) (by lia)]
    exact Nat.le_of_lt_succ (Nat.mod_lt _ hF₀)
  -- The value of the coefficients at `X = 2^(32 m)`, modulo `X^K - 1`.
  generalize hZ : polyMul (pieces a m la) (pieces b m lb) = Z at hc
  have hZ2 : Z.length ≤ 2 * 2 ^ k := by
    rw [← hZ]; have := length_polyMul (pieces a m la) (pieces b m lb) hβne
    rw [length_pieces, length_pieces] at this; lia
  have hval : sumRange (fun i => 2 ^ (32 * ((0 + i) * m)) * coef A₇ n 0 (0 + i)) (2 ^ k) =
      polyVal (2 ^ (32 * m)) (cyc Z (2 ^ k)) := by
    rw [polyVal_eq_sumRange _ _ (2 ^ k) (by rw [length_cyc]; exact Nat.le_refl _)]
    exact sumRange_congr fun i hi => by
      rw [Nat.zero_add, hc i hi, Nat.mul_comm, ← Nat.pow_mul]; congr 2; lia
  have hM : MEq (2 ^ (32 * (m * 2 ^ k)) - 1) ((2 ^ (32 * m)) ^ 2 ^ k) 1 := by
    rw [← Nat.pow_mul, show 32 * m * 2 ^ k = 32 * (m * 2 ^ k) by lia]
    have : 1 ≤ 2 ^ (32 * (m * 2 ^ k)) := Nat.one_le_two_pow
    show _ % _ = _ % _
    rw [show 2 ^ (32 * (m * 2 ^ k)) = (2 ^ (32 * (m * 2 ^ k)) - 1) + 1 by lia,
      Nat.add_sub_cancel, Nat.add_mod_left]
  have hab : MEq (2 ^ (32 * (m * 2 ^ k)) - 1) (a.toNat * b.toNat)
      (polyVal (2 ^ (32 * m)) (cyc Z (2 ^ k))) := by
    rw [← polyVal_pieces a m la hla, ← polyVal_pieces b m lb hlb, ← polyVal_polyMul, hZ]
    exact polyVal_cyc _ _ _ _ hM hZ2
  have hlt : sumRange (fun i => 2 ^ (32 * ((0 + i) * m)) * coef A₇ n 0 (0 + i)) (2 ^ k) <
      2 ^ (32 * (m * 2 ^ k + n + 1)) := by
    have h₁ := sum_pow_lt (fun i => coef A₇ n 0 i) (2 ^ (32 * n)) (2 ^ (32 * m)) (2 ^ k)
      (Nat.le_trans (by decide) (Nat.pow_le_pow_right (by decide) (by lia : 1 ≤ 32 * m))) hcF
    have e : sumRange (fun i => 2 ^ (32 * ((0 + i) * m)) * coef A₇ n 0 (0 + i)) (2 ^ k) =
        sumRange (fun i => (2 ^ (32 * m)) ^ i * coef A₇ n 0 i) (2 ^ k) :=
      sumRange_congr fun i _ => by rw [Nat.zero_add, ← Nat.pow_mul]; congr 2; lia
    rw [e]
    refine Nat.lt_of_lt_of_le h₁ ?_
    have : 2 ^ (32 * n) + 1 ≤ 2 ^ (32 * n + 32) := by
      rw [Nat.pow_add]
      have := Nat.two_pow_pos (32 * n)
      have : 2 ≤ 2 ^ 32 := by decide
      have := Nat.mul_le_mul_left (2 ^ (32 * n)) this
      lia
    calc (2 ^ (32 * n) + 1) * (2 ^ (32 * m)) ^ 2 ^ k
        ≤ 2 ^ (32 * n + 32) * (2 ^ (32 * m)) ^ 2 ^ k := Nat.mul_le_mul_right _ this
      _ = 2 ^ (32 * (m * 2 ^ k + n + 1)) := by
          rw [← Nat.pow_mul, ← Nat.pow_add]; congr 1; lia
  -- Zeroing the result, and adding the coefficients.
  have hT : (m * 2 ^ k + n + 1).toUSize.toNat = m * 2 ^ k + n + 1 :=
    USize.toNat_ofNat_of_lt' (by have := r.size.toNat_lt_size; lia)
  have hrs := r.toNat_size
  have hrst := r.stop_le_size
  have hrle := USize.le_iff_toNat_le.1 r.start_le_stop
  have e₁ := r.start_slice (i := 0) (j := (m * 2 ^ k + n + 1).toUSize) (by simp)
    (by rw [hT]; exact hr)
  have e₂ := r.size_slice (i := 0) (j := (m * 2 ^ k + n + 1).toUSize) (by simp)
    (by rw [hT]; exact hr)
  rw [USize.toNat_zero, Nat.add_zero] at e₁
  rw [USize.toNat_zero, Nat.sub_zero, hT] at e₂
  obtain ⟨z₁, z₂, z₃⟩ := zeroInto_spec (r.slice 0 (m * 2 ^ k + n + 1).toUSize)
  simp only [USlice.array_slice, e₁, e₂, Nat.add_zero] at z₁ z₂ z₃
  generalize zeroInto (r.slice 0 (m * 2 ^ k + n + 1).toUSize) = R₀ at *
  have hsz₇ : A₇.size = S := by rw [s₁, hsz₆]
  obtain ⟨c₁, c₂, c₃⟩ := recLoop_spec (m * 2 ^ k + n + 1) m n 0 A₇
    (by rw [hsz₇]; exact hSz) (2 ^ k) R₀ r.start.toNat 0 (by rw [z₁]; exact hrS) (by rw [z₁]; lia)
    (by rw [hsz₇]; lia) (by rw [z₃, Nat.zero_add]; exact hlt)
  refine ⟨by rw [c₁, z₁], fun i hi => ?_, ?_⟩
  · rw [c₂ i (by lia), z₂ i (by lia)]
  · rw [c₃, z₃, Nat.zero_add, hval]
    exact hab.symm

/-- The conditions of `FFTModParams`, decidably, with `k + 1 + 64 m ≤ 32 n` for the bound. -/
public abbrev FFTModCheck (r a b : USlice) (k m n : Nat) : Prop :=
  1 ≤ k ∧ k ≤ 31 ∧ 1 ≤ n ∧ 1 ≤ m ∧ m ≤ n ∧ 2 * (32 * n) % 2 ^ k = 0 ∧ 0 < a.size.toNat ∧
    0 < b.size.toNat ∧ a.size.toNat ≤ m * 2 ^ k ∧ b.size.toNat ≤ m * 2 ^ k ∧
    k + 1 + 64 * m ≤ 32 * n ∧ m * 2 ^ k + n + 1 ≤ r.size.toNat ∧
    (2 * 2 ^ k + 2) * (n + 1) < USize.size ∧ 32 * n < USize.size ∧
    a.array.size < USize.size ∧ b.array.size < USize.size ∧ r.array.size < USize.size

public theorem FFTModCheck.params {r a b : USlice} {k m n : Nat} (h : FFTModCheck r a b k m n) :
    FFTModParams r a b k m n := by
  obtain ⟨h₁, h₂, h₃, h₄, h₅, h₆, h₇, h₈, h₉, h₁₀, h₁₁, h₁₂, h₁₃, h₁₄, h₁₅, h₁₆, h₁₇⟩ := h
  refine ⟨h₁, h₃, h₄, h₅, h₆, h₇, h₈, h₉, h₁₀, ?_, h₁₂, h₁₃, h₁₄, h₁₅, h₁₆, h₁₇⟩
  rw [show 2 * 2 ^ k = 2 ^ (k + 1) by rw [Nat.pow_succ, Nat.mul_comm], ← Nat.pow_add]
  exact Nat.pow_le_pow_right (by decide) (by lia)

/-- The coefficient size `n` for `fftMulModAt` with `2ᵏ` pieces of `m` limbs. -/
public def fftModN (k m : Nat) : Nat :=
  let q := max 1 (2 ^ k / 64)
  (2 * m + 1 + q - 1) / q * q

/-! ## Squaring -/

/--
`a²` into the first `2 a.size` limbs of `r`, like `fftMulAt r a a` with one forward transform and
squares for the pointwise products: the block of `a` at `0`, the scratch window and a zero window.
-/
public def fftSqrAt (N : Nat) (sqr : SqrN N) (r a : USlice) (k m n : Nat) : UInt32Array :=
  let K := 2 ^ k
  let t := K * (n + 1)
  let z := t + (n + 1)
  let σ := 2 * (32 * n) / K
  let FA := loadLoop 0 n m a (UInt32Array.replicate (z + (n + 1)) 0) 0 K
  let FA := fwd n t k FA 0 σ
  let FA := pointSqrLoop n 0 N sqr FA 0 K
  let FA := inv n t k FA 0 σ
  let FA := scaleLoop n 0 t z k FA 0 K
  recLoop (a.size.toNat + a.size.toNat) m n 0 FA
    (zeroInto (r.slice 0 (a.size + a.size))) r.start.toNat 0 K

set_option maxHeartbeats 800000 in
public theorem fftSqrAt_spec (N : Nat) (sqr : SqrN N) (hsqr : IsSqrN sqr) (r a : USlice)
    (k m n : Nat) (hN : n + 1 < N) (hp : FFTParams r a a k m n) :
    (fftSqrAt N sqr r a k m n).size = r.array.size ∧
      (∀ i, (i < r.start.toNat ∨ r.start.toNat + a.size.toNat + a.size.toNat ≤ i) →
        (fftSqrAt N sqr r a k m n)[i]! = r.array[i]!) ∧
      (fftSqrAt N sqr r a k m n).valAt r.start.toNat (a.size.toNat + a.size.toNat) =
        a.toNat * a.toNat := by
  obtain ⟨hk, hn, hm, hmn, hdiv, ha, -, hpc, hbits, hr, hS, hN32, haS, -, hrS⟩ := hp
  have hF₀ : 0 < fermat n := by simp [fermat]
  have hK1 : 2 ≤ 2 ^ k := by
    have := Nat.pow_le_pow_right (show 0 < 2 by decide) hk; simpa using this
  have hσ : 2 * (32 * n) / 2 ^ k * 2 ^ k = 2 * (32 * n) :=
    Nat.div_mul_cancel (Nat.dvd_of_mod_eq_zero hdiv)
  dsimp only [fftSqrAt]
  generalize 2 * (32 * n) / 2 ^ k = σ at *
  -- The layout.
  have hsz : (UInt32Array.replicate (2 ^ k * (n + 1) + (n + 1) + (n + 1)) 0).size =
      2 ^ k * (n + 1) + (n + 1) + (n + 1) := by simp
  have hSz : 2 ^ k * (n + 1) + (n + 1) + (n + 1) < USize.size := by
    have : 2 ^ k * (n + 1) + (n + 1) + (n + 1) ≤ (2 * 2 ^ k + 2) * (n + 1) := by
      rw [Nat.add_mul, Nat.mul_assoc]; lia
    lia
  generalize hS₀ : 2 ^ k * (n + 1) + (n + 1) + (n + 1) = S at *
  -- Loading `a`.
  obtain ⟨l₁, l₂, l₃⟩ := loadLoop_spec 0 n m a (by lia) haS (2 ^ k)
    (UInt32Array.replicate S 0) 0 (by rw [hsz]; exact hSz) (by rw [hsz]; lia)
    (fun p _ _ => valAt_replicate_zero ..)
  generalize loadLoop 0 n m a (UInt32Array.replicate S 0) 0 (2 ^ k) = A₂ at *
  rw [hsz] at l₁
  have cA : ∀ p < 2 ^ k, coef A₂ n 0 p = piece a m p := fun p hp => l₃ p (by lia) (by lia)
  have hXF : 2 ^ (32 * m) < fermat n := by
    simp only [fermat]
    have : 2 ^ (32 * m) ≤ 2 ^ (32 * n) := Nat.pow_le_pow_right (by decide) (by lia)
    lia
  -- The forward transform.
  obtain ⟨f₁, f₂, f₃⟩ := fwd_spec n (2 ^ k * (n + 1)) hn hN32 k A₂ 0 σ hσ
    ⟨by rw [l₁]; exact hSz, by rw [l₁]; lia, by rw [l₁]; lia, by lia⟩
    (fun p hp => by rw [cA p hp]; exact Nat.lt_trans (piece_lt ..) hXF)
  generalize fwd n (2 ^ k * (n + 1)) k A₂ 0 σ = A₄ at *
  -- The pointwise squares.
  obtain ⟨p₁, p₂, p₃⟩ := pointSqrLoop_spec n 0 N sqr hsqr hN hn (by lia) (2 ^ k) A₄ 0
    (by rw [f₁, l₁]; exact hSz)
    (by rw [f₁, l₁]; lia) (fun q _ hq => by rw [f₃ q (by lia)]; exact Nat.mod_lt _ hF₀)
  generalize pointSqrLoop n 0 N sqr A₄ 0 (2 ^ k) = A₅ at *
  -- The inverse transform.
  obtain ⟨v₁, v₂, v₃⟩ := inv_spec n (2 ^ k * (n + 1)) hn hN32 k A₅ 0 σ hσ
    ⟨by rw [p₁, f₁, l₁]; exact hSz, by rw [p₁, f₁, l₁]; lia, by rw [p₁, f₁, l₁]; lia,
      by lia⟩ (fun q hq => by rw [p₃ q (by lia) (by lia)]; exact Nat.mod_lt _ hF₀)
  generalize inv n (2 ^ k * (n + 1)) k A₅ 0 σ = A₆ at *
  -- The zero window is untouched.
  have hz : win A₆ n (2 ^ k * (n + 1) + (n + 1)) = 0 := by
    have : win A₆ n (2 ^ k * (n + 1) + (n + 1)) =
        win (UInt32Array.replicate S 0) n (2 ^ k * (n + 1) + (n + 1)) :=
      win_congr fun j _ _ => by
        rw [v₂ j (by lia) (by lia), p₂ j (by lia), f₂ j (by lia) (by lia), l₂ j (by lia)]
    rw [this]
    exact valAt_replicate_zero ..
  -- The division by `2ᵏ`.
  have hsz₆ : A₆.size = S := by rw [v₁, p₁, f₁, l₁]
  obtain ⟨s₁, -, s₃⟩ := scaleLoop_spec n 0 (2 ^ k * (n + 1)) (2 ^ k * (n + 1) + (n + 1)) k
    hn hk hN32 (2 ^ k) A₆ 0 (by rw [hsz₆]; exact hSz) (by rw [hsz₆]; lia) (by rw [hsz₆]; lia)
    (by rw [hsz₆]; lia) (by lia) (by lia) (by lia) hz
    (fun q _ hq => by rw [v₃ q (by lia)]; exact Nat.mod_lt _ hF₀)
  generalize scaleLoop n 0 (2 ^ k * (n + 1)) (2 ^ k * (n + 1) + (n + 1)) k A₆ 0 (2 ^ k) = A₇ at *
  -- The coefficients are those of the square of the pieces.
  have hla := cover a.size.toNat m hm
  have hla₁ : 1 ≤ (a.size.toNat + m - 1) / m := (Nat.le_div_iff_mul_le (by lia)).2 (by lia)
  generalize (a.size.toNat + m - 1) / m = la at *
  have hαL : ∀ i < 2 ^ k, coef A₂ n 0 i = (pieces a m la).getD i 0 := fun i hi => by
    rw [cA i hi]
    rcases coef_pieces a m la (2 ^ k) i hla with h | h
    · rw [← h, ite_eq_left hi]
    · lia
  have hαne : pieces a m la ≠ [] := by
    intro h; have := congrArg List.length h; rw [length_pieces] at this; simp at this; lia
  have hc : ∀ l < 2 ^ k, coef A₇ n 0 l = (polyMul (pieces a m la) (pieces a m la)).getD l 0 := by
    intro l hl
    rw [s₃ l (by lia) (by lia), v₃ l hl]
    rw [← fft_coef (pieces a m la) (pieces a m la) k (32 * n) σ (2 ^ (32 * m)) (F := fermat n) rfl
      hk hσ
      (by rw [length_pieces]; lia) hαne
      (fun x hx => by
        simp only [pieces, List.mem_map, List.mem_range] at hx
        obtain ⟨i, -, rfl⟩ := hx; exact piece_lt ..)
      (fun x hx => by
        simp only [pieces, List.mem_map, List.mem_range] at hx
        obtain ⟨i, -, rfl⟩ := hx; exact piece_lt ..)
      (by rw [← Nat.pow_add, show 32 * m + 32 * m = 64 * m by lia]; exact hbits)
      (by rw [length_pieces]; lia) (by rw [length_pieces]; lia) l hl]
    have hα : ∀ q, sumRange (fun i => coef A₂ n 0 i * 2 ^ (σ * i * rev k q)) (2 ^ k) =
        sumRange (fun i => (pieces a m la).getD i 0 * 2 ^ (σ * i * rev k q)) (2 ^ k) :=
      fun q => sumRange_congr fun i hi => by rw [hαL i hi]
    have hsum : sumRange (fun p => coef A₅ n 0 p * 2 ^ ((2 * (32 * n) - σ) * rev k p * l))
        (2 ^ k) = sumRange (fun p =>
          sumRange (fun i => (pieces a m la).getD i 0 * 2 ^ (σ * i * rev k p)) (2 ^ k) %
            fermat n * (sumRange (fun i => (pieces a m la).getD i 0 * 2 ^ (σ * i * rev k p))
              (2 ^ k) % fermat n) % fermat n * 2 ^ ((2 * (32 * n) - σ) * rev k p * l)) (2 ^ k) :=
      sumRange_congr fun q hq => by
        rw [p₃ q (by lia) (by lia), f₃ q hq, hα]
    rw [hsum]
  -- The value of the coefficients at `2^(32 m)`.
  generalize hZ : polyMul (pieces a m la) (pieces a m la) = Z at hc
  have hZK : Z.length ≤ 2 ^ k := by
    rw [← hZ]; have := length_polyMul (pieces a m la) (pieces a m la) hαne
    rw [length_pieces] at this; lia
  have hab : sumRange (fun i => 2 ^ (32 * ((0 + i) * m)) * coef A₇ n 0 (0 + i)) (2 ^ k) =
      a.toNat * a.toNat := by
    rw [← polyVal_pieces a m la hla, ← polyVal_polyMul, hZ, polyVal_eq_sumRange _ Z _ hZK]
    exact sumRange_congr fun i hi => by
      rw [Nat.zero_add, hc i hi, Nat.mul_comm, ← Nat.pow_mul]; congr 2; lia
  have hablt : a.toNat * a.toNat < 2 ^ (32 * (a.size.toNat + a.size.toNat)) := by
    rw [Nat.mul_add, Nat.pow_add]
    have h₁ : a.toNat < 2 ^ (32 * a.size.toNat) := by rw [USlice.toNat_eq_valAt]; exact valAt_lt ..
    exact Nat.mul_lt_mul'' h₁ h₁
  -- Zeroing the result, and adding the coefficients.
  have hT : (a.size + a.size).toNat = a.size.toNat + a.size.toNat :=
    USize.toNat_add_of_lt (by have := r.size.toNat_lt_size; lia)
  have hrs := r.toNat_size
  have hrst := r.stop_le_size
  have hrle := USize.le_iff_toNat_le.1 r.start_le_stop
  have e₁ := r.start_slice (i := 0) (j := a.size + a.size) (by simp) (by rw [hT]; exact hr)
  have e₂ := r.size_slice (i := 0) (j := a.size + a.size) (by simp) (by rw [hT]; exact hr)
  rw [USize.toNat_zero, Nat.add_zero] at e₁
  rw [USize.toNat_zero, Nat.sub_zero, hT] at e₂
  obtain ⟨z₁, z₂, z₃⟩ := zeroInto_spec (r.slice 0 (a.size + a.size))
  simp only [USlice.array_slice, e₁, e₂] at z₁ z₂ z₃
  generalize zeroInto (r.slice 0 (a.size + a.size)) = R₀ at *
  have hsz₇ : A₇.size = S := by rw [s₁, hsz₆]
  obtain ⟨c₁, c₂, c₃⟩ := recLoop_spec (a.size.toNat + a.size.toNat) m n 0 A₇
    (by rw [hsz₇]; exact hSz) (2 ^ k) R₀ r.start.toNat 0 (by rw [z₁]; exact hrS) (by rw [z₁]; lia)
    (by rw [hsz₇]; lia) (by rw [z₃, Nat.zero_add, hab]; exact hablt)
  refine ⟨by rw [c₁, z₁], fun i hi => ?_, ?_⟩
  · rw [c₂ i (by lia), z₂ i (by lia)]
  · rw [c₃, z₃, Nat.zero_add, hab]

/-! ## The parameters -/

/--
The parameters for `T` limbs and `K = 2ᵏ` pieces: pieces of `m = ⌈T / (K - 1)⌉` limbs, so that
the two operands have at most `K + 1`, and residues of `n` limbs, `2 m + 1` rounded up to a
multiple of `K / 64`, so that the root `2^(64 n / K)` is a power of two.
-/
public def fftParams (T k : Nat) : Nat × Nat :=
  let m := (T + 2 ^ k - 2) / (2 ^ k - 1)
  let q := max 1 (2 ^ k / 64)
  (m, (2 * m + 1 + q - 1) / q * q)

/--
The number of pieces, `2ᵏ`, for `T` limbs: the least `k` with `4ᵏ ≥ 5 T`. From a sweep of
`k = 5, …, 12` at 8192 to 262144 limbs per operand (Zen 3, 2026-10-26), products and squares
alike: this choice is the best at every size measured from 12288 limbs, and within 6% at 8192.
-/
public def fftK (T : Nat) : Nat := min 30 ((Nat.log2 (5 * T - 1) + 2) / 2)

/-- The conditions of `FFTParams`, decidably, with `k + 64 m ≤ 32 n` for the bound. -/
public abbrev FFTCheck (r a b : USlice) (k m n : Nat) : Prop :=
  1 ≤ k ∧ k ≤ 32 ∧ 1 ≤ n ∧ 1 ≤ m ∧ m ≤ n ∧ 2 * (32 * n) % 2 ^ k = 0 ∧ 0 < a.size.toNat ∧
    0 < b.size.toNat ∧ (a.size.toNat + m - 1) / m + (b.size.toNat + m - 1) / m ≤ 2 ^ k + 1 ∧
    k + 64 * m ≤ 32 * n ∧ a.size.toNat + b.size.toNat ≤ r.size.toNat ∧
    (2 * 2 ^ k + 2) * (n + 1) < USize.size ∧ 32 * n < USize.size ∧
    a.array.size < USize.size ∧ b.array.size < USize.size ∧ r.array.size < USize.size

private theorem FFTCheck.params {r a b : USlice} {k m n : Nat} (h : FFTCheck r a b k m n) :
    FFTParams r a b k m n := by
  obtain ⟨h₁, h₂, h₃, h₄, h₅, h₆, h₇, h₈, h₉, h₁₀, h₁₁, h₁₂, h₁₃, h₁₄, h₁₅, h₁₆⟩ := h
  exact ⟨h₁, h₃, h₄, h₅, h₆, h₇, h₈, h₉,
    by rw [← Nat.pow_add]; exact Nat.pow_le_pow_right (by decide) (by lia), h₁₁, h₁₂, h₁₃, h₁₄,
    h₁₅, h₁₆⟩

/-! ## On the library's slices

The rest of the library multiplies the library's slices into new arrays, with values by
`MPN.toNat`: `fftMul` and `fftSqr` take its multiplication for the pointwise products, convert
the slices to `USlice`s and back, and fall back to schoolbook when the parameters do not suit.
-/

/-- The limbs `lo` to `lo + n - 1` of `a`, read as a list, have the value `valAt`. -/
private theorem ofLimbs_take_drop (a : UInt32Array) (lo n : Nat) :
    ofLimbs ((a.toList.drop lo).take n) = a.valAt lo n := by
  have hz : ∀ m lo', a.size ≤ lo' → a.valAt lo' m = 0 := by
    intro m
    induction m with
    | zero => simp
    | succ m ihm =>
      intro lo' h'
      rw [valAt_succ, ihm (lo' + 1) (by lia), getElem!_neg a lo' (by lia)]; rfl
  induction n generalizing lo with
  | zero => simp
  | succ n ih =>
    rcases Nat.lt_or_ge lo a.size with h | h
    · rw [valAt_succ, List.drop_eq_getElem_cons (by simpa using h), List.take_succ_cons,
        ofLimbs_cons, ih (lo + 1), getElem!_eq_getElem _ _ h]
      simp
    · rw [List.drop_eq_nil_of_le (by simpa using h), hz _ lo h]
      simp

/-- The value of a library slice, by `valAt`. -/
public theorem toNat_eq_valAt (s : UInt32Array.Slice) :
    MPN.toNat s = s.array.valAt s.start s.size := by
  rw [MPN.toNat, ← ofLimbs_take_drop]
  congr 1
  rw [Slice.copy, toList_extract, List.extract_eq_take_drop, Slice.size_eq]

/-- The value of an array, by `valAt`. -/
public theorem toNat_array_eq_valAt (a : UInt32Array) :
    MPN.toNat a.toSlice = a.valAt 0 a.size := by
  rw [toNat_toSlice, ← ofLimbs_take_drop, List.drop_zero, List.take_of_length_le (by simp)]

/-- A library slice as a `USlice`, for an array whose size is a `USize`. -/
@[inline, expose] public def toUS (s : UInt32Array.Slice) (h : s.array.size < USize.size) : USlice where
  array := s.array
  start := s.start.toUSize
  stop := s.stop.toUSize
  start_le_stop := USize.le_iff_toNat_le.2 (by
    have := s.start_le_stop; have := s.stop_le_array_size
    rw [Nat.toUSize_eq, Nat.toUSize_eq, USize.toNat_ofNat_of_lt' (by lia),
      USize.toNat_ofNat_of_lt' (by lia)]; exact s.start_le_stop)
  stop_le_size := by
    have := s.stop_le_array_size
    rw [Nat.toUSize_eq, USize.toNat_ofNat_of_lt' (by lia)]; exact this

public theorem toUS_spec (s : UInt32Array.Slice) (h : s.array.size < USize.size) :
    (toUS s h).array = s.array ∧ (toUS s h).start.toNat = s.start ∧
      (toUS s h).size.toNat = s.size ∧ (toUS s h).toNat = MPN.toNat s := by
  have := s.start_le_stop; have := s.stop_le_array_size
  have e₁ : (toUS s h).start.toNat = s.start := by
    show s.start.toUSize.toNat = _
    rw [Nat.toUSize_eq, USize.toNat_ofNat_of_lt' (by lia)]
  have e₂ : (toUS s h).stop.toNat = s.stop := by
    show s.stop.toUSize.toNat = _
    rw [Nat.toUSize_eq, USize.toNat_ofNat_of_lt' (by lia)]
  have e₃ : (toUS s h).size.toNat = s.size := by
    rw [USlice.toNat_size, e₁, e₂, Slice.size_eq]
  exact ⟨rfl, e₁, e₃, by rw [USlice.toNat_eq_valAt, e₁, e₃, toNat_eq_valAt]; rfl⟩

/-- A `USlice` as a library slice. -/
@[inline, expose] public def ofUS (x : USlice) : UInt32Array.Slice :=
  x.array.toSlice x.start.toNat x.stop.toNat

public theorem ofUS_spec (x : USlice) :
    (ofUS x).size = x.size.toNat ∧ MPN.toNat (ofUS x) = x.toNat := by
  have h₁ := USize.le_iff_toNat_le.1 x.start_le_stop
  have h₂ := x.stop_le_size
  have hs : (ofUS x).size = x.size.toNat := by
    rw [ofUS, size_toSlice, USlice.toNat_size]; lia
  refine ⟨hs, ?_⟩
  rw [toNat_eq_valAt, USlice.toNat_eq_valAt, hs, ofUS, array_toSlice, start_toSlice]
  congr 1; lia

/-- The pointwise products by a multiplication of the library's slices. -/
@[inline, expose] public def mulOf {N : Nat}
    (mulRec : (x y : UInt32Array.Slice) → x.size + y.size < N → UInt32Array) : MulN N :=
  fun x y h => mulRec (ofUS x) (ofUS y) (by rw [(ofUS_spec x).1, (ofUS_spec y).1]; exact h)

public theorem isMulN_mulOf {N : Nat}
    (mulRec : (x y : UInt32Array.Slice) → x.size + y.size < N → UInt32Array)
    (hrec : ∀ x y h, (mulRec x y h).size = x.size + y.size ∧
      MPN.toNat (mulRec x y h) = MPN.toNat x * MPN.toNat y) : IsMulN (mulOf mulRec) := by
  intro x y h
  obtain ⟨h₁, h₂⟩ := hrec (ofUS x) (ofUS y) (by rw [(ofUS_spec x).1, (ofUS_spec y).1]; exact h)
  have h₁' : (mulOf mulRec x y h).size = x.size.toNat + y.size.toNat := by
    show (mulRec _ _ _).size = _
    rw [h₁, (ofUS_spec x).1, (ofUS_spec y).1]
  have h₂' : MPN.toNat (mulOf mulRec x y h).toSlice = x.toNat * y.toNat := by
    show MPN.toNat (mulRec _ _ _).toSlice = _
    rw [h₂, (ofUS_spec x).2, (ofUS_spec y).2]
  refine ⟨h₁', ?_⟩
  rw [← h₁', ← toNat_array_eq_valAt]
  exact h₂'

/-- The pointwise squares by a squaring of the library's slices. -/
@[inline, expose] public def sqrOf {N : Nat}
    (sqrRec : (x : UInt32Array.Slice) → x.size < N → UInt32Array) : SqrN N :=
  fun x h => sqrRec (ofUS x) (by rw [(ofUS_spec x).1]; exact h)

public theorem isSqrN_sqrOf {N : Nat}
    (sqrRec : (x : UInt32Array.Slice) → x.size < N → UInt32Array)
    (hrec : ∀ x h, (sqrRec x h).size = x.size + x.size ∧
      MPN.toNat (sqrRec x h) = MPN.toNat x * MPN.toNat x) : IsSqrN (sqrOf sqrRec) := by
  intro x h
  obtain ⟨h₁, h₂⟩ := hrec (ofUS x) (by rw [(ofUS_spec x).1]; exact h)
  have h₁' : (sqrOf sqrRec x h).size = 2 * x.size.toNat := by
    show (sqrRec _ _).size = _
    rw [h₁, (ofUS_spec x).1]; lia
  have h₂' : MPN.toNat (sqrOf sqrRec x h).toSlice = x.toNat * x.toNat := by
    show MPN.toNat (sqrRec _ _).toSlice = _
    rw [h₂, (ofUS_spec x).2]
  refine ⟨h₁', ?_⟩
  rw [← h₁', ← toNat_array_eq_valAt]
  exact h₂'

/--
The product `a b` by the FFT with `2ᵏ` pieces, the parameters of `fftParams`, and `mulRec` for
the pointwise products, into a new array; schoolbook when the parameters do not suit the sizes,
which the dispatcher avoids.
-/
public def fftMul (a b : UInt32Array.Slice) (k : Nat)
    (mulRec : (x y : UInt32Array.Slice) → x.size + y.size < a.size + b.size → UInt32Array) :
    UInt32Array :=
  if h : a.array.size < USize.size ∧ b.array.size < USize.size then
    let r := UInt32Array.replicate (a.size + b.size) 0
    let p := fftParams (a.size + b.size) k
    if FFTCheck r.toUSlice (toUS a h.1) (toUS b h.2) k p.1 p.2 ∧ 2 * p.2 + 2 < a.size + b.size then
      fftMulAt (a.size + b.size) (mulOf mulRec) r.toUSlice (toUS a h.1) (toUS b h.2) k p.1 p.2
    else mulBasecase a b
  else mulBasecase a b

public theorem fftMul_spec (a b : UInt32Array.Slice) (k : Nat)
    (mulRec : (x y : UInt32Array.Slice) → x.size + y.size < a.size + b.size → UInt32Array)
    (hrec : ∀ x y h, (mulRec x y h).size = x.size + y.size ∧
      MPN.toNat (mulRec x y h) = MPN.toNat x * MPN.toNat y) :
    (fftMul a b k mulRec).size = a.size + b.size ∧
      MPN.toNat (fftMul a b k mulRec) = MPN.toNat a * MPN.toNat b := by
  unfold fftMul
  by_cases h : a.array.size < USize.size ∧ b.array.size < USize.size
  · rw [dite_eq_left h]
    dsimp only
    by_cases hc : FFTCheck (UInt32Array.replicate (a.size + b.size) 0).toUSlice (toUS a h.1) (toUS b h.2) k (fftParams (a.size + b.size) k).1
          (fftParams (a.size + b.size) k).2 ∧ 2 * (fftParams (a.size + b.size) k).2 + 2 < a.size + b.size
    · rw [ite_eq_left hc]
      obtain ⟨hc, hN⟩ := hc
      obtain ⟨A₁, A₂, A₃, A₄⟩ := toUS_spec a h.1
      obtain ⟨B₁, B₂, B₃, B₄⟩ := toUS_spec b h.2
      obtain ⟨s₁, -, s₃⟩ := fftMulAt_spec (a.size + b.size) (mulOf mulRec) (isMulN_mulOf mulRec hrec)
        _ _ _ k _ _ hN hc.params
      rw [A₃, B₃, A₄, B₄, start_toUSlice, USize.toNat_zero] at s₃
      simp only [array_toUSlice, size_replicate] at s₁
      refine ⟨s₁, ?_⟩
      rw [toNat_array_eq_valAt, s₁]
      exact s₃
    · rw [ite_eq_right hc]
      exact ⟨size_mulBasecase a b, toNat_mulBasecase a b⟩
  · rw [dite_eq_right h]
    exact ⟨size_mulBasecase a b, toNat_mulBasecase a b⟩

/--
The square `a²` by the FFT with `2ᵏ` pieces, one forward transform, and `sqrRec` for the pointwise
squares, into a new array; schoolbook when the parameters do not suit.
-/
public def fftSqr (a : UInt32Array.Slice) (k : Nat)
    (sqrRec : (x : UInt32Array.Slice) → x.size < a.size → UInt32Array) : UInt32Array :=
  if h : a.array.size < USize.size then
    let r := UInt32Array.replicate (a.size + a.size) 0
    let p := fftParams (a.size + a.size) k
    if FFTCheck r.toUSlice (toUS a h) (toUS a h) k p.1 p.2 ∧ p.2 + 1 < a.size then
      fftSqrAt a.size (sqrOf sqrRec) r.toUSlice (toUS a h) k p.1 p.2
    else mulBasecase a a
  else mulBasecase a a

public theorem fftSqr_spec (a : UInt32Array.Slice) (k : Nat)
    (sqrRec : (x : UInt32Array.Slice) → x.size < a.size → UInt32Array)
    (hrec : ∀ x h, (sqrRec x h).size = x.size + x.size ∧
      MPN.toNat (sqrRec x h) = MPN.toNat x * MPN.toNat x) :
    (fftSqr a k sqrRec).size = a.size + a.size ∧
      MPN.toNat (fftSqr a k sqrRec) = MPN.toNat a * MPN.toNat a := by
  unfold fftSqr
  by_cases h : a.array.size < USize.size
  · rw [dite_eq_left h]
    dsimp only
    by_cases hc : FFTCheck (UInt32Array.replicate (a.size + a.size) 0).toUSlice (toUS a h) (toUS a h) k (fftParams (a.size + a.size) k).1
          (fftParams (a.size + a.size) k).2 ∧ (fftParams (a.size + a.size) k).2 + 1 < a.size
    · rw [ite_eq_left hc]
      obtain ⟨hc, hN⟩ := hc
      obtain ⟨A₁, A₂, A₃, A₄⟩ := toUS_spec a h
      obtain ⟨s₁, -, s₃⟩ := fftSqrAt_spec a.size (sqrOf sqrRec) (isSqrN_sqrOf sqrRec hrec)
        _ _ k _ _ hN hc.params
      rw [A₃, A₄, start_toUSlice, USize.toNat_zero] at s₃
      simp only [array_toUSlice, size_replicate] at s₁
      refine ⟨s₁, ?_⟩
      rw [toNat_array_eq_valAt, s₁]
      exact s₃
    · rw [ite_eq_right hc]
      exact ⟨size_mulBasecase a a, toNat_mulBasecase a a⟩
  · rw [dite_eq_right h]
    exact ⟨size_mulBasecase a a, toNat_mulBasecase a a⟩

end MPN.FFT
