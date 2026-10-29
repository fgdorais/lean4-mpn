/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import MPN.FFT.Transform
public import MPN.FFT.Product
public import MPN.Mul.Toom
public import MPN.Sqr.Karatsuba

/-!
# FFT multiplication

Schönhage–Strassen multiplication on 64-bit limbs: `main`'s `MPN.FFT.Product` on the instance
`fftOps64` of `FFTOps`, whose operations are the in-place loops of `MPN.AddSub` and
`MPN.FFT.Fermat` with `Nat` offsets, with `mulToom` and `sqrKaratsuba` for the pointwise products.
`fftMulAt`, `fftMulModAt` and `fftSqrAt` take `USlice`s; `fftMul`, `fftSqr` and the dispatchers
`MPN.mul` and `MPN.sqr` choose the parameters.
-/

open ScalarArray UInt64Array

namespace MPN.FFT

/-- `main`'s `incrAt_spec` on `UInt64Array`. -/
private theorem incrAt_spec' (arr : UInt64Array) (o len : USize) (h : LoopBound arr o len)
    (j : USize) (c : UInt64) :
    (incrAt arr o len h j c).1.size = arr.size ∧
      (∀ i, (i < o.toNat + j.toNat ∨ o.toNat + len.toNat ≤ i) →
        (incrAt arr o len h j c).1[i]! = arr[i]!) ∧
      (incrAt arr o len h j c).1.valAt (o.toNat + j.toNat) (len.toNat - j.toNat) +
          2 ^ (64 * (len.toNat - j.toNat)) * (incrAt arr o len h j c).2.toNat =
        arr.valAt (o.toNat + j.toNat) (len.toNat - j.toNat) + c.toNat :=
  incrAt_spec arr o len h j c

/-- The value of a window: its low `n` limbs and its top limb. -/
private theorem valAt_top64 (a : UInt64Array) (o n : Nat) :
    a.valAt o (n + 1) = a.valAt o n + 2 ^ (64 * n) * a[o + n]!.toNat := valAt_top a o n

/-- `main`'s `normAt_spec` on `UInt64Array`. -/
private theorem normAt_spec' (arr : UInt64Array) (n o : USize) (h : Win arr n o)
    (hn : 1 ≤ n.toNat) :
    (normAt arr n o h).size = arr.size ∧
      (∀ i, (i < o.toNat ∨ o.toNat + n.toNat + 1 ≤ i) → (normAt arr n o h)[i]! = arr[i]!) ∧
      (normAt arr n o h).valAt o.toNat (n.toNat + 1) = arr.valAt o.toNat (n.toNat + 1) % fermat n.toNat :=
  normAt_spec arr n o h hn

variable (cfg : Config)

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

/-! ## Pieces of slices -/

/-- Piece `i` of `a`: its limbs `i m` to `i m + m - 1`, or fewer at the end. -/
@[expose] public def piece (a : USlice) (m i : Nat) : Nat :=
  FFTOps.piece a.array a.start.toNat a.size.toNat m i

/-- The first `L` pieces of `a`. -/
@[expose] public def pieces (a : USlice) (m L : Nat) : List Nat :=
  FFTOps.pieces a.array a.start.toNat a.size.toNat m L

/-- The pieces of `a` are its digits in base `2^(64 m)`. -/
public theorem polyVal_pieces (a : USlice) (m L : Nat) (hL : a.size.toNat ≤ L * m) :
    polyVal (2 ^ (64 * m)) (pieces a m L) = a.toNat := by
  rw [USlice.toNat_eq_valAt]
  exact FFTOps.polyVal_pieces a.array a.start.toNat a.size.toNat m L hL

public theorem length_pieces (a : USlice) (m L : Nat) : (pieces a m L).length = L :=
  FFTOps.length_pieces ..

public theorem getD_pieces (a : USlice) (m L i : Nat) :
    (pieces a m L).getD i 0 = if i < L then piece a m i else 0 :=
  FFTOps.getD_pieces ..

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
  rw [pieceSl, s₄]
  show _ = a.array.valAt (a.start.toNat + i * m) (min m (a.size.toNat - i * m))
  rcases Nat.le_total (i * m) a.size.toNat with h | h
  · rw [Nat.min_eq_left h]
  · rw [show a.size.toNat - i * m = 0 by lia, Nat.min_zero, valAt_zero, valAt_zero]

/-! ## The operations of `FFTOps` -/

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
  have := normAt_spec' arr n.toUSize d.toUSize w (by lia)
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
    rw [valAt_top64, getElem!_uset, valAt_uset_of _ _ _ _ _ _ (by rw [hdn]; lia)]
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
  obtain ⟨i₁, i₂, i₃⟩ := incrAt_spec' _ d.toUSize (n + 1).toUSize hlb 0 (q.2 + P[2 * n]!)
  simp only [USize.toNat_zero, Nat.add_zero, Nat.sub_zero, hd', hn1, size_uset] at i₁ i₂ i₃
  rw [t₁, hc] at i₃
  generalize incrAt (q.1.uset (d + n).toUSize 0 hidx) d.toUSize (n + 1).toUSize hlb 0
    (q.2 + P[2 * n]!) = q' at *
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
  obtain ⟨i₁, i₂, i₃⟩ := incrAt_spec' q.1 _ _ hlb 0 q.2
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

/-- `addAt` of a range of `src`, when it does not carry out. -/
public def addRangeG (arr : UInt64Array) (o len : Nat) (src : UInt64Array) (so slen : Nat) :
    UInt64Array :=
  (addAt arr o len (sl src so slen)).1

public theorem addRangeG_spec (arr : UInt64Array) (o len : Nat) (src : UInt64Array) (so slen : Nat)
    (hS : arr.size < USize.size) (h : o + len ≤ arr.size) (hsS : src.size < USize.size)
    (hs : so + slen ≤ src.size) (hl : slen ≤ len)
    (hV : arr.valAt o len + src.valAt so slen < 2 ^ (64 * len)) :
    (addRangeG arr o len src so slen).size = arr.size ∧
      (∀ i, (i < o ∨ o + len ≤ i) → (addRangeG arr o len src so slen)[i]! = arr[i]!) ∧
      (addRangeG arr o len src so slen).valAt o len = arr.valAt o len + src.valAt so slen := by
  obtain ⟨-, -, b₃, b₄⟩ := sl_spec src so slen hs hsS
  obtain ⟨a₁, a₂, a₃⟩ := addAt_spec arr o len (sl src so slen) h hS (by rw [b₃]; exact hl)
  rw [b₄] at a₃
  have hc : (addAt arr o len (sl src so slen)).2.toNat = 0 := by
    rcases Nat.eq_zero_or_pos (addAt arr o len (sl src so slen)).2.toNat with e | e
    · exact e
    · have := Nat.mul_le_mul_left (2 ^ (64 * len)) e; lia
  rw [hc, Nat.mul_zero, Nat.add_zero] at a₃
  exact ⟨a₁, a₂, a₃⟩

/-- `zeroInto` with `Nat` offsets. -/
public def zeroRangeG (arr : UInt64Array) (o len : Nat) : UInt64Array := zeroInto (sl arr o len)

public theorem zeroRangeG_spec (arr : UInt64Array) (o len : Nat) (hS : arr.size < USize.size)
    (h : o + len ≤ arr.size) :
    (zeroRangeG arr o len).size = arr.size ∧
      (∀ i, (i < o ∨ o + len ≤ i) → (zeroRangeG arr o len)[i]! = arr[i]!) ∧
      (zeroRangeG arr o len).valAt o len = 0 := by
  obtain ⟨s₁, s₂, s₃, -⟩ := sl_spec arr o len h hS
  obtain ⟨z₁, z₂, z₃⟩ := zeroInto_spec (sl arr o len)
  rw [s₁, s₂, s₃] at *
  exact ⟨z₁, z₂, z₃⟩

/-! ## The instance -/

/-- The operations of `FFTOps` on 64-bit limbs. -/
public instance fftOps64 : FFTOps UInt64Array UInt64 where
  zeros n := UInt64Array.replicate n 0
  size_zeros n := by simp [LimbArray.size]
  val_get_zeros n i := by
    have := valAt_replicate_zero n i 1
    rwa [valAt_one] at this
  addRange := addRangeG
  addRange_spec := addRangeG_spec
  reduce := reduceAt
  reduce_spec := reduceAt_spec
  addCoef := addCoef
  addCoef_spec := addCoef_spec
  zeroRange := zeroRangeG
  zeroRange_spec := zeroRangeG_spec

/-- The pointwise products of the FFT: `mulToom` into `P`. -/
public def mulP64 (cfg : Config) (P arr : UInt64Array) (x y n : Nat) : UInt64Array :=
  mulToom cfg P.toUSlice (sl arr x (n + 1)) (sl arr y (n + 1))

public theorem isMulP64 (n : Nat) : FFTOps.IsMulP (mulP64 cfg) n := by
  intro P arr x y hP hPS hS hx hy
  change P.size = _ at hP; change P.size < _ at hPS; change arr.size < _ at hS
  change _ ≤ arr.size at hx hy
  obtain ⟨-, -, x₃, x₄⟩ := sl_spec arr x (n + 1) hx hS
  obtain ⟨-, -, y₃, y₄⟩ := sl_spec arr y (n + 1) hy hS
  have hPs := size_toUSlice P hPS
  have hx₀ : 0 < (sl arr x (n + 1)).size :=
    USize.lt_iff_toNat_lt.2 (by rw [x₃, USize.toNat_zero]; lia)
  have hy₀ : 0 < (sl arr y (n + 1)).size :=
    USize.lt_iff_toNat_lt.2 (by rw [y₃, USize.toNat_zero]; lia)
  have m₁ := size_mulToom cfg P.toUSlice (sl arr x (n + 1)) (sl arr y (n + 1))
  have m₂ := valAt_mulToom cfg P.toUSlice (sl arr x (n + 1)) (sl arr y (n + 1)) hx₀ hy₀
    (by rw [x₃, y₃, hPs]; lia)
  rw [x₃, y₃, x₄, y₄, start_toUSlice, USize.toNat_zero, show n + 1 + (n + 1) = 2 * n + 2 by lia]
    at m₂
  rw [array_toUSlice] at m₁
  exact ⟨m₁.trans hP, m₂⟩

/-- The pointwise squares of the FFT: `sqrKaratsuba` into `P`. -/
public def sqrP64 (cfg : Config) (P arr : UInt64Array) (x n : Nat) : UInt64Array :=
  sqrKaratsuba cfg P.toUSlice (sl arr x (n + 1))

public theorem isSqrP64 (n : Nat) : FFTOps.IsSqrP (sqrP64 cfg) n := by
  intro P arr x hP hPS hS hx
  change P.size = _ at hP; change P.size < _ at hPS; change arr.size < _ at hS
  change _ ≤ arr.size at hx
  obtain ⟨-, -, x₃, x₄⟩ := sl_spec arr x (n + 1) hx hS
  have hPs := size_toUSlice P hPS
  have hx₀ : 0 < (sl arr x (n + 1)).size :=
    USize.lt_iff_toNat_lt.2 (by rw [x₃, USize.toNat_zero]; lia)
  have m₁ := size_sqrKaratsuba cfg P.toUSlice (sl arr x (n + 1))
  have m₂ := valAt_sqrKaratsuba cfg P.toUSlice (sl arr x (n + 1)) hx₀ (by rw [x₃, hPs]; lia)
  rw [x₃, x₄, start_toUSlice, USize.toNat_zero, show 2 * (n + 1) = 2 * n + 2 by lia] at m₂
  rw [array_toUSlice] at m₁
  exact ⟨m₁.trans hP, m₂⟩

/-- The limbs of a slice are within its array. -/
private theorem sliceBound (a : USlice) :
    a.start.toNat + a.size.toNat ≤ a.array.size := by
  have := a.toNat_size
  have := a.stop_le_size
  have := USize.le_iff_toNat_le.1 a.start_le_stop
  lia

/-! ## The multiplication -/

/--
`a b` into the first `a.size + b.size` limbs of `r`, with `K = 2ᵏ` windows of `n + 1` limbs for
the pieces of `m` limbs of each operand: `FFTOps.fftMulAt`.
-/
public def fftMulAt (cfg : Config) (r a b : USlice) (k m n : Nat) : UInt64Array :=
  FFTOps.fftMulAt (mulP64 cfg) r.array r.start.toNat a.array a.start.toNat a.size.toNat b.array
    b.start.toNat b.size.toNat k m n

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

private theorem FFTParams.gen {r a b : USlice} {k m n : Nat} (hp : FFTParams r a b k m n) :
    FFTOps.FFTParams r.array r.start.toNat a.array a.start.toNat a.size.toNat b.array
      b.start.toNat b.size.toNat k m n := by
  obtain ⟨hk, hn, hm, hmn, hdiv, ha, hb, hpc, hbits, hr, hS, h64, haS, hbS, hrS⟩ := hp
  have := sliceBound r
  have hb₂ : 2 ^ k * 2 ^ (64 * m + 64 * m) ≤ 2 ^ (64 * n) := by
    rw [show 64 * m + 64 * m = 128 * m by lia]; exact hbits
  exact ⟨hk, hn, hm, hmn, hdiv, ha, hb, hpc, hb₂,
    by show _ ≤ r.array.size; lia, hS, h64, haS, hbS, hrS, sliceBound a, sliceBound b⟩

public theorem fftMulAt_spec (r a b : USlice) (k m n : Nat) (hp : FFTParams r a b k m n) :
    (fftMulAt cfg r a b k m n).size = r.array.size ∧
      (∀ i, (i < r.start.toNat ∨ r.start.toNat + a.size.toNat + b.size.toNat ≤ i) →
        (fftMulAt cfg r a b k m n)[i]! = r.array[i]!) ∧
      (fftMulAt cfg r a b k m n).valAt r.start.toNat (a.size.toNat + b.size.toNat) =
        a.toNat * b.toNat := by
  obtain ⟨h₁, h₂, h₃⟩ := FFTOps.fftMulAt_spec (mulP64 cfg) _ _ _ _ _ _ _ _ k m n hp.gen
    (isMulP64 cfg n)
  rw [USlice.toNat_eq_valAt, USlice.toNat_eq_valAt]
  exact ⟨h₁, fun i hi => h₂ i (by lia), h₃⟩

/-! ## The product modulo `β^N - 1` -/

/--
`a b` modulo `2^(64 N) - 1`, for `N = m 2ᵏ`, into the first `N + n + 1` limbs of `r`:
`FFTOps.fftMulModAt`, at about half the cost of a product of the same operands.
-/
public def fftMulModAt (cfg : Config) (r a b : USlice) (k m n : Nat) : UInt64Array :=
  FFTOps.fftMulModAt (mulP64 cfg) r.array r.start.toNat a.array a.start.toNat a.size.toNat b.array
    b.start.toNat b.size.toNat k m n

/-- The parameters of `fftMulModAt` for which it computes `a b` modulo `2^(64 m 2ᵏ) - 1`. -/
public structure FFTModParams (r a b : USlice) (k m n : Nat) : Prop where
  hk : 1 ≤ k
  hn : 1 ≤ n
  hm : 1 ≤ m
  hmn : m ≤ n
  hdiv : 2 * (64 * n) % 2 ^ k = 0
  ha : 0 < a.size.toNat
  hb : 0 < b.size.toNat
  hla : a.size.toNat ≤ m * 2 ^ k
  hlb : b.size.toNat ≤ m * 2 ^ k
  hbits : 2 * 2 ^ k * 2 ^ (128 * m) ≤ 2 ^ (64 * n)
  hr : m * 2 ^ k + n + 1 ≤ r.size.toNat
  hS : (2 * 2 ^ k + 2) * (n + 1) < USize.size
  h64 : 64 * n < USize.size
  haS : a.array.size < USize.size
  hbS : b.array.size < USize.size
  hrS : r.array.size < USize.size

private theorem FFTModParams.gen {r a b : USlice} {k m n : Nat}
    (hp : FFTModParams r a b k m n) :
    FFTOps.FFTModParams r.array r.start.toNat a.array a.start.toNat a.size.toNat b.array
      b.start.toNat b.size.toNat k m n := by
  obtain ⟨hk, hn, hm, hmn, hdiv, ha, hb, hla, hlb, hbits, hr, hS, h64, haS, hbS, hrS⟩ := hp
  have := sliceBound r
  have hb₂ : 2 * 2 ^ k * 2 ^ (64 * m + 64 * m) ≤ 2 ^ (64 * n) := by
    rw [show 64 * m + 64 * m = 128 * m by lia]; exact hbits
  exact ⟨hk, hn, hm, hmn, hdiv, ha, hb, hla, hlb, hb₂, by show _ ≤ r.array.size; lia, hS,
    h64, haS, hbS, hrS, sliceBound a, sliceBound b⟩

public theorem fftMulModAt_spec (r a b : USlice) (k m n : Nat) (hp : FFTModParams r a b k m n) :
    (fftMulModAt cfg r a b k m n).size = r.array.size ∧
      (∀ i, (i < r.start.toNat ∨ r.start.toNat + (m * 2 ^ k + n + 1) ≤ i) →
        (fftMulModAt cfg r a b k m n)[i]! = r.array[i]!) ∧
      (fftMulModAt cfg r a b k m n).valAt r.start.toNat (m * 2 ^ k + n + 1) %
          (2 ^ (64 * (m * 2 ^ k)) - 1) =
        a.toNat * b.toNat % (2 ^ (64 * (m * 2 ^ k)) - 1) := by
  obtain ⟨h₁, h₂, h₃⟩ := FFTOps.fftMulModAt_spec (mulP64 cfg) _ _ _ _ _ _ _ _ k m n hp.gen
    (isMulP64 cfg n)
  rw [USlice.toNat_eq_valAt, USlice.toNat_eq_valAt]
  exact ⟨h₁, h₂, h₃⟩

/-- The conditions of `FFTModParams`, decidably, with `k + 1 + 128 m ≤ 64 n` for the bound. -/
public abbrev FFTModCheck (r a b : USlice) (k m n : Nat) : Prop :=
  1 ≤ k ∧ k ≤ 63 ∧ 1 ≤ n ∧ 1 ≤ m ∧ m ≤ n ∧ 2 * (64 * n) % 2 ^ k = 0 ∧ 0 < a.size.toNat ∧
    0 < b.size.toNat ∧ a.size.toNat ≤ m * 2 ^ k ∧ b.size.toNat ≤ m * 2 ^ k ∧
    k + 1 + 128 * m ≤ 64 * n ∧ m * 2 ^ k + n + 1 ≤ r.size.toNat ∧
    (2 * 2 ^ k + 2) * (n + 1) < USize.size ∧ 64 * n < USize.size ∧
    a.array.size < USize.size ∧ b.array.size < USize.size ∧ r.array.size < USize.size

public theorem FFTModCheck.params {r a b : USlice} {k m n : Nat} (h : FFTModCheck r a b k m n) :
    FFTModParams r a b k m n := by
  obtain ⟨h₁, h₂, h₃, h₄, h₅, h₆, h₇, h₈, h₉, h₁₀, h₁₁, h₁₂, h₁₃, h₁₄, h₁₅, h₁₆, h₁₇⟩ := h
  refine ⟨h₁, h₃, h₄, h₅, h₆, h₇, h₈, h₉, h₁₀, ?_, h₁₂, h₁₃, h₁₄, h₁₅, h₁₆, h₁₇⟩
  rw [show 2 * 2 ^ k = 2 ^ (k + 1) by rw [Nat.pow_succ, Nat.mul_comm], ← Nat.pow_add]
  exact Nat.pow_le_pow_right (by decide) (by lia)

/-- The coefficient size `n` for `fftMulModAt` with `2ᵏ` pieces of `m` limbs. -/
public def fftModN (k m : Nat) : Nat :=
  let q := max 1 (2 ^ k / 128)
  (2 * m + 1 + q - 1) / q * q

/-! ## Squaring -/

/--
`a²` into the first `2 a.size` limbs of `r`, with one forward transform and squares for the
pointwise products: `FFTOps.fftSqrAt`.
-/
public def fftSqrAt (cfg : Config) (r a : USlice) (k m n : Nat) : UInt64Array :=
  FFTOps.fftSqrAt (sqrP64 cfg) r.array r.start.toNat a.array a.start.toNat a.size.toNat k m n

public theorem fftSqrAt_spec (r a : USlice) (k m n : Nat) (hp : FFTParams r a a k m n) :
    (fftSqrAt cfg r a k m n).size = r.array.size ∧
      (∀ i, (i < r.start.toNat ∨ r.start.toNat + a.size.toNat + a.size.toNat ≤ i) →
        (fftSqrAt cfg r a k m n)[i]! = r.array[i]!) ∧
      (fftSqrAt cfg r a k m n).valAt r.start.toNat (a.size.toNat + a.size.toNat) =
        a.toNat * a.toNat := by
  obtain ⟨h₁, h₂, h₃⟩ := FFTOps.fftSqrAt_spec (sqrP64 cfg) _ _ _ _ _ k m n hp.gen
    (isSqrP64 cfg n)
  rw [USlice.toNat_eq_valAt]
  exact ⟨h₁, fun i hi => h₂ i (by lia), h₃⟩

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
public def fftMul (cfg : Config) (r a b : USlice) (k : Nat) : UInt64Array :=
  let p := fftParams (a.size.toNat + b.size.toNat) k
  if FFTCheck r a b k p.1 p.2 then fftMulAt cfg r a b k p.1 p.2 else mulToom cfg r a b

private theorem fftMul_spec (r a b : USlice) (k : Nat) :
    (fftMul cfg r a b k).size = r.array.size ∧
      (∀ i, (i < r.start.toNat ∨ r.start.toNat + a.size.toNat + b.size.toNat ≤ i) →
        (fftMul cfg r a b k)[i]! = r.array[i]!) ∧
      (0 < a.size → 0 < b.size → a.size.toNat + b.size.toNat ≤ r.size.toNat →
        (fftMul cfg r a b k).valAt r.start.toNat (a.size.toNat + b.size.toNat) =
          a.toNat * b.toNat) := by
  rw [fftMul]
  split
  · rename_i h
    obtain ⟨s₁, s₂, s₃⟩ := fftMulAt_spec cfg r a b k _ _ h.params
    exact ⟨s₁, s₂, fun _ _ _ => s₃⟩
  · exact ⟨size_mulToom cfg r a b, getElem!_mulToom cfg r a b, valAt_mulToom cfg r a b⟩

@[simp] public theorem size_fftMul (r a b : USlice) (k : Nat) :
    (fftMul cfg r a b k).size = r.array.size :=
  (fftMul_spec cfg r a b k).1

/-- `fftMul` leaves the limbs of `r` outside the ones it writes unchanged. -/
public theorem getElem!_fftMul (r a b : USlice) (k : Nat) (i : Nat)
    (hi : i < r.start.toNat ∨ r.start.toNat + a.size.toNat + b.size.toNat ≤ i) :
    (fftMul cfg r a b k)[i]! = r.array[i]! :=
  (fftMul_spec cfg r a b k).2.1 i hi

public theorem valAt_fftMul (r a b : USlice) (k : Nat) (ha : 0 < a.size) (hb : 0 < b.size)
    (hr : a.size.toNat + b.size.toNat ≤ r.size.toNat) :
    (fftMul cfg r a b k).valAt r.start.toNat (a.size.toNat + b.size.toNat) = a.toNat * b.toNat :=
  (fftMul_spec cfg r a b k).2.2 ha hb hr

/--
Writes the `2 a.size` limbs of `a²` into `r`, by the FFT with `2ᵏ` pieces, or by `sqrKaratsuba`
when the parameters of `fftParams` do not suit the size.
-/
public def fftSqr (cfg : Config) (r a : USlice) (k : Nat) : UInt64Array :=
  let p := fftParams (a.size.toNat + a.size.toNat) k
  if FFTCheck r a a k p.1 p.2 then fftSqrAt cfg r a k p.1 p.2 else sqrKaratsuba cfg r a

private theorem fftSqr_spec (r a : USlice) (k : Nat) :
    (fftSqr cfg r a k).size = r.array.size ∧
      (∀ i, (i < r.start.toNat ∨ r.start.toNat + 2 * a.size.toNat ≤ i) →
        (fftSqr cfg r a k)[i]! = r.array[i]!) ∧
      (0 < a.size → 2 * a.size.toNat ≤ r.size.toNat →
        (fftSqr cfg r a k).valAt r.start.toNat (2 * a.size.toNat) = a.toNat * a.toNat) := by
  rw [fftSqr]
  split
  · rename_i h
    obtain ⟨s₁, s₂, s₃⟩ := fftSqrAt_spec cfg r a k _ _ h.params
    rw [show 2 * a.size.toNat = a.size.toNat + a.size.toNat by lia]
    exact ⟨s₁, fun i hi => s₂ i (by lia), fun _ _ => s₃⟩
  · exact ⟨size_sqrKaratsuba cfg r a, getElem!_sqrKaratsuba cfg r a, valAt_sqrKaratsuba cfg r a⟩

@[simp] public theorem size_fftSqr (r a : USlice) (k : Nat) :
    (fftSqr cfg r a k).size = r.array.size :=
  (fftSqr_spec cfg r a k).1

/-- `fftSqr` leaves the limbs of `r` outside the ones it writes unchanged. -/
public theorem getElem!_fftSqr (r a : USlice) (k : Nat) (i : Nat)
    (hi : i < r.start.toNat ∨ r.start.toNat + 2 * a.size.toNat ≤ i) :
    (fftSqr cfg r a k)[i]! = r.array[i]! :=
  (fftSqr_spec cfg r a k).2.1 i hi

public theorem valAt_fftSqr (r a : USlice) (k : Nat) (ha : 0 < a.size)
    (hr : 2 * a.size.toNat ≤ r.size.toNat) :
    (fftSqr cfg r a k).valAt r.start.toNat (2 * a.size.toNat) = a.toNat * a.toNat :=
  (fftSqr_spec cfg r a k).2.2 ha hr

end MPN.FFT

namespace MPN

open FFT

variable (cfg : Config)

/--
Writes the `a.size + b.size` limbs of `a b` into `r`, for operands of comparable sizes: by
`fftMul` from `cfg.mulFFT` limbs in the larger operand, or `cfg.mulFFTUnbal` when they differ
by `3 : 2` or more, when the smaller one has `cfg.mulFFTMin` limbs, by `mulToom` otherwise, which
uses the Toom methods, Karatsuba and the schoolbook method by the sizes. It requires
`0 < a.size`, `0 < b.size` and `a.size + b.size ≤ r.size`.
-/
public def mulBal (cfg : Config) (r a b : USlice) : UInt64Array :=
  if (cfg.mulFFT ≤ max a.size.toNat b.size.toNat ∨
      cfg.mulFFTUnbal ≤ max a.size.toNat b.size.toNat ∧
        3 * min a.size.toNat b.size.toNat ≤ 2 * max a.size.toNat b.size.toNat) ∧
      cfg.mulFFTMin ≤ min a.size.toNat b.size.toNat then
    fftMul cfg r a b (fftK (a.size.toNat + b.size.toNat))
  else mulToom cfg r a b

@[simp] public theorem size_mulBal (r a b : USlice) : (mulBal cfg r a b).size = r.array.size := by
  rw [mulBal]; split <;> simp

/-- `mulBal` leaves the limbs of `r` outside the ones it writes unchanged. -/
public theorem getElem!_mulBal (r a b : USlice) (i : Nat)
    (hi : i < r.start.toNat ∨ r.start.toNat + a.size.toNat + b.size.toNat ≤ i) :
    (mulBal cfg r a b)[i]! = r.array[i]! := by
  rw [mulBal]; split
  · exact getElem!_fftMul cfg r a b _ i hi
  · exact getElem!_mulToom cfg r a b i hi

public theorem valAt_mulBal (r a b : USlice) (ha : 0 < a.size) (hb : 0 < b.size)
    (hr : a.size.toNat + b.size.toNat ≤ r.size.toNat) :
    (mulBal cfg r a b).valAt r.start.toNat (a.size.toNat + b.size.toNat) = a.toNat * b.toNat := by
  rw [mulBal]; split
  · exact valAt_fftMul cfg r a b _ ha hb hr
  · exact valAt_mulToom cfg r a b ha hb hr

/-! ## Unbalanced products -/

/--
The products of pieces `i` to `i + cnt - 1` of `a`, of `c` limbs, by `b`, each by `mulBal` into
a new array, added to the region of `T` limbs at `rs` of `arr`, piece `j` from limb `j c` on.
-/
public def chunkLoop (cfg : Config) (T c rs : Nat) (a b : USlice) :
    UInt64Array → Nat → Nat → UInt64Array
  | arr, _, 0 => arr
  | arr, i, cnt + 1 =>
    let P := mulBal cfg
      (UInt64Array.replicate ((FFT.pieceSl a c i).size.toNat + b.size.toNat) 0).toUSlice
      (FFT.pieceSl a c i) b
    chunkLoop cfg T c rs a b
      (addCoef arr rs T (i * c) P 0 ((FFT.pieceSl a c i).size.toNat + b.size.toNat)) (i + 1) cnt

set_option maxHeartbeats 400000 in
public theorem chunkLoop_spec (T c rs : Nat) (a b : USlice) (hc : 1 ≤ c)
    (haS : a.array.size < USize.size) (hb : 0 < b.size) (hab : a.size.toNat + b.size.toNat ≤ T)
    (hTS : T < USize.size) (cnt : Nat) :
    ∀ arr i, arr.size < USize.size → rs + T ≤ arr.size → (i + cnt) * c < a.size.toNat + c →
      arr.valAt rs T + sumRange (fun j => 2 ^ (64 * ((i + j) * c)) *
        (FFT.piece a c (i + j) * b.toNat)) cnt < 2 ^ (64 * T) →
      (chunkLoop cfg T c rs a b arr i cnt).size = arr.size ∧
      (∀ t, (t < rs ∨ rs + T ≤ t) → (chunkLoop cfg T c rs a b arr i cnt)[t]! = arr[t]!) ∧
      (chunkLoop cfg T c rs a b arr i cnt).valAt rs T = arr.valAt rs T +
        sumRange (fun j => 2 ^ (64 * ((i + j) * c)) * (FFT.piece a c (i + j) * b.toNat)) cnt := by
  induction cnt with
  | zero => intro arr i _ _ _ _; exact ⟨rfl, fun _ _ => rfl, by simp [chunkLoop]⟩
  | succ cnt ih =>
    intro arr i hS hT hcov hsum
    rw [sumRange_succ_left] at hsum ⊢
    simp only [Nat.add_zero] at hsum ⊢
    have hs' : sumRange (fun j => 2 ^ (64 * ((i + (j + 1)) * c)) *
        (FFT.piece a c (i + (j + 1)) * b.toNat)) cnt = sumRange (fun j =>
          2 ^ (64 * ((i + 1 + j) * c)) * (FFT.piece a c (i + 1 + j) * b.toNat)) cnt :=
      sumRange_congr fun j _ => by rw [show i + (j + 1) = i + 1 + j by lia]
    rw [hs'] at hsum ⊢
    rw [chunkLoop]
    -- The product of piece `i` by `b`.
    obtain ⟨p₁, p₂⟩ := FFT.pieceSl_spec a c i haS
    have hic : i * c < a.size.toNat := by
      have := Nat.mul_le_mul_right c (show i + 1 ≤ i + (cnt + 1) by lia)
      rw [Nat.add_mul, Nat.one_mul] at this; lia
    have hlen : (FFT.pieceSl a c i).size.toNat + b.size.toNat < USize.size := by
      rw [p₁]; lia
    have hrep := size_toUSlice (UInt64Array.replicate ((FFT.pieceSl a c i).size.toNat +
      b.size.toNat) 0) (by rw [size_replicate]; exact hlen)
    simp only [size_replicate] at hrep
    have hv := valAt_mulBal cfg (UInt64Array.replicate ((FFT.pieceSl a c i).size.toNat +
      b.size.toNat) 0).toUSlice (FFT.pieceSl a c i) b
      (USize.lt_iff_toNat_lt.2 (by rw [p₁, USize.toNat_zero]; lia)) hb
      (by rw [hrep]; exact Nat.le_refl _)
    have hsz := size_mulBal cfg (UInt64Array.replicate ((FFT.pieceSl a c i).size.toNat +
      b.size.toNat) 0).toUSlice (FFT.pieceSl a c i) b
    rw [start_toUSlice, USize.toNat_zero, p₂] at hv
    rw [array_toUSlice, size_replicate] at hsz
    generalize mulBal cfg (UInt64Array.replicate ((FFT.pieceSl a c i).size.toNat + b.size.toNat)
      0).toUSlice (FFT.pieceSl a c i) b = P at *
    -- Added from limb `i c` on.
    obtain ⟨c₁, c₂, c₃⟩ := addCoef_spec arr rs T (i * c) P 0
      ((FFT.pieceSl a c i).size.toNat + b.size.toNat) hS hT (by lia) (by rw [hsz]; exact hlen)
      (by rw [hsz]; lia) (by rw [hv]; lia)
    rw [hv] at c₃
    generalize addCoef arr rs T (i * c) P 0 ((FFT.pieceSl a c i).size.toNat + b.size.toNat) = A
      at *
    obtain ⟨i₁, i₂, i₃⟩ := ih A (i + 1) (by rw [c₁]; exact hS) (by rw [c₁]; exact hT) (by lia)
      (by rw [c₃]; lia)
    refine ⟨i₁.trans c₁, fun t ht => by rw [i₂ t ht, c₂ t ht], ?_⟩
    rw [i₃, c₃]
    lia

/--
`a b` for `b.size ≤ a.size`, by `mulBal` on the pieces of `a` of `b.size` limbs, the products
added into the zeroed limbs of `r`, like GMP's `mpn_mul` on unbalanced operands.
-/
public def mulChunked (cfg : Config) (r a b : USlice) : UInt64Array :=
  chunkLoop cfg (a.size.toNat + b.size.toNat) b.size.toNat r.start.toNat a b
    (zeroInto (r.slice 0 (a.size + b.size))) 0 ((a.size.toNat + b.size.toNat - 1) / b.size.toNat)

private theorem mulChunked_spec (r a b : USlice) (hb : 0 < b.size)
    (hr : a.size.toNat + b.size.toNat ≤ r.size.toNat) (haS : a.array.size < USize.size)
    (hrS : r.array.size < USize.size) :
    (mulChunked cfg r a b).size = r.array.size ∧
      (∀ i, (i < r.start.toNat ∨ r.start.toNat + a.size.toNat + b.size.toNat ≤ i) →
        (mulChunked cfg r a b)[i]! = r.array[i]!) ∧
      (mulChunked cfg r a b).valAt r.start.toNat (a.size.toNat + b.size.toNat) =
        a.toNat * b.toNat := by
  have hb' := USize.lt_iff_toNat_lt.1 hb
  rw [USize.toNat_zero] at hb'
  -- The number of pieces covers `a`, and no more.
  generalize hL : (a.size.toNat + b.size.toNat - 1) / b.size.toNat = L
  have hL₁ : a.size.toNat ≤ L * b.size.toNat := by
    have h₁ := Nat.div_add_mod (a.size.toNat + b.size.toNat - 1) b.size.toNat
    have h₂ := Nat.mod_lt (a.size.toNat + b.size.toNat - 1) hb'
    rw [hL, Nat.mul_comm] at h₁
    lia
  have hL₂ : L * b.size.toNat < a.size.toNat + b.size.toNat := by
    rw [← hL]
    exact Nat.lt_of_le_of_lt (Nat.div_mul_le_self _ _) (by lia)
  -- The sum of the products of the pieces is `a b`.
  have hab : sumRange (fun j => 2 ^ (64 * ((0 + j) * b.size.toNat)) *
      (FFT.piece a b.size.toNat (0 + j) * b.toNat)) L = a.toNat * b.toNat := by
    rw [← FFT.polyVal_pieces a b.size.toNat L hL₁,
      polyVal_eq_sumRange _ _ L (by rw [FFT.length_pieces]; exact Nat.le_refl _),
      sumRange_mul_right]
    exact sumRange_congr fun j hj => by
      rw [FFT.getD_pieces, ite_eq_left hj, Nat.zero_add, ← Nat.pow_mul,
        show 64 * b.size.toNat * j = 64 * (j * b.size.toNat) by lia]
      grind
  have hablt : a.toNat * b.toNat < 2 ^ (64 * (a.size.toNat + b.size.toNat)) := by
    rw [Nat.mul_add, Nat.pow_add]
    have h₁ : a.toNat < 2 ^ (64 * a.size.toNat) := by rw [USlice.toNat_eq_valAt]; exact valAt_lt ..
    have h₂ : b.toNat < 2 ^ (64 * b.size.toNat) := by rw [USlice.toNat_eq_valAt]; exact valAt_lt ..
    exact Nat.mul_lt_mul'' h₁ h₂
  -- Zeroing the result, and adding the products.
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
  rw [mulChunked, hL]
  generalize zeroInto (r.slice 0 (a.size + b.size)) = R₀ at *
  obtain ⟨c₁, c₂, c₃⟩ := chunkLoop_spec cfg (a.size.toNat + b.size.toNat) b.size.toNat r.start.toNat
    a b (by lia) haS hb (Nat.le_refl _) (by have := r.size.toNat_lt_size; lia) L R₀ 0
    (by rw [z₁]; exact hrS) (by rw [z₁]; lia) (by lia) (by rw [z₃, Nat.zero_add, hab]; exact hablt)
  refine ⟨by rw [c₁, z₁], fun i hi => ?_, ?_⟩
  · rw [c₂ i (by lia), z₂ i (by lia)]
  · rw [c₃, z₃, Nat.zero_add, hab]

/-- `mul` for `b.size ≤ a.size`. -/
public def mulU (cfg : Config) (r a b : USlice) : UInt64Array :=
  if cfg.mulUnbalanced ≤ b.size.toNat ∧ 2 * b.size.toNat ≤ a.size.toNat ∧
      (b.size.toNat < cfg.mulChunkMax ∨ a.size.toNat < cfg.mulFFTUnbal) ∧
      a.size.toNat + b.size.toNat ≤ r.size.toNat ∧
      a.array.size < USize.size ∧ r.array.size < USize.size then
    mulChunked cfg r a b
  else mulBal cfg r a b

private theorem mulU_spec (r a b : USlice) :
    (mulU cfg r a b).size = r.array.size ∧
      (∀ i, (i < r.start.toNat ∨ r.start.toNat + a.size.toNat + b.size.toNat ≤ i) →
        (mulU cfg r a b)[i]! = r.array[i]!) ∧
      (0 < a.size → 0 < b.size → a.size.toNat + b.size.toNat ≤ r.size.toNat →
        (mulU cfg r a b).valAt r.start.toNat (a.size.toNat + b.size.toNat) =
          a.toNat * b.toNat) := by
  rw [mulU]
  split
  · rename_i h
    have h₁ := h.1
    have := cfg.one_le_mulUnbalanced
    have hb : 0 < b.size := USize.lt_iff_toNat_lt.2 (by rw [USize.toNat_zero]; lia)
    obtain ⟨s₁, s₂, s₃⟩ := mulChunked_spec cfg r a b hb h.2.2.2.1 h.2.2.2.2.1 h.2.2.2.2.2
    exact ⟨s₁, s₂, fun _ _ _ => s₃⟩
  · exact ⟨size_mulBal cfg r a b, getElem!_mulBal cfg r a b, valAt_mulBal cfg r a b⟩

/--
Writes the `a.size + b.size` limbs of `a b` into `r`: by `mulChunked` when the larger operand
has at least twice the limbs of the smaller, which has at least `cfg.mulUnbalanced` limbs, and less
than `cfg.mulChunkMax` unless the larger one is below `cfg.mulFFTUnbal`; by `mulBal` otherwise. It
requires `0 < a.size`, `0 < b.size` and `a.size + b.size ≤ r.size`.
-/
public def mul (cfg : Config) (r a b : USlice) : UInt64Array :=
  if b.size ≤ a.size then mulU cfg r a b else mulU cfg r b a

@[simp] public theorem size_mul (r a b : USlice) : (mul cfg r a b).size = r.array.size := by
  rw [mul]; split <;> exact (mulU_spec cfg ..).1

/-- `mul` leaves the limbs of `r` outside the ones it writes unchanged. -/
public theorem getElem!_mul (r a b : USlice) (i : Nat)
    (hi : i < r.start.toNat ∨ r.start.toNat + a.size.toNat + b.size.toNat ≤ i) :
    (mul cfg r a b)[i]! = r.array[i]! := by
  rw [mul]; split
  · exact (mulU_spec cfg r a b).2.1 i hi
  · exact (mulU_spec cfg r b a).2.1 i (by lia)

public theorem valAt_mul (r a b : USlice) (ha : 0 < a.size) (hb : 0 < b.size)
    (hr : a.size.toNat + b.size.toNat ≤ r.size.toNat) :
    (mul cfg r a b).valAt r.start.toNat (a.size.toNat + b.size.toNat) = a.toNat * b.toNat := by
  rw [mul]; split
  · exact (mulU_spec cfg r a b).2.2 ha hb hr
  · rw [Nat.add_comm, Nat.mul_comm]; exact (mulU_spec cfg r b a).2.2 hb ha (by lia)

/--
Writes the `2 a.size` limbs of `a²` into `r`: by `fftSqr` from `cfg.sqrFFT` limbs, by
`sqrToom` below. It requires
`0 < a.size` and `2 a.size ≤ r.size`.
-/
public def sqr (cfg : Config) (r a : USlice) : UInt64Array :=
  if cfg.sqrFFT ≤ a.size.toNat then fftSqr cfg r a (fftK (2 * a.size.toNat))
  else sqrToom cfg r a

@[simp] public theorem size_sqr (r a : USlice) : (sqr cfg r a).size = r.array.size := by
  rw [sqr]; split <;> simp

/-- `sqr` leaves the limbs of `r` outside the ones it writes unchanged. -/
public theorem getElem!_sqr (r a : USlice) (i : Nat)
    (hi : i < r.start.toNat ∨ r.start.toNat + 2 * a.size.toNat ≤ i) :
    (sqr cfg r a)[i]! = r.array[i]! := by
  rw [sqr]; split
  · exact getElem!_fftSqr cfg r a _ i hi
  · exact getElem!_sqrToom cfg r a i hi

public theorem valAt_sqr (r a : USlice) (ha : 0 < a.size) (hr : 2 * a.size.toNat ≤ r.size.toNat) :
    (sqr cfg r a).valAt r.start.toNat (2 * a.size.toNat) = a.toNat * a.toNat := by
  rw [sqr]; split
  · exact valAt_fftSqr cfg r a _ ha hr
  · exact valAt_sqrToom cfg r a ha hr

end MPN
