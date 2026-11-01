/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import MPN.AddSubW
public import MPN.FFT.Product

/-!
# The operations of the FFT over `WordArray`

The operations of `MPN.FFT.FFTOps` beyond `zeros`, for any `WordArray`, in place on the windows
they write. `addRange` and `zeroRange` are the kernels `addIntoK` and `zeroIntoK` of the Toom
methods. `addCoefK` adds a coefficient to a region from its limb `off` on, with `addIntoK` on the
part of the region from there. `reduceK` writes the residue modulo `2^(w n) + 1` of a pointwise
product `P` of `2 n + 2` limbs: `P_lo - P_mid` in one pass over the window, reading both halves
of `P`, then `P_hi` and the borrow with `incrAt`, and `normAt`. Each checks its bounds; otherwise
it writes the value of its specification with `writeNat`, which never happens.
-/

namespace MPN.WordArray

open Toom LimbArray FFT FFT.WinOps

variable {A L : Type} [LA : LimbArray A L] [R : WordArray A L] [F : WordFolds A L]

/-! ## Adding and clearing ranges -/

/-- `addIntoK` as `FFTOps.addRange`. -/
public theorem addRange_spec (arr : A) (o len : Nat) (src : A) (so slen : Nat)
    (_ : LA.size arr < USize.size) (h : o + len ≤ LA.size arr) (_ : LA.size src < USize.size)
    (_ : so + slen ≤ LA.size src) (_ : slen ≤ len)
    (hV : valAt arr o len + valAt src so slen < 2 ^ (LA.w * len)) :
    LA.size (addIntoK arr o len src so slen) = LA.size arr ∧
      (∀ i, (i < o ∨ o + len ≤ i) → LA.get (addIntoK arr o len src so slen) i = LA.get arr i) ∧
      valAt (addIntoK arr o len src so slen) o len = valAt arr o len + valAt src so slen :=
  have s := addIntoK_spec arr o len src so slen h hV
  ⟨s.1.1, s.1.2, s.2⟩

/-- `zeroIntoK` as `FFTOps.zeroRange`. -/
public theorem zeroRange_spec (arr : A) (o len : Nat) (_ : LA.size arr < USize.size)
    (h : o + len ≤ LA.size arr) :
    LA.size (zeroIntoK arr o len) = LA.size arr ∧
      (∀ i, (i < o ∨ o + len ≤ i) → LA.get (zeroIntoK arr o len) i = LA.get arr i) ∧
      valAt (zeroIntoK arr o len) o len = 0 :=
  have s := zeroIntoK_spec arr o len h
  ⟨s.1.1, s.1.2, s.2⟩

/-! ## Adding a coefficient -/

/--
Adds the `len₀` limbs of `src` from `so` on to the region of `T` limbs of `arr` from `o` on, from
its limb `off` on, with the carry out into the rest of the region: only the limbs of `src` inside
the region are added.
-/
public def addCoefK (arr : A) (o T off : Nat) (src : A) (so len₀ : Nat) : A :=
  addIntoK arr (o + off) (T - off) src so (min len₀ (T - off))

public theorem addCoefK_spec (arr : A) (o T off : Nat) (src : A) (so len₀ : Nat)
    (_ : LA.size arr < USize.size) (hT : o + T ≤ LA.size arr) (hoff : off ≤ T)
    (_ : LA.size src < USize.size) (_ : so + len₀ ≤ LA.size src)
    (hV : valAt arr o T + 2 ^ (LA.w * off) * valAt src so len₀ < 2 ^ (LA.w * T)) :
    LA.size (addCoefK arr o T off src so len₀) = LA.size arr ∧
      (∀ i, (i < o ∨ o + T ≤ i) → LA.get (addCoefK arr o T off src so len₀) i = LA.get arr i) ∧
      valAt (addCoefK arr o T off src so len₀) o T =
        valAt arr o T + 2 ^ (LA.w * off) * valAt src so len₀ := by
  have hsplitT : 2 ^ (LA.w * T) = 2 ^ (LA.w * off) * 2 ^ (LA.w * (T - off)) := by
    rw [← Nat.pow_add, ← Nat.mul_add, Nat.add_sub_cancel' hoff]
  have hsplit : ∀ x : A,
      valAt x o T = valAt x o off + 2 ^ (LA.w * off) * valAt x (o + off) (T - off) := by
    intro x; rw [← valAt_add, Nat.add_sub_cancel' hoff]
  rw [hsplit arr, hsplitT] at hV
  -- The part of the region from `off` on, plus the source, fits.
  have hfit : valAt arr (o + off) (T - off) + valAt src so len₀ < 2 ^ (LA.w * (T - off)) := by
    exact Nat.lt_of_mul_lt_mul_left (a := 2 ^ (LA.w * off)) (by rw [Nat.mul_add]; lia)
  have hS' : valAt src so (min len₀ (T - off)) = valAt src so len₀ := by
    rcases Nat.le_total len₀ (T - off) with h | h
    · rw [Nat.min_eq_left h]
    · rw [Nat.min_eq_right h]
      have e := valAt_add src so (T - off) (len₀ - (T - off))
      rw [Nat.add_sub_cancel' h] at e
      rcases Nat.eq_zero_or_pos (valAt src (so + (T - off)) (len₀ - (T - off))) with e₀ | e₀
      · rw [e, e₀, Nat.mul_zero, Nat.add_zero]
      · have := Nat.mul_le_mul_left (2 ^ (LA.w * (T - off))) e₀; lia
  obtain ⟨⟨w₁, w₂⟩, w₃⟩ := addIntoK_spec arr (o + off) (T - off) src so (min len₀ (T - off))
    (by lia) (by rw [hS']; exact hfit)
  rw [hS'] at w₃
  unfold addCoefK
  refine ⟨w₁, fun i hi => w₂ i (by lia), ?_⟩
  have hlo : valAt (addIntoK arr (o + off) (T - off) src so (min len₀ (T - off))) o off =
      valAt arr o off := valAt_congr _ fun i _ _ => w₂ i (by lia)
  rw [hsplit, hsplit arr, hlo, w₃, Nat.mul_add, Nat.add_assoc]

/-! ## The residue of a pointwise product -/

private theorem toNat_toUSize'' {n : Nat} (h : n < 4294967295) : n.toUSize.toNat = n := by
  rw [Nat.toUSize_eq, USize.toNat_ofNat_of_lt' (by have := USize.size_eq; lia)]

/-- The bounds of `reduceK`, from its checks. -/
public structure ReduceOK (arr : A) (n d : Nat) (P : A) : Prop where
  hn : n.toUSize.toNat = n
  hd : d.toUSize.toNat = d
  hn1 : (n + 1).toUSize.toNat = n + 1
  hdn : (d + n).toUSize.toNat = d + n
  h2n : (2 * n).toUSize.toNat = 2 * n
  hw : d + n + 1 ≤ LA.size arr
  hS : LA.size arr < 4294967295
  hP : 2 * n + 2 ≤ LA.size P
  hPS : LA.size P < 4294967295

omit R F in
public theorem reduceOK_of {arr P : A} {n d : Nat}
    (h : winOK arr d (n + 1) = true ∧ winOK P 0 (2 * n + 2) = true) : ReduceOK arr n d P := by
  simp only [winOK, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨h₁, h₂⟩, h₃, h₄⟩ := h
  exact ⟨toNat_toUSize'' (by lia), toNat_toUSize'' (by lia), toNat_toUSize'' (by lia),
    toNat_toUSize'' (by lia), toNat_toUSize'' (by lia), by lia, h₂, by lia, h₄⟩

namespace ReduceOK

variable {arr P : A} {n d : Nat}

omit R F in
public theorem lo (h : ReduceOK arr n d P) : LoopBound P 0 n.toUSize := by
  have := h.hP; have := h.hPS; have := USize.le_size
  constructor <;> simp only [USize.toNat_zero, h.hn] <;> lia

omit R F in
public theorem hi (h : ReduceOK arr n d P) : LoopBound P n.toUSize n.toUSize := by
  have := h.hP; have := h.hPS; have := USize.le_size
  constructor <;> simp only [h.hn] <;> lia

omit R F in
public theorem dn (h : ReduceOK arr n d P) : LoopBound arr d.toUSize n.toUSize := by
  have := h.hw; have := h.hS; have := USize.le_size
  constructor <;> simp only [h.hn, h.hd] <;> lia

omit R F in
public theorem idx2n (h : ReduceOK arr n d P) : (2 * n).toUSize.toNat < LA.size P := by
  have := h.hP; rw [h.h2n]; lia

omit R F in
public theorem idxTop (h : ReduceOK arr n d P) {a : A} (ha : LA.size a = LA.size arr) :
    (d + n).toUSize.toNat < LA.size a := by
  have := h.hw; rw [h.hdn, ha]; lia

omit R F in
public theorem lb1 (h : ReduceOK arr n d P) {a : A} (ha : LA.size a = LA.size arr) :
    LoopBound a d.toUSize (n + 1).toUSize := by
  have := h.hw; have := h.hS; have := USize.le_size
  constructor <;> simp only [h.hn1, h.hd, ha] <;> lia

omit R F in
public theorem window (h : ReduceOK arr n d P) {a : A} (ha : LA.size a = LA.size arr) :
    FFT.Win a n.toUSize d.toUSize := by
  have := h.hw; have := h.hS; have := USize.le_size
  constructor <;> simp only [h.hn, h.hd, ha] <;> lia

end ReduceOK

/--
Writes `P % F` into the window at `d`, for `P` of `2 n + 2` limbs: `P_lo - P_mid + P_hi`, with the
borrow of `P_lo - P_mid` and the limb `P_hi` added by `incrAt`, then `normAt`.
-/
public def reduceK (arr : A) (n d : Nat) (P : A) : A :=
  if h : winOK arr d (n + 1) = true ∧ winOK P 0 (2 * n + 2) = true then
    have hb := reduceOK_of h
    F.foldThen n.toUSize (subNStep A P 0 P n.toUSize n.toUSize hb.lo hb.hi) arr d.toUSize hb.dn 0
      R.b0 fun a ha c =>
        let c := R.add (R.unB c) (R.uget P (2 * n).toUSize hb.idx2n)
        let a₁ := R.uset a (d + n).toUSize R.zero (hb.idxTop ha)
        let a₂ := (FFT.incrAt a₁ d.toUSize (n + 1).toUSize
          (hb.lb1 (by rw [R.size_uset, ha])) 0 c).1
        FFT.normAt a₂ n.toUSize d.toUSize
          (hb.window (by rw [(FFT.incrAt_spec ..).1, R.size_uset, ha]))
  else writeNat arr d (n + 1) (valAt P 0 (2 * n + 2) % fermatW LA.w n)

/-- The value of `reduceK`: `P_lo - P_mid + P_hi`, plus a multiple of `F`. -/
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

omit R F in
/-- The value of a window: its low `n` limbs and its top limb. -/
private theorem valAt_top' (a : A) (o n : Nat) :
    valAt a o (n + 1) = valAt a o n + 2 ^ (LA.w * n) * LA.val (LA.get a (o + n)) := by
  rw [valAt_add, valAt_one]

omit F in
/-- What follows the first pass of `reduceK`, on any array and borrow that it may return. -/
private theorem reduce_aux (arr : A) (n d : Nat) (P : A) (hb : ReduceOK arr n d P) (hn : 1 ≤ n)
    (hPv : valAt P 0 (2 * n + 2) ≤ 2 ^ (LA.w * n) * 2 ^ (LA.w * n))
    (a : A) (ha : LA.size a = LA.size arr) (c : L)
    (a₂ : ∀ i, (i < d ∨ d + n ≤ i) → LA.get a i = LA.get arr i)
    (a₃ : valAt a d n + valAt P n n = valAt P 0 n + 2 ^ (LA.w * n) * LA.val (R.unB c)) :
    LA.size (FFT.normAt (FFT.incrAt (R.uset a (d + n).toUSize R.zero (hb.idxTop ha)) d.toUSize
        (n + 1).toUSize (hb.lb1 (by rw [R.size_uset, ha])) 0
        (R.add (R.unB c) (R.uget P (2 * n).toUSize hb.idx2n))).1 n.toUSize d.toUSize
          (hb.window (by rw [(FFT.incrAt_spec ..).1, R.size_uset, ha]))) = LA.size arr ∧
      (∀ i, (i < d ∨ d + n + 1 ≤ i) →
        LA.get (FFT.normAt (FFT.incrAt (R.uset a (d + n).toUSize R.zero (hb.idxTop ha))
          d.toUSize (n + 1).toUSize (hb.lb1 (by rw [R.size_uset, ha])) 0
          (R.add (R.unB c) (R.uget P (2 * n).toUSize hb.idx2n))).1 n.toUSize d.toUSize
            (hb.window (by rw [(FFT.incrAt_spec ..).1, R.size_uset, ha]))) i = LA.get arr i) ∧
      win (FFT.normAt (FFT.incrAt (R.uset a (d + n).toUSize R.zero (hb.idxTop ha))
          d.toUSize (n + 1).toUSize (hb.lb1 (by rw [R.size_uset, ha])) 0
          (R.add (R.unB c) (R.uget P (2 * n).toUSize hb.idx2n))).1 n.toUSize d.toUSize
            (hb.window (by rw [(FFT.incrAt_spec ..).1, R.size_uset, ha]))) n d =
        valAt P 0 (2 * n + 2) % fermatW LA.w n := by
  have hB4 := four_le (R := R)
  have hdn := hb.hdn
  have hd' := hb.hd
  have hn' := hb.hn
  have hn1 := hb.hn1
  -- The top limb, cleared.
  have t₁ : valAt (R.uset a (d + n).toUSize R.zero (hb.idxTop ha)) d (n + 1) = valAt a d n := by
    rw [valAt_top', R.get_uset, valAt_uset_of _ _ _ _ _ _ (by rw [hdn]; lia)]
    simp only [hdn, ↓reduceIte, R.val_zero, Nat.mul_zero, Nat.add_zero]
  -- `P` in three parts: `P_lo`, `P_mid` and the top limbs.
  have hPv' : valAt P 0 (2 * n + 2) = valAt P 0 n + 2 ^ (LA.w * n) * valAt P n n +
      2 ^ (LA.w * n) * 2 ^ (LA.w * n) * (LA.val (LA.get P (2 * n)) +
        2 ^ LA.w * LA.val (LA.get P (2 * n + 1))) := by
    have e₁ := valAt_add P 0 n (n + 2)
    have e₂ := valAt_add P n n 2
    have e₃ := valAt_succ P (n + n) 1
    have e₄ := valAt_one P (n + n + 1)
    rw [show n + (n + 2) = 2 * n + 2 by lia, Nat.zero_add] at e₁
    rw [e₂, e₃, e₄, show n + n = 2 * n by lia] at e₁
    rw [e₁, Nat.mul_add, Nat.mul_add, Nat.mul_add, ← Nat.pow_add, ← Nat.mul_add,
      show LA.w * n + LA.w * n = LA.w * (2 * n) by lia]
    rw [show LA.w * (2 * n) = LA.w * n + LA.w * n by lia, Nat.pow_add]
    lia
  have hB : 1 ≤ 2 ^ (LA.w * n) := Nat.one_le_two_pow
  have hBB : 1 ≤ 2 ^ (LA.w * n) * 2 ^ (LA.w * n) := Nat.mul_le_mul hB hB
  have hhi : LA.val (LA.get P (2 * n)) + 2 ^ LA.w * LA.val (LA.get P (2 * n + 1)) ≤ 1 := by
    rcases Nat.lt_or_ge (LA.val (LA.get P (2 * n)) +
      2 ^ LA.w * LA.val (LA.get P (2 * n + 1))) 2 with e | e
    · lia
    · have := Nat.mul_le_mul_left (2 ^ (LA.w * n) * 2 ^ (LA.w * n)) e; lia
  have hP₁ : LA.val (LA.get P (2 * n + 1)) = 0 := by
    rcases Nat.eq_zero_or_pos (LA.val (LA.get P (2 * n + 1))) with e | e
    · exact e
    · have := Nat.mul_le_mul_left (2 ^ LA.w) e; lia
  simp only [hP₁, Nat.mul_zero, Nat.add_zero] at hPv' hhi
  have hc₁ : LA.val (R.unB c) ≤ 1 := by
    rcases Nat.lt_or_ge (LA.val (R.unB c)) 2 with e | e
    · lia
    · have := Nat.mul_le_mul_left (2 ^ (LA.w * n)) e
      have := valAt_lt a d n
      have := valAt_lt P n n
      lia
  have hP2 : R.uget P (2 * n).toUSize hb.idx2n = LA.get P (2 * n) := by
    rw [R.uget_eq, hb.h2n]
  have hc : LA.val (R.add (R.unB c) (R.uget P (2 * n).toUSize hb.idx2n)) =
      LA.val (R.unB c) + LA.val (LA.get P (2 * n)) := by
    rw [R.val_add, hP2, Nat.mod_eq_of_lt (by lia)]
  -- The increment by the borrow and `P_hi`.
  obtain ⟨i₁, i₂, i₃⟩ := FFT.incrAt_spec (R.uset a (d + n).toUSize R.zero (hb.idxTop ha))
    d.toUSize (n + 1).toUSize (hb.lb1 (by rw [R.size_uset, ha])) 0
    (R.add (R.unB c) (R.uget P (2 * n).toUSize hb.idx2n))
  simp only [USize.toNat_zero, Nat.add_zero, Nat.sub_zero, hd', hn1, R.size_uset] at i₁ i₂ i₃
  rw [t₁, hc] at i₃
  generalize FFT.incrAt (R.uset a (d + n).toUSize R.zero (hb.idxTop ha)) d.toUSize
    (n + 1).toUSize (hb.lb1 (by rw [R.size_uset, ha])) 0
    (R.add (R.unB c) (R.uget P (2 * n).toUSize hb.idx2n)) = q at *
  -- No carry out of the window.
  have hq := valAt_lt a d n
  have hB1 : 2 ^ (LA.w * (n + 1)) = 2 ^ (LA.w * n) * 2 ^ LA.w := by
    rw [Nat.mul_succ, Nat.pow_add]
  have hc' : LA.val q.2 = 0 := by
    rcases Nat.eq_zero_or_pos (LA.val q.2) with e | e
    · exact e
    · have := Nat.mul_le_mul_left (2 ^ (LA.w * (n + 1))) e
      have : 2 ^ (LA.w * n) * 2 ≤ 2 ^ (LA.w * (n + 1)) := by
        rw [hB1]; exact Nat.mul_le_mul_left _ (by lia)
      have : 2 ^ LA.w ≤ 2 ^ (LA.w * n) :=
        Nat.pow_le_pow_right (by decide) (Nat.le_mul_of_pos_right _ hn)
      lia
  rw [hc', Nat.mul_zero, Nat.add_zero] at i₃
  obtain ⟨n₁, n₂, n₃⟩ := FFT.normAt_spec q.1 n.toUSize d.toUSize
    (hb.window (by rw [i₁, ha])) (by rw [hn']; exact hn)
  rw [hn', hd'] at n₂ n₃
  refine ⟨by rw [n₁, i₁, ha], fun i hi => ?_, ?_⟩
  · rw [n₂ i hi, i₂ i (by lia), R.get_uset, ite_eq_right_iff.2 (fun e => by rw [hdn] at e; lia),
      a₂ i (by lia)]
  · rw [win, n₃, i₃]
    simp only [fermatW]
    rw [hPv']
    generalize LA.val (LA.get P (2 * n)) = H at *
    generalize valAt P 0 n = Plo at *
    generalize valAt P n n = Pmid at *
    generalize valAt a d n = V at *
    generalize LA.val (R.unB c) = cb at *
    generalize 2 ^ (LA.w * n) = Bn at *
    rw [reduce_eq a₃ hc₁ hhi hq, Nat.add_mul_mod_self_left]

/-- `reduceK` as `FFTOps.reduce`. -/
public theorem reduceK_spec (arr : A) (n d : Nat) (P : A) (_ : LA.size arr < USize.size)
    (hd : d + n + 1 ≤ LA.size arr) (hn : 1 ≤ n) (_ : LA.size P = 2 * n + 2)
    (_ : LA.size P < USize.size)
    (hPv : valAt P 0 (2 * n + 2) ≤ 2 ^ (LA.w * n) * 2 ^ (LA.w * n)) :
    LA.size (reduceK arr n d P) = LA.size arr ∧
      (∀ i, (i < d ∨ d + n + 1 ≤ i) → LA.get (reduceK arr n d P) i = LA.get arr i) ∧
      win (reduceK arr n d P) n d = valAt P 0 (2 * n + 2) % fermatW LA.w n := by
  unfold reduceK
  split
  · rename_i h
    have hb := reduceOK_of h
    dsimp only
    rw [F.foldThen_eq, foldUInPlaceThen]
    obtain ⟨f₁, -, f₂, f₃⟩ := foldUInPlace_spec2 n.toUSize
      (subNStep A P 0 P n.toUSize n.toUSize hb.lo hb.hi) P 0 P n.toUSize (fun _ => 0)
      (fun c => LA.val (R.unB c)) 1 0 0 1 0 1 0 (fun _ => True) (fun _ _ _ _ _ => trivial)
      (fun j hj z c _ => by
        have e := R.val_subMulB (R.uget P (0 + j) (hb.lo.uset_bound hj))
          (R.uget P (n.toUSize + j) (hb.hi.uset_bound hj)) R.one c
        simp only [subNStep, R.uget_eq, R.val_one, Nat.mul_one, hb.lo.toNat_add hj,
          hb.hi.toNat_add hj] at e ⊢
        lia)
      arr d.toUSize hb.dn 0 R.b0 trivial
    simp only [USize.toNat_zero, Nat.add_zero, Nat.sub_zero, Nat.zero_add, hb.hn, hb.hd,
      Nat.one_mul, Nat.zero_mul, Nat.mul_zero, R.val_unB_b0] at f₂ f₃
    exact reduce_aux arr n d P hb hn hPv _ f₁ _ f₂ (by lia)
  · refine ⟨size_writeNat .., fun i hi => get_writeNat _ _ _ _ _ (by lia), ?_⟩
    rw [win, valAt_writeNat arr d (n + 1) _ (by lia), Nat.mod_eq_of_lt]
    refine Nat.lt_of_lt_of_le (Nat.mod_lt _ (fermatW_pos _ _)) ?_
    simp only [fermatW]
    rw [Nat.mul_succ, Nat.pow_add]
    have := four_le (R := R)
    have : 1 ≤ 2 ^ (LA.w * n) := Nat.one_le_two_pow
    have := Nat.mul_le_mul_left (2 ^ (LA.w * n)) (show 2 ≤ 2 ^ LA.w by lia)
    lia

end MPN.WordArray
