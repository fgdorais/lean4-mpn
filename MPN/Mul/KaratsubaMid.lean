/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import MPN.AddSub

/-!
# The middle term of Karatsuba's method

With `z₀ = a₀ b₀` in limbs `[0, 2 k)` of `r` and `z₂ = a₁ b₁` above them, Karatsuba's method adds
`z₁ = t - z₀ - z₂` from limb `k` on, where `t = (a₀ + a₁) (b₀ + b₁)`. `karatsubaMid` does it in
one pass over `t`: limb `i` of the window becomes `r[k + i] + t[i] - z₀[i] - z₂[i]` plus the carry,
written into `t`, which nothing else holds, with the library's slice fold; then the window is
copied into `r` with `copySlice`, and the carry goes on with `add1IntoLoop`. Two subtractions and
an addition took three passes over `t`.

The carry from one limb to the next is between `-2` and `1`; the loop keeps it plus `2`, a word
between `0` and `3`, and its high word comes from a double-width sum (`UInt64.addDiffh`).
-/

open ScalarArray UInt64Array

namespace MPN

/-! ## The step -/

/--
The high word of `v + x + c + 2⁶⁵ - 2 - y - z` in double width, which is between `0` and `3` when
`c ≤ 3`: the carry out of `v + x + (c - 2) - y - z`, plus `2`.
-/
@[extern c inline "(uint64_t)(((__uint128_t)(#1) + (__uint128_t)(#2) + (__uint128_t)(#5) + \
  ((((__uint128_t)1) << 65) - 2) - (__uint128_t)(#3) - (__uint128_t)(#4)) >> 64)"]
public def UInt64.addDiffh (v x y z c : UInt64) : UInt64 :=
  ((v.toNat + x.toNat + c.toNat + (2 ^ 65 - 2) - y.toNat - z.toNat) / 2 ^ 64).toUInt64

private theorem sub_word (u v : UInt64) :
    ∃ k, k ≤ 1 ∧ (u - v).toNat + v.toNat = u.toNat + 2 ^ 64 * k := by
  have := u.toNat_lt; have := v.toNat_lt
  rw [UInt64.toNat_sub]
  by_cases h : v.toNat ≤ u.toNat
  · exact ⟨0, by lia, by
      rw [show 2 ^ 64 - v.toNat + u.toNat = (u.toNat - v.toNat) + 2 ^ 64 by lia, Nat.add_mod_right,
        Nat.mod_eq_of_lt (by lia)]; lia⟩
  · exact ⟨1, by lia, by rw [Nat.mod_eq_of_lt (by lia)]; lia⟩

private theorem add_word (u v : UInt64) :
    ∃ k, k ≤ 1 ∧ (u + v).toNat + 2 ^ 64 * k = u.toNat + v.toNat := by
  have := u.toNat_lt; have := v.toNat_lt
  rw [UInt64.toNat_add]
  by_cases h : u.toNat + v.toNat < 2 ^ 64
  · exact ⟨0, by lia, by rw [Nat.mod_eq_of_lt h]; try lia⟩
  · exact ⟨1, by lia, by
      rw [show u.toNat + v.toNat = (u.toNat + v.toNat - 2 ^ 64) + 2 ^ 64 by lia, Nat.add_mod_right,
        Nat.mod_eq_of_lt (by lia)]; try lia⟩

/-- The step of the loop: limb `v + x + (c - 2) - y - z` and the next carry plus `2`. -/
public theorem addDiff_step (v x y z c : UInt64) (hc : c.toNat ≤ 3) :
    (v + x + c - 2 - y - z).toNat + 2 ^ 64 * (UInt64.addDiffh v x y z c).toNat + y.toNat +
        z.toNat + 2 = v.toNat + x.toNat + c.toNat + 2 ^ 65 ∧
      (UInt64.addDiffh v x y z c).toNat ≤ 3 := by
  have := v.toNat_lt; have := x.toNat_lt; have := y.toNat_lt; have := z.toNat_lt
  obtain ⟨k₁, hk₁, e₁⟩ := add_word v x
  obtain ⟨k₂, hk₂, e₂⟩ := add_word (v + x) c
  obtain ⟨k₃, hk₃, e₃⟩ := sub_word (v + x + c) 2
  obtain ⟨k₄, hk₄, e₄⟩ := sub_word (v + x + c - 2) y
  obtain ⟨k₅, hk₅, e₅⟩ := sub_word (v + x + c - 2 - y) z
  have h2 : (2 : UInt64).toNat = 2 := rfl
  rw [h2] at e₃
  have hN : (v.toNat + x.toNat + c.toNat + (2 ^ 65 - 2) - y.toNat - z.toNat) / 2 ^ 64 < 4 := by
    lia
  have hh : (UInt64.addDiffh v x y z c).toNat =
      (v.toNat + x.toNat + c.toNat + (2 ^ 65 - 2) - y.toNat - z.toNat) / 2 ^ 64 := by
    rw [UInt64.addDiffh, Nat.toUInt64_eq, UInt64.toNat_ofNat', Nat.mod_eq_of_lt (by lia)]
  rw [hh]
  have := (v + x + c - 2 - y - z).toNat_lt
  generalize (v + x).toNat = s₁ at *
  generalize (v + x + c).toNat = s₂ at *
  generalize (v + x + c - 2).toNat = s₃ at *
  generalize (v + x + c - 2 - y).toNat = s₄ at *
  generalize (v + x + c - 2 - y - z).toNat = s₅ at *
  constructor <;> lia

/-! ## The loop -/

/-- `g j + 2⁶⁴ g (j + 1) + ⋯`, `m` terms: the value of the limbs `g j, …, g (j + m - 1)`. -/
public def wsum (g : Nat → Nat) (j : Nat) : Nat → Nat
  | 0 => 0
  | m + 1 => g j + 2 ^ 64 * wsum g (j + 1) m

public theorem valAt_eq_wsum (a : UInt64Array) (lo m : Nat) :
    a.valAt lo m = wsum (fun i => a[i]!.toNat) lo m := by
  induction m generalizing lo with
  | zero => rw [valAt_zero, wsum]
  | succ m ih => rw [valAt_succ, wsum, ih]

/--
The fold of `karatsubaMid` from limb `j`, for any step `f` that computes limb
`v + x + (c - 2) - y - z` and the next carry plus `2` from the limbs `gv i`, `gy i`, `gz i`: the
new limbs, the carry out and the limbs it reads, as values.
-/
private theorem foldlInPlace_loop_mid (m : Nat) (hm : m < USize.size)
    (f : (i : USize) → i.toNat < m → UInt64 → UInt64 → UInt64 × UInt64) (gv gy gz : Nat → Nat)
    (hf : ∀ i hi x c, c.toNat ≤ 3 →
      (f i hi x c).1.toNat + 2 ^ 64 * (f i hi x c).2.toNat + gy i.toNat + gz i.toNat + 2 =
          gv i.toNat + x.toNat + c.toNat + 2 ^ 65 ∧ (f i hi x c).2.toNat ≤ 3) (d : Nat) :
    ∀ (j : Nat) (s : UInt64Array.Slice) (hs : s.size = m) (c : UInt64), m - j = d →
      s.start = 0 → c.toNat ≤ 3 →
      (UInt64Array.Slice.foldlInPlace.loop m f s hs j c).1.array.size = s.array.size ∧
      (UInt64Array.Slice.foldlInPlace.loop m f s hs j c).1.start = 0 ∧
      (∀ i, (i < j ∨ m ≤ i) →
        (UInt64Array.Slice.foldlInPlace.loop m f s hs j c).1.array[i]! = s.array[i]!) ∧
      (UInt64Array.Slice.foldlInPlace.loop m f s hs j c).2.toNat ≤ 3 ∧
      (UInt64Array.Slice.foldlInPlace.loop m f s hs j c).1.array.valAt j (m - j) +
          2 ^ (64 * (m - j)) * (UInt64Array.Slice.foldlInPlace.loop m f s hs j c).2.toNat +
          wsum gy j (m - j) + wsum gz j (m - j) + 2 =
        wsum gv j (m - j) + s.array.valAt j (m - j) + c.toNat + 2 * 2 ^ (64 * (m - j)) := by
  induction d with
  | zero =>
    intro j s hs c hd hs₀ hc
    rw [UInt64Array.Slice.foldlInPlace.loop]
    simp only [show ¬j < m by lia, ↓reduceDIte]
    refine ⟨by simp, by simp [hs₀], fun _ _ => by simp, by simpa using hc, ?_⟩
    simp [hd, wsum]
  | succ d ih =>
    intro j s hs c hd hs₀ hc
    have hj : j < m := by lia
    have hst : s.stop = m := by
      have := UInt64Array.Slice.size_eq s
      have := s.start_le_stop
      lia
    have hjA : j < s.array.size := by have := s.stop_le_array_size; lia
    rw [UInt64Array.Slice.foldlInPlace.loop]
    simp only [hj, ↓reduceDIte]
    have hjU : j.toUSize.toNat = j := by
      rw [Nat.toUSize_eq, USize.toNat_ofNat']; exact Nat.mod_eq_of_lt (by lia)
    generalize hp : f j.toUSize _ s[j] c = p
    have hxj : s[j] = s.array[j]! := by
      rw [UInt64Array.Slice.getElem_eq, getElem!_eq_getElem _ _ (by lia)]; simp [hs₀]
    obtain ⟨hp₁, hp₂⟩ := hf j.toUSize (by rw [hjU]; exact hj) s[j] c hc
    rw [hp, hjU, hxj] at hp₁
    rw [hp] at hp₂
    obtain ⟨ih₁, ih₂, ih₃, ih₄, ih₅⟩ := ih (j + 1) (s.set j p.1 (by lia)) (by simpa using hs) p.2
      (by lia) (by simpa using hs₀) hp₂
    simp only [UInt64Array.Slice.array_set, UInt64Array.size_set, hs₀, Nat.zero_add] at ih₁ ih₃ ih₅
    -- The array after the loop has `p.1` at `j`, and the old limbs below `j` and from `m` on.
    have hset : ∀ i, (s.array.set j p.1 (by lia))[i]! = if i = j then p.1 else s.array[i]! := by
      intro i
      by_cases hi : i < s.array.size
      · rw [getElem!_eq_getElem _ _ (by simpa using hi), getElem!_eq_getElem _ _ hi,
          UInt64Array.getElem_set]
        by_cases e : i = j
        · subst e; simp
        · simp [e, Ne.symm e]
      · rw [getElem!_neg (s.array.set j p.1 (by lia)) i (by simpa using hi),
          getElem!_neg s.array i hi]
        split <;> first | (exfalso; lia) | rfl
    generalize UInt64Array.Slice.foldlInPlace.loop m f (s.set j p.1 _) _ (j + 1) p.2 = R at *
    refine ⟨ih₁, ih₂, fun i hi => ?_, ih₄, ?_⟩
    · rw [ih₃ i (by lia), hset]
      simp only [show i ≠ j by lia, ↓reduceIte]
    · have hRj : R.1.array[j]! = p.1 := by rw [ih₃ j (by lia), hset]; simp
      have hval : (s.array.set j p.1 (by lia)).valAt (j + 1) (m - (j + 1)) =
          s.array.valAt (j + 1) (m - (j + 1)) :=
        valAt_congr _ fun i h₁ _ => by rw [hset]; simp only [show i ≠ j by lia, ↓reduceIte]
      rw [hval] at ih₅
      rw [show m - j = m - (j + 1) + 1 by lia, valAt_succ, valAt_succ, wsum, wsum, wsum, hRj,
        Nat.mul_add 64 _ 1, Nat.mul_one, Nat.pow_add]
      generalize R.1.array.valAt (j + 1) (m - (j + 1)) = X at *
      generalize s.array.valAt (j + 1) (m - (j + 1)) = T at *
      generalize wsum gv (j + 1) (m - (j + 1)) = V at *
      generalize wsum gy (j + 1) (m - (j + 1)) = Y at *
      generalize wsum gz (j + 1) (m - (j + 1)) = Z at *
      generalize 2 ^ (64 * (m - (j + 1))) = P at *
      generalize R.2.toNat = cR at *
      generalize p.2.toNat = c₁ at *
      generalize p.1.toNat = l at *
      generalize s.array[j]!.toNat = x at *
      grind

/-- The limbs of `a` from `lo`, `len` of them and zeros after, as `wsum`. -/
private theorem wsum_pad (a : UInt64Array) (lo len : Nat) (m : Nat) : ∀ j, len ≤ j + m →
    wsum (fun i => if i < len then a[lo + i]!.toNat else 0) j m = a.valAt (lo + j) (len - j) := by
  induction m with
  | zero => intro j hj; rw [wsum, show len - j = 0 by lia, valAt_zero]
  | succ m ih =>
    intro j hj
    rw [wsum, ih (j + 1) (by lia)]
    by_cases hjl : j < len
    · simp only [hjl, ↓reduceIte]
      rw [show len - j = len - (j + 1) + 1 by lia, valAt_succ, Nat.add_assoc]
    · simp only [hjl, ↓reduceIte, show len - (j + 1) = 0 by lia, show len - j = 0 by lia,
        valAt_zero]

private theorem wsum_shift (a : UInt64Array) (lo m : Nat) : ∀ j,
    wsum (fun i => a[lo + i]!.toNat) j m = a.valAt (lo + j) m := by
  induction m with
  | zero => intro j; rw [wsum, valAt_zero]
  | succ m ih => intro j; rw [wsum, ih (j + 1), valAt_succ, Nat.add_assoc]

/-- `valAt` of limbs that agree after a shift. -/
private theorem valAt_shift (a b : UInt64Array) (n : Nat) : ∀ lo lo',
    (∀ i, i < n → a[lo + i]! = b[lo' + i]!) → a.valAt lo n = b.valAt lo' n := by
  induction n with
  | zero => intro _ _ _; rw [valAt_zero, valAt_zero]
  | succ n ih =>
    intro lo lo' h
    rw [valAt_succ, valAt_succ, ih (lo + 1) (lo' + 1) fun i hi => by
      rw [Nat.add_right_comm lo, Nat.add_right_comm lo', Nat.add_assoc, Nat.add_assoc]
      exact h (i + 1) (by lia)]
    have := h 0 (by lia)
    simp only [Nat.add_zero] at this
    rw [this]

/-- The slice fold keeps the size of its array. -/
private theorem size_array_foldlInPlace_loop {β : Type} (m : Nat)
    (f : (i : USize) → i.toNat < m → UInt64 → β → UInt64 × β) (s : UInt64Array.Slice)
    (hs : s.size = m) (j : Nat) (b : β) :
    (UInt64Array.Slice.foldlInPlace.loop m f s hs j b).1.array.size = s.array.size := by
  fun_induction UInt64Array.Slice.foldlInPlace.loop m f s hs j b with
  | case1 s hs j b hj hj' p ih => rw [ih]; simp
  | case2 => rfl

/-! ## The middle term -/

/--
The conditions of `karatsubaMid`: the `n` limbs from `rs` fit in `arr`, `t` has `2 k + 2` limbs,
and `3 k ≤ n ≤ 4 k + 2` with `2 ≤ k`, so that the window of `min (n - k) (2 k + 2)` limbs covers `z₀` and `z₂`.
-/
public abbrev MidOK (arr : UInt64Array) (rs k n : USize) (t : UInt64Array) : Prop :=
  LoopBound arr rs n ∧ k.toNat + k.toNat + k.toNat ≤ n.toNat ∧
    n.toNat ≤ k.toNat + k.toNat + k.toNat + k.toNat + 2 ∧ t.size = k.toNat + k.toNat + 2 ∧
    2 ≤ k.toNat

/-- The length of the window, `min (n - k) (2 k + 2)`. -/
@[inline, expose] public def midLen (k n : USize) : USize := min (n - k) (k + k + 2)

private theorem toNat_kk {arr : UInt64Array} {rs k n : USize} {t : UInt64Array}
    (h : MidOK arr rs k n t) : (k + k).toNat = k.toNat + k.toNat := by
  obtain ⟨⟨-, h₁⟩, h₂, -, -, -⟩ := h
  exact USize.toNat_add_of_lt (by lia)

private theorem toNat_midLen {arr : UInt64Array} {rs k n : USize} {t : UInt64Array}
    (h : MidOK arr rs k n t) :
    (midLen k n).toNat = min (n.toNat - k.toNat) (k.toNat + k.toNat + 2) := by
  have hkk := toNat_kk h
  obtain ⟨⟨-, h₁⟩, h₂, -, -, h₅⟩ := h
  have h2 : (2 : USize).toNat = 2 := by
    have : 4294967296 ≤ USize.size := by cases USize.size_eq <;> lia
    rw [USize.toNat_ofNat, Nat.mod_eq_of_lt (by simp only [USize.size] at this; lia)]
  rw [midLen, USize.toNat_min, USize.toNat_sub_of_le _ _ (USize.le_iff_toNat_le.2 (by lia)),
    USize.toNat_add_of_lt (by rw [hkk, h2]; lia), hkk, h2]

private theorem midStep_v {arr : UInt64Array} {rs k n : USize} {t : UInt64Array}
    (h : MidOK arr rs k n t) {i : USize} (hi : i.toNat < (midLen k n).toNat) : k + i < n := by
  have hL := toNat_midLen h
  obtain ⟨⟨-, h₁⟩, h₂, -, -, -⟩ := h
  rw [USize.lt_iff_toNat_lt, USize.toNat_add_of_lt (by lia)]
  lia

private theorem toNat_n_sub {arr : UInt64Array} {rs k n : USize} {t : UInt64Array}
    (h : MidOK arr rs k n t) : (n - (k + k)).toNat = n.toNat - (k.toNat + k.toNat) := by
  have hkk := toNat_kk h
  obtain ⟨-, h₂, -, -, -⟩ := h
  rw [USize.toNat_sub_of_le _ _ (USize.le_iff_toNat_le.2 (by lia)), hkk]

private theorem midStep_z {arr : UInt64Array} {rs k n : USize} {t : UInt64Array}
    (h : MidOK arr rs k n t) {i : USize} (hz : i < n - (k + k)) : k + k + i < n := by
  have hkk := toNat_kk h
  have hnk := toNat_n_sub h
  obtain ⟨⟨-, h₁⟩, h₂, -, -, -⟩ := h
  have := USize.lt_iff_toNat_lt.1 hz
  rw [USize.lt_iff_toNat_lt, USize.toNat_add_of_lt (by rw [hkk]; lia), hkk]
  lia

private theorem toNat_kki {arr : UInt64Array} {rs k n : USize} {t : UInt64Array}
    (h : MidOK arr rs k n t) {i : USize} (hz : i < n - (k + k)) :
    (k + k + i).toNat = k.toNat + k.toNat + i.toNat := by
  have hkk := toNat_kk h
  have hnk := toNat_n_sub h
  obtain ⟨⟨-, h₁⟩, h₂, -, -, -⟩ := h
  have := USize.lt_iff_toNat_lt.1 hz
  rw [USize.toNat_add_of_lt (by rw [hkk]; lia), hkk]

private theorem midStep_y {arr : UInt64Array} {rs k n : USize} {t : UInt64Array}
    (h : MidOK arr rs k n t) {i : USize} (hi : i < k + k) : i < n := by
  have hkk := toNat_kk h
  obtain ⟨-, h₂, -, -, -⟩ := h
  rw [USize.lt_iff_toNat_lt] at hi ⊢
  lia

/--
Limb `i` of the window: `r[k + i] + t[i] - z₀[i] - z₂[i]` plus the carry `c - 2`, reading `z₀` in
limbs `[rs, rs + 2 k)` of `arr` and `z₂` in `[rs + 2 k, rs + n)`, zero beyond them, and the next
carry plus `2`.
-/
@[inline] def midStep (arr : UInt64Array) (rs k n : USize) (t : UInt64Array)
    (h : MidOK arr rs k n t) (i : USize) (hi : i.toNat < (midLen k n).toNat) (x c : UInt64) :
    UInt64 × UInt64 :=
  let v := arr.uget (rs + (k + i)) (h.1.uset_bound (midStep_v h hi))
  let y := if hy : i < k + k then arr.uget (rs + i) (h.1.uset_bound (midStep_y h hy)) else 0
  let z := if hz : i < n - (k + k) then arr.uget (rs + (k + k + i)) (h.1.uset_bound (midStep_z h hz))
    else 0
  (v + x + c - 2 - y - z, UInt64.addDiffh v x y z c)

private theorem toNat_k_add {arr : UInt64Array} {rs k n : USize} {t : UInt64Array}
    (h : MidOK arr rs k n t) {i : USize} (hi : i.toNat < (midLen k n).toNat) :
    (k + i).toNat = k.toNat + i.toNat := by
  have hL := toNat_midLen h
  obtain ⟨⟨-, h₁⟩, h₂, h₃, -, -⟩ := h
  exact USize.toNat_add_of_lt (by lia)

/-- The step relation of `midStep`, on the limbs of `arr` it reads. -/
private theorem midStep_spec {arr : UInt64Array} {rs k n : USize} {t : UInt64Array}
    (h : MidOK arr rs k n t) (i : USize) (hi : i.toNat < (midLen k n).toNat) (x c : UInt64)
    (hc : c.toNat ≤ 3) :
    (midStep arr rs k n t h i hi x c).1.toNat + 2 ^ 64 * (midStep arr rs k n t h i hi x c).2.toNat +
        (if i.toNat < k.toNat + k.toNat then arr[rs.toNat + i.toNat]!.toNat else 0) +
        (if i.toNat < n.toNat - (k.toNat + k.toNat) then
          arr[rs.toNat + (k.toNat + k.toNat) + i.toNat]!.toNat else 0) + 2 =
      arr[rs.toNat + k.toNat + i.toNat]!.toNat + x.toNat + c.toNat + 2 ^ 65 ∧
      (midStep arr rs k n t h i hi x c).2.toNat ≤ 3 := by
  have hki := toNat_k_add h hi
  have hkk := toNat_kk h
  have hL := toNat_midLen h
  have hv := h.1.toNat_add (midStep_v h hi)
  unfold midStep
  dsimp only
  have hs := addDiff_step (arr.uget (rs + (k + i)) (h.1.uset_bound (midStep_v h hi))) x
    (if hy : i < k + k then arr.uget (rs + i) (h.1.uset_bound (midStep_y h hy)) else 0)
    (if hz : i < n - (k + k) then arr.uget (rs + (k + k + i)) (h.1.uset_bound (midStep_z h hz))
      else 0) c hc
  have hvv : (arr.uget (rs + (k + i)) (h.1.uset_bound (midStep_v h hi))).toNat =
      arr[rs.toNat + k.toNat + i.toNat]!.toNat := by
    rw [uget_eq_getElem!, hv, hki, Nat.add_assoc]
  have hyy : (if hy : i < k + k then arr.uget (rs + i) (h.1.uset_bound (midStep_y h hy))
      else 0).toNat =
        if i.toNat < k.toNat + k.toNat then arr[rs.toNat + i.toNat]!.toNat else 0 := by
    by_cases hy : i < k + k
    · have hy' : i.toNat < k.toNat + k.toNat := by rw [← hkk]; exact USize.lt_iff_toNat_lt.1 hy
      rw [dite_eq_left hy, ite_eq_left hy', uget_eq_getElem!, h.1.toNat_add (midStep_y h hy)]
    · have hy' : ¬i.toNat < k.toNat + k.toNat := by
        rw [← hkk]; exact fun e => hy (USize.lt_iff_toNat_lt.2 e)
      rw [dite_eq_right hy, ite_eq_right hy']; rfl
  have hzz : (if hz : i < n - (k + k) then arr.uget (rs + (k + k + i))
      (h.1.uset_bound (midStep_z h hz)) else 0).toNat =
        if i.toNat < n.toNat - (k.toNat + k.toNat) then
          arr[rs.toNat + (k.toNat + k.toNat) + i.toNat]!.toNat else 0 := by
    have hnk := toNat_n_sub h
    by_cases hz : i < n - (k + k)
    · have hz' : i.toNat < n.toNat - (k.toNat + k.toNat) := by
        rw [← hnk]; exact USize.lt_iff_toNat_lt.1 hz
      rw [dite_eq_left hz, ite_eq_left hz', uget_eq_getElem!, h.1.toNat_add (midStep_z h hz),
        toNat_kki h hz, Nat.add_assoc rs.toNat]
    · have hz' : ¬i.toNat < n.toNat - (k.toNat + k.toNat) := by
        rw [← hnk]; exact fun e => hz (USize.lt_iff_toNat_lt.2 e)
      rw [dite_eq_right hz, ite_eq_right hz']; rfl
  have e := hs.1
  rw [hvv, hyy, hzz] at e
  exact ⟨by lia, hs.2⟩

private theorem lt_midLen {arr : UInt64Array} {rs k n : USize} {t : UInt64Array}
    (h : MidOK arr rs k n t) {i : USize}
    (hi : i.toNat < (t.toSlice 0 (midLen k n).toNat).size) : i.toNat < (midLen k n).toNat := by
  rw [UInt64Array.size_toSlice] at hi
  lia

private theorem size_copy_mid {arr : UInt64Array} {rs k n : USize} {t : UInt64Array}
    (h : MidOK arr rs k n t) (src : UInt64Array) (hsrc : src.size = t.size) :
    (src.copySlice 0 arr (rs.toNat + k.toNat) (midLen k n).toNat).size = arr.size := by
  have hL := toNat_midLen h
  obtain ⟨⟨h₀, h₁⟩, h₂, -, h₄, -⟩ := h
  rw [UInt64Array.size_copySlice]
  lia

/--
Adds `t - z₀ - z₂` to the limbs of `arr` from `rs + k` to `rs + n - 1`, where `z₀` is in limbs
`[rs, rs + 2 k)` and `z₂` in `[rs + 2 k, rs + n)`, in one pass over the window of
`min (n - k) (2 k + 2)` limbs: the new limbs are written into `t`, copied into `arr`, and the carry
goes on above the window. It requires `MidOK arr rs k n t`, and leaves `arr` unchanged otherwise.
-/
public def karatsubaMid (arr : UInt64Array) (rs k n : USize) (t : UInt64Array) : UInt64Array :=
  if h : MidOK arr rs k n t then
    let p := (t.toSlice 0 (midLen k n).toNat).foldlInPlace (2 : UInt64) fun i hi x c =>
      midStep arr rs k n t h i (lt_midLen h hi) x c
    let arr' := p.1.array.copySlice 0 arr (rs.toNat + k.toNat) (midLen k n).toNat
    if hb : LoopBound arr' rs n then (add1IntoLoop arr' rs n hb (k + midLen k n) (p.2 - 2)).1
    else arr'
  else arr

/-! ## Correctness -/

/-- The fold of `karatsubaMid` on a slice from `0`, from its step relation. -/
private theorem foldlInPlace_mid (s : UInt64Array.Slice) (hm : s.size < USize.size)
    (hs₀ : s.start = 0) (f : (i : USize) → i.toNat < s.size → UInt64 → UInt64 → UInt64 × UInt64)
    (gv gy gz : Nat → Nat)
    (hf : ∀ i hi x c, c.toNat ≤ 3 →
      (f i hi x c).1.toNat + 2 ^ 64 * (f i hi x c).2.toNat + gy i.toNat + gz i.toNat + 2 =
          gv i.toNat + x.toNat + c.toNat + 2 ^ 65 ∧ (f i hi x c).2.toNat ≤ 3) :
    (s.foldlInPlace 2 f).1.array.size = s.array.size ∧
      (s.foldlInPlace 2 f).2.toNat ≤ 3 ∧
      (s.foldlInPlace 2 f).1.array.valAt 0 s.size +
          2 ^ (64 * s.size) * (s.foldlInPlace 2 f).2.toNat + wsum gy 0 s.size +
          wsum gz 0 s.size + 2 =
        wsum gv 0 s.size + s.array.valAt 0 s.size + 2 + 2 * 2 ^ (64 * s.size) := by
  unfold UInt64Array.Slice.foldlInPlace
  obtain ⟨h₁, -, -, h₄, h₅⟩ := foldlInPlace_loop_mid s.size hm f gv gy gz hf _ 0 s rfl 2 rfl hs₀
    (by decide)
  rw [Nat.sub_zero] at h₅
  exact ⟨h₁, h₄, h₅⟩

/-- The limbs after the copy: the window from `src`, the others from `arr`. -/
private theorem getElem!_copy_mid {arr : UInt64Array} {rs k n : USize} {t : UInt64Array}
    (h : MidOK arr rs k n t) (src : UInt64Array) (hsrc : src.size = t.size) (i : Nat) :
    (src.copySlice 0 arr (rs.toNat + k.toNat) (midLen k n).toNat)[i]! =
      if rs.toNat + k.toNat ≤ i ∧ i < rs.toNat + k.toNat + (midLen k n).toNat then
        src[i - (rs.toNat + k.toNat)]! else arr[i]! := by
  have hL := toNat_midLen h
  have hsz := size_copy_mid h src hsrc
  obtain ⟨⟨h₀, h₁⟩, h₂, -, h₄, -⟩ := h
  by_cases hi : i < arr.size
  · rw [getElem!_eq_getElem _ _ (by rw [hsz]; exact hi), UInt64Array.getElem_copySlice]
    have hmin : min (rs.toNat + k.toNat) arr.size = rs.toNat + k.toNat := by lia
    have hmin2 : min (midLen k n).toNat (src.size - 0) = (midLen k n).toNat := by lia
    simp only [hmin, hmin2]
    split
    · rw [ite_eq_right (by lia), getElem!_eq_getElem _ _ hi]
    · split
      · rw [ite_eq_left (by lia), getElem!_eq_getElem _ _ (by lia)]
        simp
      · rw [ite_eq_right (by lia), getElem!_eq_getElem _ _ hi]
  · rw [getElem!_neg (src.copySlice 0 arr (rs.toNat + k.toNat) (midLen k n).toNat) i
      (by rw [hsz]; exact hi), getElem!_neg arr i hi]
    split
    · exfalso; lia
    · rfl

/-- Two numbers below `P` that differ by a multiple of `P` are equal. -/
private theorem eq_of_add_mul {X Y P a b : Nat} (hX : X < P) (hY : Y < P)
    (h : X + P * a = Y + P * b) : X = Y := by
  have := congrArg (· % P) h
  simp only [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hX, Nat.mod_eq_of_lt hY] at this
  exact this

public theorem karatsubaMid_spec (arr : UInt64Array) (rs k n : USize) (t : UInt64Array)
    (h : MidOK arr rs k n t) :
    (karatsubaMid arr rs k n t).size = arr.size ∧
      (∀ i, (i < rs.toNat ∨ rs.toNat + n.toNat ≤ i) →
        (karatsubaMid arr rs k n t)[i]! = arr[i]!) ∧
      (∀ Z₁, t.valAt 0 (k.toNat + k.toNat + 2) =
          arr.valAt rs.toNat (k.toNat + k.toNat) + Z₁ +
            arr.valAt (rs.toNat + (k.toNat + k.toNat)) (n.toNat - (k.toNat + k.toNat)) →
        arr.valAt rs.toNat (k.toNat + k.toNat) + 2 ^ (64 * k.toNat) * Z₁ +
            2 ^ (64 * (k.toNat + k.toNat)) *
              arr.valAt (rs.toNat + (k.toNat + k.toNat)) (n.toNat - (k.toNat + k.toNat)) <
          2 ^ (64 * n.toNat) →
        (karatsubaMid arr rs k n t).valAt rs.toNat n.toNat =
          arr.valAt rs.toNat (k.toNat + k.toNat) + 2 ^ (64 * k.toNat) * Z₁ +
            2 ^ (64 * (k.toNat + k.toNat)) *
              arr.valAt (rs.toNat + (k.toNat + k.toNat)) (n.toNat - (k.toNat + k.toNat))) := by
  have hL := toNat_midLen h
  have hkk := toNat_kk h
  have hh := h
  obtain ⟨⟨h₀, h₁⟩, h₂, h₃, h₄, h₅⟩ := hh
  rw [karatsubaMid, dite_eq_left h]
  dsimp only
  -- The fold over the window of `t`.
  have hs₀ : (t.toSlice 0 (midLen k n).toNat).start = 0 := by
    rw [UInt64Array.start_toSlice]; lia
  have hss : (t.toSlice 0 (midLen k n).toNat).size = (midLen k n).toNat := by
    rw [UInt64Array.size_toSlice]; lia
  obtain ⟨hp₁, hp₄, hp₅⟩ := foldlInPlace_mid (t.toSlice 0 (midLen k n).toNat) (by lia) hs₀
    (fun i hi x c => midStep arr rs k n t h i (lt_midLen h hi) x c)
    (fun j => arr[rs.toNat + k.toNat + j]!.toNat)
    (fun j => if j < k.toNat + k.toNat then arr[rs.toNat + j]!.toNat else 0)
    (fun j => if j < n.toNat - (k.toNat + k.toNat) then
      arr[rs.toNat + (k.toNat + k.toNat) + j]!.toNat else 0)
    (fun i hi x c hc => midStep_spec h i (lt_midLen h hi) x c hc)
  generalize (t.toSlice 0 (midLen k n).toNat).foldlInPlace 2
    (fun i hi x c => midStep arr rs k n t h i (lt_midLen h hi) x c) = p at *
  rw [hss, UInt64Array.array_toSlice] at hp₅
  rw [UInt64Array.array_toSlice] at hp₁
  rw [wsum_shift, wsum_pad _ _ _ _ 0 (by lia), wsum_pad _ _ _ _ 0 (by lia)] at hp₅
  simp only [Nat.add_zero, Nat.sub_zero] at hp₅
  -- The copy into `arr`.
  have hc := getElem!_copy_mid h p.1.array hp₁
  have hcs := size_copy_mid h p.1.array hp₁
  generalize p.1.array.copySlice 0 arr (rs.toNat + k.toNat) (midLen k n).toNat = arr' at *
  have hb : LoopBound arr' rs n := by rw [LoopBound, hcs]; exact h.1
  rw [dite_eq_left hb]
  -- The carry above the window.
  have hkL : (k + midLen k n).toNat = k.toNat + (midLen k n).toNat :=
    USize.toNat_add_of_lt (by lia)
  obtain ⟨a₁, a₂, a₃⟩ := add1IntoLoop_spec arr' rs n hb (k + midLen k n) (p.2 - 2)
  rw [hkL] at a₂ a₃
  generalize add1IntoLoop arr' rs n hb (k + midLen k n) (p.2 - 2) = q at *
  refine ⟨by rw [a₁, hcs], fun i hi => ?_, fun Z₁ hT hW => ?_⟩
  · rw [a₂ i (by lia), hc i, ite_eq_right (by lia)]
  -- The value, from its three parts: below the window, the window, and above it.
  generalize hK : k.toNat = K at *
  generalize hN : n.toNat = N at *
  generalize hLL : (midLen k n).toNat = L at *
  generalize hR : rs.toNat = R at *
  have hlo : q.1.valAt R K = arr.valAt R K :=
    valAt_congr _ fun i h₁ h₂ => by rw [a₂ i (by lia), hc i, ite_eq_right (by lia)]
  have hmid : q.1.valAt (R + K) L = p.1.array.valAt 0 L :=
    valAt_shift _ _ L _ _ fun i hi => by
      rw [a₂ _ (by lia), hc, ite_eq_left (by lia), Nat.zero_add]
      congr 1
      lia
  have hhi : arr'.valAt (R + (K + L)) (N - (K + L)) = arr.valAt (R + (K + L)) (N - (K + L)) :=
    valAt_congr _ fun i h₁ h₂ => by rw [hc i, ite_eq_right (by lia)]
  rw [hhi] at a₃
  have hsplit (a : UInt64Array) : a.valAt R N =
      a.valAt R K + 2 ^ (64 * K) * (a.valAt (R + K) L +
        2 ^ (64 * L) * a.valAt (R + (K + L)) (N - (K + L))) := by
    have e : N = K + (L + (N - (K + L))) := by lia
    calc a.valAt R N = a.valAt R (K + (L + (N - (K + L)))) := by rw [← e]
      _ = _ := by rw [UInt64Array.valAt_add, UInt64Array.valAt_add, Nat.add_assoc R]
  have hsplit₂ : arr.valAt R N = arr.valAt R (K + K) +
      2 ^ (64 * (K + K)) * arr.valAt (R + (K + K)) (N - (K + K)) := by
    rw [← UInt64Array.valAt_add, show K + K + (N - (K + K)) = N by lia]
  rw [hsplit q.1, hlo, hmid]
  have hA := hsplit arr
  rw [hsplit₂] at hA
  have hPow : 2 ^ (64 * (K + K)) = 2 ^ (64 * K) * 2 ^ (64 * K) := by
    rw [← Nat.pow_add]; congr 1; lia
  have hPN : 2 ^ (64 * N) = 2 ^ (64 * K) * (2 ^ (64 * L) * 2 ^ (64 * (N - (K + L)))) := by
    rw [← Nat.pow_add, ← Nat.pow_add]; congr 1; lia
  have hX := valAt_lt p.1.array 0 L
  have hQ : 0 < 2 ^ (64 * K) := Nat.two_pow_pos _
  have hlt := valAt_lt q.1 R N
  rw [hsplit q.1, hlo, hmid, hPN] at hlt
  rw [hPow] at hA hW ⊢
  rw [hPN] at hW
  generalize arr.valAt R K = R₀ at *
  generalize arr.valAt (R + K) L = V at *
  generalize arr.valAt R (K + K) = Z₀ at *
  generalize arr.valAt (R + (K + K)) (N - (K + K)) = Z₂ at *
  generalize p.1.array.valAt 0 L = X at *
  generalize 2 ^ (64 * K) = Q at *
  rcases Nat.lt_or_ge L (K + K + 2) with hLt | hLe
  · -- The window ends at `n`: `t` was cut to `L` limbs, and nothing is above the window.
    have hNL : N - (K + L) = 0 := by lia
    rw [hNL, valAt_zero, Nat.mul_zero, Nat.add_zero] at hA ⊢
    have hTL := valAt_mod t 0 (Nat.le_of_lt hLt)
    rw [hTL] at hp₅
    generalize t.valAt 0 (K + K + 2) = T at *
    generalize 2 ^ (64 * L) = P at *
    have hdm := Nat.div_add_mod T P
    have hPpos : 0 < P := by
      rcases Nat.eq_zero_or_pos P with e | e
      · rw [e] at hX; lia
      · exact e
    -- `V + Z₁` fits in the window, since the result fits in `n` limbs.
    have hVZ : V + Z₁ < P := by
      have hW' : Q * (V + Z₁) < Q * P := by
        rw [show N - (K + L) = 0 by lia, Nat.pow_zero, Nat.mul_one] at hW
        have : R₀ + Q * V = Z₀ + Q * Q * Z₂ := hA.symm
        have e : Z₀ + Q * Z₁ + Q * Q * Z₂ = R₀ + Q * (V + Z₁) := by grind
        lia
      exact Nat.lt_of_mul_lt_mul_left hW'
    have hXe : X = V + Z₁ := by
      apply eq_of_add_mul hX hVZ (a := p.2.toNat + T / P) (b := 2)
      rw [Nat.mul_add]
      generalize P * (T / P) = PT at *
      generalize T % P = TP at *
      generalize P * p.2.toNat = Pc at *
      lia
    rw [hXe, Nat.mul_add]
    generalize Q * V = QV at *
    generalize Q * Z₁ = QZ at *
    generalize Q * Q * Z₂ = QQZ at *
    lia
  · -- The window has all of `t`: the carry out of it goes on above.
    have hLe' : L = K + K + 2 := by lia
    subst hLe'
    rw [hT] at hp₅
    generalize 2 ^ (64 * (K + K + 2)) = P at *
    generalize q.1.valAt (R + (K + (K + K + 2))) (N - (K + (K + K + 2))) = Hq at *
    generalize arr.valAt (R + (K + (K + K + 2))) (N - (K + (K + K + 2))) = H at *
    generalize 2 ^ (64 * (N - (K + (K + K + 2)))) = P' at *
    generalize q.2.toNat = cout at *
    -- The carry out of the window is `2` or `3`, the true carry `0` or `1`.
    have hc23 : p.2.toNat = 2 ∨ p.2.toNat = 3 := by
      have : p.2.toNat = 0 ∨ p.2.toNat = 1 ∨ p.2.toNat = 2 ∨ p.2.toNat = 3 := by lia
      rcases this with e | e | e | e <;> rw [e] at hp₅ <;> first | lia | simp [e]
    have hsub : (p.2 - 2).toNat = p.2.toNat - 2 :=
      UInt64.toNat_sub_of_le _ _ (by rw [UInt64.le_iff_toNat_le]; simp; lia)
    rw [hsub] at a₃
    -- The value plus the carry out of `n` limbs is the product.
    have hres : R₀ + Q * (X + P * Hq) + Q * (P * P') * cout = Z₀ + Q * Z₁ + Q * Q * Z₂ := by
      have e₁ : Q * (P * P') * cout = Q * P * (P' * cout) := by
        rw [Nat.mul_assoc, Nat.mul_assoc, Nat.mul_assoc]
      have e₂ : Q * (P * H) = Q * P * H := by rw [Nat.mul_assoc]
      have e₃ : Q * (P * Hq) = Q * P * Hq := by rw [Nat.mul_assoc]
      rw [e₁, Nat.mul_add, e₃]
      rw [Nat.mul_add, e₂] at hA
      rcases hc23 with e | e <;> rw [e] at hp₅ a₃
      · have hx : X = V + Z₁ := by lia
        have ha : Q * P * Hq + Q * P * (P' * cout) = Q * P * H := by
          rw [← Nat.mul_add, a₃, Nat.sub_self, Nat.add_zero]
        rw [hx, Nat.mul_add]
        generalize Q * P * Hq = A at *
        generalize Q * P * (P' * cout) = B at *
        generalize Q * P * H = C at *
        generalize Q * V = QV at *
        generalize Q * Z₁ = QZ at *
        generalize Q * Q * Z₂ = QQZ at *
        lia
      · have hx : X + P = V + Z₁ := by lia
        have ha : Q * P * Hq + Q * P * (P' * cout) = Q * P * H + Q * P := by
          rw [← Nat.mul_add, a₃, Nat.mul_add, Nat.mul_one]
        have hb : Q * X + Q * P = Q * V + Q * Z₁ := by
          rw [← Nat.mul_add, ← Nat.mul_add, hx]
        generalize Q * P * Hq = A at *
        generalize Q * P * (P' * cout) = B at *
        generalize Q * P * H = C at *
        generalize Q * V = QV at *
        generalize Q * Z₁ = QZ at *
        generalize Q * Q * Z₂ = QQZ at *
        generalize Q * X = QX at *
        generalize Q * P = QP at *
        lia
    -- Both are below `β^n`, so the carry out is `0`.
    have hcout : cout = 0 := by
      rcases Nat.eq_zero_or_pos cout with e | e
      · exact e
      · have : Q * (P * P') ≤ Q * (P * P') * cout := Nat.le_mul_of_pos_right _ e
        generalize Q * (P * P') * cout = D at *
        generalize Q * (P * P') = E at *
        lia
    rw [hcout, Nat.mul_zero, Nat.add_zero] at hres
    exact hres

end MPN
