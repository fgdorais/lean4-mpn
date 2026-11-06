/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import MPN32.Div.Limb
public import MPN32.Div.Basecase
public import MPN32.Mul
public import MPN.Join
public import MPN32.Sqr
public import MPN32.Cmp
public import MPN.Generic.DC
public import MPN32.Arch.DivTwo
public import MPN32.Bits
public import MPN.Generic.Barrett

/-!
# Division

`divMod a b` is `(a / b, a % b)`, trimmed, with `Nat`'s conventions: `a / 0 = 0` and `a % 0 = a`.
The divisor is first cut to its nonzero limbs. A divisor of one limb uses `divRem1`, and one of two
`divRem2`. A longer one is normalized, like in GMP: both numbers are multiplied by a power of two
`f` that sets the top bit of the divisor, which keeps the corrections of the quotient estimates
few, and the remainder is divided by `f` again at the end: by shifts in `divRemBasecase` below
`config.divDC` limbs in the divisor, and by `mulRow` before the division by blocks from there.
Normalization only affects speed: the quotient of `a f` by `b f` is `a / b` and the remainder
`(a % b) f` for any `f ≠ 0`.
-/

open ScalarArray

namespace MPN.W32

/-! ## The size without trailing zeros -/

/-- The number of limbs of `s` below `i` without the trailing zeros. -/
def topSizeLoop (s : UInt32Array.Slice) : Nat → Nat
  | 0 => 0
  | i + 1 => if s.getD i 0 = 0 then topSizeLoop s i else i + 1

/-- The number of limbs of `s` without its trailing zero limbs. -/
public def topSize (s : UInt32Array.Slice) : Nat := topSizeLoop s s.size

private theorem topSizeLoop_spec (s : UInt32Array.Slice) (i : Nat) :
    topSizeLoop s i ≤ i ∧
      (∀ k, topSizeLoop s i ≤ k → k < i → s.getD k 0 = 0) ∧
      (0 < topSizeLoop s i → s.getD (topSizeLoop s i - 1) 0 ≠ 0) := by
  induction i with
  | zero => simp [topSizeLoop]
  | succ i ih =>
    simp only [topSizeLoop]
    split
    · rename_i h
      refine ⟨by lia, fun k hk hki => ?_, ih.2.2⟩
      by_cases hk' : k = i
      · rw [hk']; exact h
      · exact ih.2.1 k hk (by lia)
    · rename_i h
      exact ⟨Nat.le_refl _, fun k hk hki => by lia, fun _ => h⟩

public theorem topSize_le (s : UInt32Array.Slice) : topSize s ≤ s.size :=
  (topSizeLoop_spec s s.size).1

/-- The top limb below `topSize s` is not zero. -/
public theorem getD_topSize_ne_zero (s : UInt32Array.Slice) (h : 0 < topSize s) :
    s.getD (topSize s - 1) 0 ≠ 0 :=
  (topSizeLoop_spec s s.size).2.2 h

/-- Cutting `s` to `topSize s` limbs keeps its value. -/
public theorem toNat_slice_topSize (s : UInt32Array.Slice) :
    toNat (s.slice 0 (topSize s)) = toNat s := by
  have hle := topSize_le s
  have hz : ∀ k, topSize s ≤ k → k < s.size → s.getD k 0 = 0 := (topSizeLoop_spec s s.size).2.1
  have h := toNat_slice_add_toNat_slice s (topSize s) hle
  have h0 : toNat (s.slice (topSize s) s.size) = 0 := by
    rw [toNat_slice, Nat.min_self]
    refine MPN.LimbArray.valAt_eq_zero _ fun i h₁ h₂ => ?_
    change s.array[i]!.toNat = 0
    have := hz (i - s.start) (by lia) (by lia)
    rw [UInt32Array.Slice.getD_eq, dite_eq_left (by lia), UInt32Array.Slice.getElem_eq_getElem!,
      show s.start + (i - s.start) = i by lia] at this
    rw [this]
    rfl
  rw [h0, Nat.mul_zero, Nat.add_zero] at h
  exact h

/-- A number of `topSize s` limbs is below `β ^ topSize s`. -/
public theorem toNat_lt_topSize (s : UInt32Array.Slice) : toNat s < 2 ^ (32 * topSize s) := by
  have := toNat_lt (s.slice 0 (topSize s))
  rw [toNat_slice_topSize, UInt32Array.Slice.size_slice] at this
  have hle := topSize_le s
  rwa [show min (topSize s) s.size - 0 = topSize s by lia] at this

/-! ## The base-generic operations

`ops32With div` is the instance of `NatOps` for slices of 32-bit limbs with the division `div`:
`ops32B`, with the schoolbook division `divBase32`, runs `main`'s divide-and-conquer division
(`NatOps.divNorm`) below, and `ops32`, with `divModSlow`, the other base-generic algorithms.
-/

/-- The top limb of `s` cut to `topSize s` limbs is not zero. -/
private theorem top_slice_topSize_ne_zero (s : UInt32Array.Slice) (h : 0 < topSize s) :
    (s.slice 0 (topSize s))[(s.slice 0 (topSize s)).size - 1]'(by
      simp only [UInt32Array.Slice.size_slice]; have := topSize_le s; lia) ≠ 0 := by
  have hle := topSize_le s
  have := getD_topSize_ne_zero s h
  rw [UInt32Array.Slice.getD_eq] at this
  simp only [show topSize s - 1 < s.size by lia, ↓reduceDIte] at this
  simp only [UInt32Array.Slice.getElem_slice, UInt32Array.Slice.size_slice, Nat.zero_add,
    Nat.min_eq_left hle, Nat.sub_zero]
  exact this

private theorem div_mod_eq {q r N D : Nat} (hD : 0 < D) (h : q * D + r = N) (hr : r < D) :
    q = N / D ∧ r = N % D := by
  have := (Nat.div_mod_unique (a := N) (b := D) (d := q) (c := r) hD).2
    ⟨by rw [Nat.mul_comm D q]; lia, hr⟩
  exact ⟨this.1.symm, this.2.symm⟩

public theorem toNat_slice_lo (s : UInt32Array.Slice) (k : Nat) :
    toNat (s.slice 0 k) = toNat s % (2 ^ 32) ^ k := by
  rw [toNat_slice, toNat_eq_valAt, Nat.sub_zero, Nat.add_zero, ← Nat.pow_mul]
  by_cases hk : k ≤ s.size
  · rw [Nat.min_eq_left hk, UInt32Array.valAt_mod _ _ hk]
  · rw [Nat.min_eq_right (by lia), Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le
      (UInt32Array.valAt_lt ..) (Nat.pow_le_pow_right (by decide) (by lia)))]

public theorem toNat_slice_hi (s : UInt32Array.Slice) (k : Nat) :
    toNat (s.slice k s.size) = toNat s / (2 ^ 32) ^ k := by
  rw [← Nat.pow_mul]
  by_cases hk : k ≤ s.size
  · exact toNat_slice_from s k hk
  · rw [toNat_of_size_eq_zero (by simp; lia), Nat.div_eq_of_lt]
    exact Nat.lt_of_lt_of_le (toNat_lt s) (Nat.pow_le_pow_right (by decide) (by lia))

public theorem toNat_shl (k : Nat) (x : UInt32Array.Slice) :
    toNat (UInt32Array.replicate k 0 ++ x.copy).toSlice = toNat x * (2 ^ 32) ^ k := by
  rw [toNat_replicate_append, toNat_copy, ← Nat.pow_mul]

public theorem toNat_pow (k : Nat) :
    toNat ((UInt32Array.replicate k 0).push 1).toSlice = (2 ^ 32) ^ k := by
  rw [toNat_replicate_push, ← Nat.pow_mul]

public theorem toNat_sub_slice (x y : UInt32Array.Slice) (h : toNat y ≤ toNat x) :
    toNat (subLimbs x (y.slice 0 x.size)).toSlice = toNat x - toNat y := by
  have hy : toNat (y.slice 0 x.size) = toNat y := by
    rw [toNat_slice_lo, Nat.mod_eq_of_lt]
    rw [← Nat.pow_mul]
    exact Nat.lt_of_le_of_lt h (toNat_lt x)
  rw [toNat_toSlice, ← toNat_toSlice, toNat_subLimbs _ _ (by simp; lia) (by rw [hy]; exact h), hy]

/--
`(u / v, u % v)` by the schoolbook method alone: the divisor is cut to its nonzero limbs, then
`divRem1` for one limb and `divRemBasecase` for more. The base case of `ops32B.divNorm`.
-/
public def divBase32 (u v : UInt32Array.Slice) : UInt32Array.Slice × UInt32Array.Slice :=
  let n := topSize v
  if n = 1 then
    let p := divRem1 u (v.getD 0 0)
    (p.1.toSlice, (UInt32Array.mk #[p.2]).toSlice)
  else if h : 2 ≤ n then
    let p := divRemBasecase div32RecipU u (v.slice 0 n) (by simp; have := topSize_le v; lia)
    (p.1.toSlice, p.2.toSlice)
  else (UInt32Array.empty.toSlice, u)

public theorem val_divBase32 (u v : UInt32Array.Slice) (hv : toNat v ≠ 0) :
    toNat (divBase32 u v).1 = toNat u / toNat v ∧ toNat (divBase32 u v).2 = toNat u % toNat v := by
  have hb := toNat_slice_topSize v
  have hle := topSize_le v
  have hV : 0 < toNat v := by lia
  unfold divBase32
  dsimp only
  split
  · rename_i h₁
    have hd := getD_topSize_ne_zero v (by lia)
    rw [h₁] at hd
    have hb1 : toNat v = (v.getD 0 0).toNat := by
      rw [← hb, toNat_of_size_eq_one (by simp [h₁]; lia)]
      simp [UInt32Array.Slice.getD_eq, show 0 < v.size by lia]
    obtain ⟨h₂, h₃⟩ := divRem1_spec u (v.getD 0 0) hd
    rw [← hb1] at h₂ h₃
    obtain ⟨hq, hr⟩ := div_mod_eq hV h₂ h₃
    refine ⟨hq, ?_⟩
    rw [← hr, toNat_toSlice]
    simp
  · split
    · rename_i h₁ h
      obtain ⟨h₂, h₃⟩ := divRemBasecase_spec div32RecipU u (v.slice 0 (topSize v))
        (by simp; lia) (top_slice_topSize_ne_zero v (by lia))
      rw [hb] at h₂ h₃
      exact div_mod_eq hV h₂ h₃
    · rename_i h₁ h
      have h₀ : topSize v = 0 := by lia
      have : toNat v = 0 := by rw [← hb, toNat_of_size_eq_zero (by simp [h₀])]
      lia

/-- The window of a slice, for a guarded slice. -/
private theorem window_bound (v : UInt32Array.Slice) (h : v.start + v.size < USize.size) :
    MPN.WordArray.LoopBound v.array v.start.toUSize v.size.toUSize := by
  have := v.stop_le_array_size
  have := v.start_le_stop
  have hs := v.size_eq
  have h₁ : v.start.toUSize.toNat = v.start := toNat_toUSize (by lia)
  have h₂ : v.size.toUSize.toNat = v.size := toNat_toUSize (by lia)
  show v.start.toUSize.toNat + v.size.toUSize.toNat ≤ v.array.size ∧
    v.start.toUSize.toNat + v.size.toUSize.toNat < USize.size
  rw [h₁, h₂]
  exact ⟨by lia, by lia⟩

private theorem join_ok (k : Nat) (x y : UInt32Array.Slice)
    (h : x.start + x.size < 4294967295 ∧ y.start + y.size < 4294967295 ∧
      k + x.size < 4294967295) :
    WordArray.JoinOK k.toUSize x.array x.start.toUSize x.size.toUSize y.array y.start.toUSize
      y.size.toUSize (UInt32Array.replicate (k + x.size) 0) := by
  have e₁ := toNat_toUSize (show k < USize.size from lt_usizeSize (by lia))
  have e₂ := toNat_toUSize (show x.size < USize.size from lt_usizeSize (by lia))
  refine ⟨window_bound x (lt_usizeSize h.1), window_bound y (lt_usizeSize h.2.1), ?_, ?_,
    fun i => ?_⟩
  · rw [e₁, e₂]; exact lt_usizeSize h.2.2
  · show (UInt32Array.replicate _ 0).size = _; rw [UInt32Array.size_replicate, e₁, e₂]
  · show ((UInt32Array.replicate (k + x.size) 0)[i]!).toNat = 0
    by_cases hi : i < k + x.size
    · rw [getElem!_pos _ i (by simpa using hi), UInt32Array.getElem_replicate]; rfl
    · rw [getElem!_neg _ i (by simpa using hi)]; rfl

/-- `x βᵏ + y mod βᵏ`, by `main`'s `WordArray.joinW` in one array. -/
public def join32 (k : Nat) (x y : UInt32Array.Slice) : UInt32Array.Slice :=
  if h : x.start + x.size < 4294967295 ∧ y.start + y.size < 4294967295 ∧
      k + x.size < 4294967295 then
    (WordArray.joinW UInt32Array k.toUSize x.array x.start.toUSize x.size.toUSize y.array
      y.start.toUSize y.size.toUSize (UInt32Array.replicate (k + x.size) 0)
      (join_ok k x y h)).toSlice
  else (ofNat (toNat x * 2 ^ (32 * k) + toNat y % 2 ^ (32 * k))).toSlice

public theorem toNat_join32 (k : Nat) (x y : UInt32Array.Slice) :
    toNat (join32 k x y) = toNat x * (2 ^ 32) ^ k + toNat y % (2 ^ 32) ^ k := by
  rw [← Nat.pow_mul]
  by_cases h : x.start + x.size < 4294967295 ∧ y.start + y.size < 4294967295 ∧
      k + x.size < 4294967295
  · have e : join32 k x y = (WordArray.joinW UInt32Array k.toUSize x.array x.start.toUSize
        x.size.toUSize y.array y.start.toUSize y.size.toUSize (UInt32Array.replicate (k + x.size) 0)
        (join_ok k x y h)).toSlice := by
      simp only [join32, h, and_self, ↓reduceDIte]
    rw [e]
    have e₁ := toNat_toUSize (show k < USize.size from lt_usizeSize (by lia))
    have e₂ := toNat_toUSize (show x.size < USize.size from lt_usizeSize (by lia))
    have e₃ := toNat_toUSize (show y.size < USize.size from lt_usizeSize (by lia))
    have e₄ := toNat_toUSize (show x.start < USize.size from lt_usizeSize (by lia))
    have e₅ := toNat_toUSize (show y.start < USize.size from lt_usizeSize (by lia))
    obtain ⟨j₁, j₂⟩ := WordArray.joinW_spec (A := UInt32Array) k.toUSize x.array x.start.toUSize
      x.size.toUSize y.array y.start.toUSize y.size.toUSize _ (join_ok k x y h)
    simp only [e₁, e₂, e₃, e₄, e₅] at j₁ j₂
    rw [toNat_array_eq_valAt, toNat_eq_valAt x, toNat_eq_valAt y]
    rw [show (WordArray.joinW UInt32Array _ x.array _ _ y.array _ _ _ _).size = k + x.size from j₁]
    exact j₂
  · have e : join32 k x y = (ofNat (toNat x * 2 ^ (32 * k) + toNat y % 2 ^ (32 * k))).toSlice := by
      simp only [join32, h, ↓reduceDIte]
    rw [e, toNat_toSlice, ← toNat_toSlice, toNat_ofNat]

/-- The operations of `NatOps` on slices of 32-bit limbs, with the division `div`. -/
@[expose] public def ops32With (div : UInt32Array.Slice → UInt32Array.Slice →
      UInt32Array.Slice × UInt32Array.Slice)
    (hdiv : ∀ x y, toNat y ≠ 0 →
      toNat (div x y).1 = toNat x / toNat y ∧ toNat (div x y).2 = toNat x % toNat y) :
    NatOps UInt32Array.Slice where
  B := 2 ^ 32
  one_lt_B := by decide
  val := toNat
  size := fun x => x.size
  val_lt x := by rw [← Nat.pow_mul]; exact toNat_lt x
  mul x y :=
    let r := (mulLimbs x y).toSlice
    r.slice 0 (topSize r)
  val_mul x y := by
    show toNat ((mulLimbs x y).toSlice.slice 0 (topSize _)) = _
    rw [toNat_slice_topSize]; exact isMul_mulLimbs.toNat_eq x y
  sqr x :=
    let r := (sqrLimbs x).toSlice
    r.slice 0 (topSize r)
  val_sqr x := by
    show toNat ((sqrLimbs x).toSlice.slice 0 (topSize _)) = _
    rw [toNat_slice_topSize]; exact toNat_sqrLimbs x
  add x y :=
    let r := (addLimbs x y).toSlice
    r.slice 0 (topSize r)
  val_add x y := by
    show toNat ((addLimbs x y).toSlice.slice 0 (topSize _)) = _
    rw [toNat_slice_topSize]; exact toNat_addLimbs x y
  sub x y :=
    let r := (subLimbs x (y.slice 0 x.size)).toSlice
    r.slice 0 (topSize r)
  val_sub x y h := by
    show toNat ((subLimbs x (y.slice 0 x.size)).toSlice.slice 0 (topSize _)) = _
    rw [toNat_slice_topSize]; exact toNat_sub_slice x y h
  le x y := !(lt y x)
  le_iff x y := by
    rw [Bool.not_eq_true', Bool.eq_false_iff, ne_eq, lt_iff]
    lia
  lo k x := x.slice 0 k
  val_lo k x := toNat_slice_lo x k
  hi k x := x.slice k x.size
  val_hi k x := toNat_slice_hi x k
  size_hi k x := by simp
  shl k x := (UInt32Array.replicate k 0 ++ x.copy).toSlice
  val_shl k x := toNat_shl k x
  join := join32
  val_join := toNat_join32
  pow k := ((UInt32Array.replicate k 0).push 1).toSlice
  val_pow k := toNat_pow k
  one := ((UInt32Array.replicate 0 0).push 1).toSlice
  val_one := by rw [toNat_pow, Nat.pow_zero]
  -- The FFT's wrapped product (`Dispatch.mulModW`) on the windows of the slices, trimmed.
  mulModSize n := Dispatch.modSize config.mul.fftKFactor n
  le_mulModSize n := Dispatch.le_modSize ..
  mulMod n x y :=
    let r := (Dispatch.mulModW config.mul n x.array x.start x.size y.array y.start y.size).toSlice
    r.slice 0 (topSize r)
  val_mulMod n x y := by
    show toNat ((Dispatch.mulModW config.mul n x.array x.start x.size y.array y.start
      y.size).toSlice.slice 0 (topSize _)) % _ = _
    rw [toNat_slice_topSize, toNat_array_eq_valAt, toNat_eq_valAt x, toNat_eq_valAt y,
      ← Nat.pow_mul]
    exact Dispatch.mulModW_spec config.mul n _ _ _ _ _ _
  divRem := div
  val_divRem := hdiv

/-- The instance with the schoolbook division, for the divide-and-conquer division over it. -/
@[expose] public def ops32B : NatOps UInt32Array.Slice := ops32With divBase32 val_divBase32

@[simp] public theorem ops32B_val (x : UInt32Array.Slice) : ops32B.val x = toNat x := rfl

@[simp] public theorem ops32B_B : ops32B.B = 2 ^ 32 := rfl

/--
`(r / v, r % v)` by `main`'s division of a normalized divisor on `ops32B` (`Dispatch.divN`), with
`divBase32` below `c.divDC` limbs, as arrays.
-/
public def dcGen (c : Dispatch.DivConfig) (r : UInt32Array) (v : UInt32Array.Slice) :
    UInt32Array × UInt32Array :=
  let p := Dispatch.divN ops32B c divBase32 r.toSlice v v.size (r.size + 1 - v.size)
  (p.1.copy, p.2.copy)

/-- `r / v` as in `dcGen`, without the remainder (`Dispatch.divQN`). -/
public def dcGenQ (c : Dispatch.DivConfig) (r : UInt32Array) (v : UInt32Array.Slice) :
    UInt32Array :=
  (Dispatch.divQN ops32B c divBase32 r.toSlice v v.size (r.size + 1 - v.size)).copy

/-- The bounds of `Dispatch.divN` on a divisor whose top limb is not zero. -/
private theorem dc_bounds (r : UInt32Array) (v : UInt32Array.Slice) (hn : 2 ≤ v.size)
    (hvt : v[v.size - 1]'(by lia) ≠ 0) :
    0 < toNat v ∧ toNat r.toSlice < toNat v * (2 ^ 32) ^ (r.size + 1 - v.size) := by
  -- `v ≥ β^(v.size - 1)`, so `r < v β^(r.size + 1 - v.size)`.
  have htop : 2 ^ (32 * (v.size - 1)) ≤ toNat v := by
    have h := toNat_slice_add_toNat_slice v (v.size - 1) (by lia)
    have e : toNat (v.slice (v.size - 1) v.size) = (v[v.size - 1]'(by lia)).toNat := by
      rw [toNat_of_size_eq_one (by simp; lia)]
      simp
    have : 1 ≤ (v[v.size - 1]'(by lia)).toNat := by
      rcases Nat.eq_zero_or_pos (v[v.size - 1]'(by lia)).toNat with h' | h'
      · exact absurd (UInt32.toNat_inj.1 (by simpa using h')) hvt
      · exact h'
    have := Nat.mul_le_mul_left (2 ^ (32 * (v.size - 1))) this
    rw [e] at h
    lia
  have hr : toNat r.toSlice < 2 ^ (32 * r.size) := by
    have := toNat_lt r.toSlice; simpa using this
  refine ⟨Nat.lt_of_lt_of_le (Nat.two_pow_pos _) htop, ?_⟩
  rw [← Nat.pow_mul]
  calc toNat r.toSlice < 2 ^ (32 * r.size) := hr
    _ ≤ 2 ^ (32 * (v.size - 1)) * 2 ^ (32 * (r.size + 1 - v.size)) := by
        rw [← Nat.pow_add]; exact Nat.pow_le_pow_right (by decide) (by lia)
    _ ≤ toNat v * 2 ^ (32 * (r.size + 1 - v.size)) := Nat.mul_le_mul_right _ htop

private theorem hbase32 : ∀ U V, 0 < ops32B.val V →
    ops32B.val (divBase32 U V).1 = ops32B.val U / ops32B.val V ∧
      ops32B.val (divBase32 U V).2 = ops32B.val U % ops32B.val V :=
  fun U V h => val_divBase32 U V (by simp only [ops32B_val] at h; lia)

private theorem dcGen_spec (c : Dispatch.DivConfig) (r : UInt32Array) (v : UInt32Array.Slice)
    (hn : 2 ≤ v.size) (hvt : v[v.size - 1]'(by lia) ≠ 0) :
    toNat (dcGen c r v).1 * toNat v + toNat (dcGen c r v).2 = toNat r ∧
      toNat (dcGen c r v).2 < toNat v := by
  obtain ⟨hV, hrv⟩ := dc_bounds r v hn hvt
  obtain ⟨h₁, h₂⟩ := Dispatch.divN_spec c hbase32 (U := r.toSlice) (V := v)
    (n := v.size) (k := r.size + 1 - v.size)
    (by simp only [ops32B_val]; exact hV)
    (by simp only [ops32B_val, ops32B_B]; rw [← Nat.pow_mul]; exact toNat_lt v)
    (by simp only [ops32B_val, ops32B_B]; exact hrv)
  simp only [ops32B_val] at h₁ h₂
  simp only [dcGen, toNat_copy]
  rw [h₁, h₂]
  refine ⟨?_, Nat.mod_lt _ hV⟩
  have := Nat.div_add_mod (toNat r.toSlice) (toNat v)
  rw [Nat.mul_comm] at this
  exact this

private theorem toNat_dcGenQ (c : Dispatch.DivConfig) (r : UInt32Array) (v : UInt32Array.Slice)
    (hn : 2 ≤ v.size) (hvt : v[v.size - 1]'(by lia) ≠ 0) :
    toNat (dcGenQ c r v) = toNat r / toNat v := by
  obtain ⟨hV, hrv⟩ := dc_bounds r v hn hvt
  have h := Dispatch.divQN_spec c hbase32 (U := r.toSlice) (V := v)
    (n := v.size) (k := r.size + 1 - v.size)
    (by simp only [ops32B_val]; exact hV)
    (by simp only [ops32B_val, ops32B_B]; rw [← Nat.pow_mul]; exact toNat_lt v)
    (by simp only [ops32B_val, ops32B_B]; exact hrv)
  simp only [ops32B_val] at h
  simp only [dcGenQ, toNat_copy]
  rw [h, toNat_toSlice]

/-! ## Normalized division -/

/-- The shift that brings the top bit of `vt ≠ 0` to the top of the limb. -/
@[expose] public def normShift (vt : UInt32) : Nat := (31 - vt.log2).toNat % 32

/-- `x 2ˢ`, for `s < 32`, in `x.size + 1` limbs, by `main`'s `Schoolbook.shlTop`. -/
public def shlNorm (x : UInt32Array.Slice) (s : Nat) : UInt32Array :=
  if h : x.start + x.size + 1 < USize.size then
    Schoolbook.shlTop x.array x.start.toUSize x.size.toUSize (window_bound x (by lia))
      (by rw [toNat_toUSize (by lia)]; lia) s
  else ofNat (toNat x * 2 ^ s)

/-- `⌊r / 2ˢ⌋`, for `s < 32`, in `r.size` limbs, by `main`'s `Schoolbook.shrArr`. -/
public def shrNorm (r : UInt32Array) (s : Nat) : UInt32Array :=
  if r.size < USize.size then Schoolbook.shrArr r s else ofNat (toNat r / 2 ^ s)

public theorem toNat_shlNorm (x : UInt32Array.Slice) (s : Nat) (hs : s < 32) :
    toNat (shlNorm x s) = toNat x * 2 ^ s := by
  by_cases h : x.start + x.size + 1 < USize.size
  · rw [shlNorm, dite_eq_left h]
    obtain ⟨h₁, h₂⟩ := Schoolbook.shlTop_spec (A := UInt32Array) x.array x.start.toUSize
      x.size.toUSize (window_bound x (by lia)) (by rw [toNat_toUSize (by lia)]; lia) s hs
    simp only [toNat_toUSize (show x.start < USize.size by lia),
      toNat_toUSize (show x.size < USize.size by lia)] at h₁ h₂
    rw [toNat_toSlice, Nat.sub_zero, toNat_eq_valAt]
    exact (congrArg (fun k => LimbArray.valAt _ 0 k) h₁).trans h₂
  · rw [shlNorm, dite_eq_right h]
    exact toNat_ofNat _

public theorem toNat_shrNorm (r : UInt32Array) (s : Nat) (hs : s < 32) :
    toNat (shrNorm r s) = toNat r / 2 ^ s := by
  by_cases h : r.size < USize.size
  · rw [shrNorm, ite_eq_left h]
    have := Schoolbook.shrArr_spec r s hs h
    rw [toNat_toSlice, toNat_toSlice, Nat.sub_zero, Nat.sub_zero]
    exact this.2
  · rw [shrNorm, ite_eq_right h]
    exact toNat_ofNat _

/--
The division of the normalized dividend, an array of its own: below `c.divDC` limbs in the
divisor by `divRemBasecase`, and from `c.divDC` on by `main`'s division by blocks or by a
reciprocal (`dcGen`).
-/
public def divRemNormWith (c : Dispatch.DivConfig) (r : UInt32Array) (v : UInt32Array.Slice)
    (hn : 2 ≤ v.size) : UInt32Array × UInt32Array :=
  if v.size < c.divDC then divRemBasecase div32RecipU r.toSlice v hn else dcGen c r v

/-- The quotient of `divRemNormWith`, from `c.divDC` limbs without the remainder (`dcGenQ`). -/
public def divQNormWith (c : Dispatch.DivConfig) (r : UInt32Array) (v : UInt32Array.Slice)
    (hn : 2 ≤ v.size) : UInt32Array :=
  if v.size < c.divDC then (divRemBasecase div32RecipU r.toSlice v hn).1 else dcGenQ c r v

public theorem divRemNormWith_spec (c : Dispatch.DivConfig) (r : UInt32Array)
    (v : UInt32Array.Slice) (hn : 2 ≤ v.size) (hvt : v[v.size - 1]'(by lia) ≠ 0) :
    toNat (divRemNormWith c r v hn).1 * toNat v + toNat (divRemNormWith c r v hn).2 = toNat r ∧
      toNat (divRemNormWith c r v hn).2 < toNat v := by
  by_cases h : v.size < c.divDC
  · have e : divRemNormWith c r v hn = divRemBasecase div32RecipU r.toSlice v hn := by
      unfold divRemNormWith
      rw [ite_eq_left h]
    rw [e]
    exact divRemBasecase_spec div32RecipU r.toSlice v hn hvt
  · have e : divRemNormWith c r v hn = dcGen c r v := by
      unfold divRemNormWith
      rw [ite_eq_right h]
    rw [e]
    exact dcGen_spec c r v hn hvt

/-- `divQNormWith` has the quotient of `divRemNormWith`. -/
private theorem toNat_divQNormWith (c : Dispatch.DivConfig) (r : UInt32Array)
    (v : UInt32Array.Slice) (hn : 2 ≤ v.size) (hvt : v[v.size - 1]'(by lia) ≠ 0) :
    toNat (divQNormWith c r v hn) = toNat (divRemNormWith c r v hn).1 := by
  obtain ⟨hV, -⟩ := dc_bounds r v hn hvt
  obtain ⟨h₁, h₂⟩ := divRemNormWith_spec c r v hn hvt
  by_cases h : v.size < c.divDC
  · have e : divQNormWith c r v hn = (divRemBasecase div32RecipU r.toSlice v hn).1 := by
      unfold divQNormWith
      rw [ite_eq_left h]
    have e' : divRemNormWith c r v hn = divRemBasecase div32RecipU r.toSlice v hn := by
      unfold divRemNormWith
      rw [ite_eq_left h]
    rw [e, e']
  · have e : divQNormWith c r v hn = dcGenQ c r v := by
      unfold divQNormWith
      rw [ite_eq_right h]
    rw [e, toNat_dcGenQ c r v hn hvt, (div_mod_eq hV h₁ h₂).1]

/-- `divRemNormWith` with the thresholds of `config`. -/
def divRemNorm (r : UInt32Array) (v : UInt32Array.Slice) (hn : 2 ≤ v.size) :
    UInt32Array × UInt32Array :=
  divRemNormWith config.toDivConfig r v hn

private theorem divRemNorm_spec (r : UInt32Array) (v : UInt32Array.Slice) (hn : 2 ≤ v.size)
    (hvt : v[v.size - 1]'(by lia) ≠ 0) :
    toNat (divRemNorm r v hn).1 * toNat v + toNat (divRemNorm r v hn).2 = toNat r ∧
      toNat (divRemNorm r v hn).2 < toNat v :=
  divRemNormWith_spec config.toDivConfig r v hn hvt

/--
`u / v` and `u % v` for a divisor of at least two limbs with a nonzero top limb, untrimmed, from
`config.divDC` limbs: `u` and `v` are normalized, divided with `divRemNorm`, and the remainder
shifted back.
-/
def divModLimbsDC (u v : UInt32Array.Slice) (hn : 2 ≤ v.size) : UInt32Array × UInt32Array :=
  let s := normShift (v[v.size - 1]'(by lia))
  let vf := shlNorm v s
  let v' := vf.toSlice.slice 0 (topSize vf)
  if h : 2 ≤ v'.size then
    let p := divRemNorm (shlNorm u s) v' h
    (p.1, shrNorm p.2 s)
  else
    divRemBasecase div32RecipU u v hn

/-- The quotient of `divModLimbsDC`, without shifting the remainder back. -/
def divLimbsQDC (u v : UInt32Array.Slice) (hn : 2 ≤ v.size) : UInt32Array :=
  let s := normShift (v[v.size - 1]'(by lia))
  let vf := shlNorm v s
  let v' := vf.toSlice.slice 0 (topSize vf)
  if h : 2 ≤ v'.size then
    divQNormWith config.toDivConfig (shlNorm u s) v' h
  else
    (divRemBasecase div32RecipU u v hn).1

private theorem toNat_divLimbsQDC (u v : UInt32Array.Slice) (hn : 2 ≤ v.size) :
    toNat (divLimbsQDC u v hn) = toNat (divModLimbsDC u v hn).1 := by
  unfold divLimbsQDC divModLimbsDC
  simp only [toNat_toSlice]
  split
  · rename_i h
    have hpos : 0 < topSize (shlNorm v (normShift (v[v.size - 1]'(by lia)))) := by
      simp only [UInt32Array.Slice.size_slice] at h
      lia
    rw [← toNat_toSlice, ← toNat_toSlice]
    exact toNat_divQNormWith _ _ _ h (top_slice_topSize_ne_zero _ hpos)
  · rfl

private theorem divModLimbsDC_spec (u v : UInt32Array.Slice) (hn : 2 ≤ v.size)
    (hvt : v[v.size - 1]'(by lia) ≠ 0) :
    toNat (divModLimbsDC u v hn).1 = toNat u / toNat v ∧
      toNat (divModLimbsDC u v hn).2 = toNat u % toNat v := by
  have hvt' : 0 < (v[v.size - 1]'(by lia)).toNat := by
    rcases Nat.eq_zero_or_pos (v[v.size - 1]'(by lia)).toNat with h | h
    · exact absurd (UInt32.toNat_inj.1 (by simpa using h)) hvt
    · exact h
  have hVpos : 0 < toNat v := by
    have := toNat_lt_topSize v
    have htop : (v[v.size - 1]'(by lia)).toNat ≤ toNat v := by
      have h := toNat_slice_add_toNat_slice v (v.size - 1) (by lia)
      have : toNat (v.slice (v.size - 1) v.size) = (v[v.size - 1]'(by lia)).toNat := by
        rw [toNat_of_size_eq_one (by simp; lia)]
        simp
      have := Nat.mul_le_mul_right (toNat (v.slice (v.size - 1) v.size))
        (Nat.one_le_two_pow (n := 32 * (v.size - 1)))
      lia
    lia
  have hs : normShift (v[v.size - 1]'(by lia)) < 32 := Nat.mod_lt _ (by decide)
  simp only [divModLimbsDC]
  split
  · rename_i h
    -- Normalized: `u 2ˢ = q (v 2ˢ) + r'` with `r' < v 2ˢ`, and `r' = r 2ˢ`.
    generalize normShift (v[v.size - 1]'(by lia)) = s at *
    have hF : 0 < 2 ^ s := Nat.two_pow_pos _
    have hv' : toNat ((shlNorm v s).toSlice.slice 0 (topSize (shlNorm v s))) = toNat v * 2 ^ s := by
      rw [toNat_slice_topSize, toNat_shlNorm _ _ hs]
    have hpos : 0 < topSize (shlNorm v s) := by
      simp only [UInt32Array.Slice.size_slice] at h
      lia
    obtain ⟨h₁, h₂⟩ := divRemNorm_spec (shlNorm u s) _ h (top_slice_topSize_ne_zero _ hpos)
    rw [hv', toNat_shlNorm _ _ hs] at h₁
    rw [hv'] at h₂
    obtain ⟨hq, hr⟩ := div_mod_eq (Nat.mul_pos hVpos hF) h₁ h₂
    rw [Nat.mul_div_mul_right _ _ hF] at hq
    rw [Nat.mul_mod_mul_right] at hr
    rw [dite_eq_left h]
    refine ⟨hq, ?_⟩
    rw [toNat_shrNorm _ _ hs, hr, Nat.mul_div_cancel _ hF]
  · -- The fallback, without normalization.
    rename_i h
    rw [dite_eq_right h]
    obtain ⟨h₁, h₂⟩ := divRemBasecase_spec div32RecipU u v hn hvt
    obtain ⟨hq, hr⟩ := div_mod_eq hVpos h₁ h₂
    exact ⟨hq, hr⟩

/--
`u / v` and `u % v` for a divisor of at least two limbs with a nonzero top limb, untrimmed: by
`divRemBasecase` below `config.divDC` limbs in the divisor, which normalizes by shifts, and by
`divModLimbsDC` from there.
-/
def divModLimbs (u v : UInt32Array.Slice) (hn : 2 ≤ v.size) : UInt32Array × UInt32Array :=
  if v.size < config.divDC then divRemBasecase div32RecipU u v hn else divModLimbsDC u v hn

/-- The quotient of `divModLimbs`. -/
def divLimbsQ (u v : UInt32Array.Slice) (hn : 2 ≤ v.size) : UInt32Array :=
  if v.size < config.divDC then (divRemBasecase div32RecipU u v hn).1 else divLimbsQDC u v hn

private theorem toNat_divLimbsQ (u v : UInt32Array.Slice) (hn : 2 ≤ v.size) :
    toNat (divLimbsQ u v hn) = toNat (divModLimbs u v hn).1 := by
  unfold divLimbsQ divModLimbs
  by_cases h : v.size < config.divDC
  · rw [ite_eq_left h, ite_eq_left h]
  · rw [ite_eq_right h, ite_eq_right h]
    exact toNat_divLimbsQDC u v hn

private theorem divModLimbs_spec (u v : UInt32Array.Slice) (hn : 2 ≤ v.size)
    (hvt : v[v.size - 1]'(by lia) ≠ 0) :
    toNat (divModLimbs u v hn).1 = toNat u / toNat v ∧
      toNat (divModLimbs u v hn).2 = toNat u % toNat v := by
  unfold divModLimbs
  by_cases h : v.size < config.divDC
  · rw [ite_eq_left h]
    obtain ⟨h₁, h₂⟩ := divRemBasecase_spec div32RecipU u v hn hvt
    exact div_mod_eq (Nat.lt_of_le_of_lt (Nat.zero_le _) h₂) h₁ h₂
  · rw [ite_eq_right h]
    exact divModLimbsDC_spec u v hn hvt

/-! ## Division -/

/-- `(a / b, a % b)`, trimmed, by Algorithm D and division by blocks. -/
public def divModSlow (a b : UInt32Array.Slice) : UInt32Array × UInt32Array :=
  let n := topSize b
  if h₀ : n = 0 then
    (.empty, trim a.copy)
  else if h : n = 1 then
    let p := divRem1 a (b.getD 0 0)
    (trim p.1, trim (UInt32Array.mk #[p.2]))
  else if n = 2 then
    let p := divRem2 a (b.getD 1 0) (b.getD 0 0)
    (trim p.1, ofWord64 p.2)
  else
    let p := divModLimbs a (b.slice 0 n) (by simp; have := topSize_le b; lia)
    (trim p.1, trim p.2)

/-- `divModSlow` without the remainder. -/
public def divSlow (a b : UInt32Array.Slice) : UInt32Array :=
  let n := topSize b
  if n = 0 then
    .empty
  else if n = 1 then
    trim (divRem1 a (b.getD 0 0)).1
  else if n = 2 then
    trim (div2 a (b.getD 1 0) (b.getD 0 0))
  else if h : 2 ≤ n then
    trim (divLimbsQ a (b.slice 0 n) (by simp; have := topSize_le b; lia))
  else
    .empty

private theorem isTrimmed_divSlow (a b : UInt32Array.Slice) : isTrimmed (divSlow a b) = true := by
  unfold divSlow
  dsimp only
  split
  · exact isTrimmed_empty
  · split
    · exact isTrimmed_trim _
    · split
      · exact isTrimmed_trim _
      · split
        · exact isTrimmed_trim _
        · exact isTrimmed_empty

private theorem divModSlow_of_topSize_eq_zero (a b : UInt32Array.Slice) (h : topSize b = 0) :
    divModSlow a b = (.empty, trim a.copy) := by
  simp [divModSlow, h]

private theorem divModSlow_of_topSize_eq_one (a b : UInt32Array.Slice) (h : topSize b = 1) :
    divModSlow a b = (trim (divRem1 a (b.getD 0 0)).1,
      trim (UInt32Array.mk #[(divRem1 a (b.getD 0 0)).2])) := by
  simp [divModSlow, h]

private theorem divModSlow_of_topSize_eq_two (a b : UInt32Array.Slice) (h : topSize b = 2) :
    divModSlow a b = (trim (divRem2 a (b.getD 1 0) (b.getD 0 0)).1,
      ofWord64 (divRem2 a (b.getD 1 0) (b.getD 0 0)).2) := by
  simp [divModSlow, h]

private theorem divModSlow_of_two_le_topSize (a b : UInt32Array.Slice) (h : 3 ≤ topSize b) :
    divModSlow a b = (trim (divModLimbs a (b.slice 0 (topSize b))
        (by simp; have := topSize_le b; lia)).1,
      trim (divModLimbs a (b.slice 0 (topSize b)) (by simp; have := topSize_le b; lia)).2) := by
  simp [divModSlow, show topSize b ≠ 0 by lia, show topSize b ≠ 1 by lia,
    show topSize b ≠ 2 by lia]

/-- `divModSlow` divides, with `Nat`'s conventions for a zero divisor. -/
public theorem toNat_divModSlow (a b : UInt32Array.Slice) :
    toNat (divModSlow a b).1 = toNat a / toNat b ∧
      toNat (divModSlow a b).2 = toNat a % toNat b := by
  have hb := toNat_slice_topSize b
  have hle := topSize_le b
  rcases Nat.lt_or_ge (topSize b) 2 with h | h
  · rcases Nat.lt_or_ge (topSize b) 1 with h' | h'
    · -- A zero divisor.
      have h₀ : topSize b = 0 := by lia
      have : toNat b = 0 := by
        rw [← hb, toNat_of_size_eq_zero (by simp [h₀])]
      rw [divModSlow_of_topSize_eq_zero a b h₀, this, Nat.div_zero, Nat.mod_zero]
      exact ⟨rfl, by rw [toNat_trim, toNat_copy]⟩
    · -- A divisor of one limb.
      have h₁ : topSize b = 1 := by lia
      have hd := getD_topSize_ne_zero b (by lia)
      rw [h₁] at hd
      have hb1 : toNat b = (b.getD 0 0).toNat := by
        rw [← hb, toNat_of_size_eq_one (by simp [h₁]; lia)]
        simp [UInt32Array.Slice.getD_eq, show 0 < b.size by lia]
      have hd' : 0 < (b.getD 0 0).toNat := by
        rcases Nat.eq_zero_or_pos (b.getD 0 0).toNat with h | h
        · exact absurd (UInt32.toNat_inj.1 (by simpa using h)) hd
        · exact h
      obtain ⟨h₂, h₃⟩ := divRem1_spec a (b.getD 0 0) hd
      obtain ⟨hq, hr⟩ := div_mod_eq hd' h₂ h₃
      rw [divModSlow_of_topSize_eq_one a b h₁, hb1, toNat_trim, toNat_trim, ← hq, ← hr]
      refine ⟨rfl, ?_⟩
      rw [toNat_toSlice]
      simp
  · rcases Nat.lt_or_ge (topSize b) 3 with h₃ | h₃
    · -- A divisor of two limbs.
      have h₂ : topSize b = 2 := by lia
      have hd := getD_topSize_ne_zero b (by lia)
      rw [h₂] at hd
      have hb2 : toNat b = (b.getD 1 0).toNat * 2 ^ 32 + (b.getD 0 0).toNat := by
        rw [← hb, toNat_of_size_eq_two (by simp [h₂]; lia)]
        simp only [UInt32Array.Slice.getD_eq, UInt32Array.Slice.size_slice,
          UInt32Array.Slice.getElem_slice]
        simp [show 0 < min 2 b.size by lia, show 1 < min 2 b.size by lia, h₂,
          show 0 < b.size by lia, show 1 < b.size by lia]
        lia
      have hd' : b.getD 1 0 ≠ 0 := by simpa using hd
      obtain ⟨h₄, h₅⟩ := divRem2_spec a (b.getD 1 0) (b.getD 0 0) hd'
      rw [← hb2] at h₄ h₅
      obtain ⟨hq, hr⟩ := div_mod_eq (by lia) h₄ h₅
      rw [divModSlow_of_topSize_eq_two a b h₂, toNat_trim, toNat_ofWord64, ← hq, ← hr]
      exact ⟨rfl, rfl⟩
    -- A divisor of at least three limbs.
    have hs := divModLimbs_spec a (b.slice 0 (topSize b))
      (by simp; lia) (top_slice_topSize_ne_zero b (by lia))
    rw [hb] at hs
    rw [divModSlow_of_two_le_topSize a b h₃, toNat_trim, toNat_trim]
    exact hs

/-! ## Whole-number operations on 32-bit limbs

`ops32` is the instance of `NatOps` for slices of 32-bit limbs, which runs the base-generic
algorithms (`Generic.Barrett`) on the operations of this library, with `divModSlow` as their
fallback.
-/

/-- The operations of `NatOps` on slices of 32-bit limbs, with `divModSlow`. -/
@[expose] public def ops32 : NatOps UInt32Array.Slice :=
  ops32With (fun x y => ((divModSlow x y).1.toSlice, (divModSlow x y).2.toSlice))
    fun x y _ => toNat_divModSlow x y

private theorem isTrimmed_divModSlow_fst (a b : UInt32Array.Slice) :
    isTrimmed (divModSlow a b).1 = true := by
  rcases Nat.lt_or_ge (topSize b) 2 with h | h
  · rcases Nat.lt_or_ge (topSize b) 1 with h' | h'
    · rw [divModSlow_of_topSize_eq_zero a b (by lia)]
      exact isTrimmed_empty
    · rw [divModSlow_of_topSize_eq_one a b (by lia)]
      exact isTrimmed_trim _
  · rcases Nat.lt_or_ge (topSize b) 3 with h₃ | h₃
    · rw [divModSlow_of_topSize_eq_two a b (by lia)]
      exact isTrimmed_trim _
    · rw [divModSlow_of_two_le_topSize a b h₃]
      exact isTrimmed_trim _

private theorem isTrimmed_divModSlow_snd (a b : UInt32Array.Slice) :
    isTrimmed (divModSlow a b).2 = true := by
  rcases Nat.lt_or_ge (topSize b) 2 with h | h
  · rcases Nat.lt_or_ge (topSize b) 1 with h' | h'
    · rw [divModSlow_of_topSize_eq_zero a b (by lia)]
      exact isTrimmed_trim _
    · rw [divModSlow_of_topSize_eq_one a b (by lia)]
      exact isTrimmed_trim _
  · rcases Nat.lt_or_ge (topSize b) 3 with h₃ | h₃
    · rw [divModSlow_of_topSize_eq_two a b (by lia)]
      exact isTrimmed_ofWord64 _
    · rw [divModSlow_of_two_le_topSize a b h₃]
      exact isTrimmed_trim _

@[simp] public theorem ops32_val (x : UInt32Array.Slice) : ops32.val x = toNat x := rfl

private theorem toNat_divSlow (a b : UInt32Array.Slice) :
    toNat (divSlow a b) = toNat (divModSlow a b).1 := by
  by_cases h₀ : topSize b = 0
  · have e : divSlow a b = .empty := by simp [divSlow, h₀]
    rw [e, divModSlow_of_topSize_eq_zero a b h₀]
  by_cases h₁ : topSize b = 1
  · have e : divSlow a b = trim (divRem1 a (b.getD 0 0)).1 := by simp [divSlow, h₁]
    rw [e, divModSlow_of_topSize_eq_one a b h₁]
  by_cases h₂ : topSize b = 2
  · have e : divSlow a b = trim (divRem2 a (b.getD 1 0) (b.getD 0 0)).1 := by
      simp [divSlow, h₂, div2_eq]
    rw [e, divModSlow_of_topSize_eq_two a b h₂]
  have e : divSlow a b =
      trim (divLimbsQ a (b.slice 0 (topSize b)) (by simp; have := topSize_le b; lia)) := by
    simp [divSlow, h₀, h₁, h₂, show 2 ≤ topSize b by lia]
  rw [e, divModSlow_of_two_le_topSize a b (by lia), toNat_trim, toNat_trim, toNat_divLimbsQ]

/-! ## Division -/

/--
`(a / b, a % b)`, trimmed: by Algorithm D, and from `config.divDC` limbs of divisor by division by
blocks or, from `config.divMu`, by Barrett's division with Newton's reciprocal (`divModSlow`).
-/
public def divMod (a b : UInt32Array.Slice) : UInt32Array × UInt32Array := divModSlow a b

/--
Divides two numbers, with `a / 0 = 0`: `divMod` without the remainder, by Barrett's division
without the remainder of its last block from `config.divQMu` limbs of divisor (`divSlow`).
-/
public def div (a b : UInt32Array.Slice) : UInt32Array := divSlow a b

/-- The remainder of dividing two numbers, with `a % 0 = a`. -/
public def mod (a b : UInt32Array.Slice) : UInt32Array := (divMod a b).2

/-- `divMod` divides, with `Nat`'s conventions for a zero divisor. -/
public theorem toNat_divMod (a b : UInt32Array.Slice) :
    toNat (divMod a b).1 = toNat a / toNat b ∧ toNat (divMod a b).2 = toNat a % toNat b :=
  toNat_divModSlow a b

/-- Division is `Nat` division. -/
@[simp] public theorem toNat_div (a b : UInt32Array.Slice) :
    toNat (div a b) = toNat a / toNat b := by
  rw [div, toNat_divSlow]
  exact (toNat_divModSlow a b).1

/-- The remainder is `Nat`'s remainder. -/
@[simp] public theorem toNat_mod (a b : UInt32Array.Slice) : toNat (mod a b) = toNat a % toNat b :=
  (toNat_divMod a b).2

public theorem isTrimmed_div (a b : UInt32Array.Slice) : isTrimmed (div a b) = true :=
  isTrimmed_divSlow a b

public theorem isTrimmed_mod (a b : UInt32Array.Slice) : isTrimmed (mod a b) = true :=
  isTrimmed_divModSlow_snd a b

end MPN.W32
