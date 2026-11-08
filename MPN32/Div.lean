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
public import MPN.Div.Driver
public import MPN.Generic.OpsArray

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

/-- The limbs of a slice below `2³² - 1` limbs are a loop on machine indices. -/
private theorem topSize_bound (s : UInt32Array.Slice) (hs : s.array.size < 4294967295) :
    WordArray.LoopBound s.array s.start.toUSize s.size.toUSize := by
  have := s.stop_le_array_size; have := s.start_le_stop; have := s.size_eq
  have := USize.le_size
  simp only [WordArray.LoopBound]
  rw [toNat_toUSize (by lia), toNat_toUSize (by lia)]
  exact ⟨show s.start + s.size ≤ s.array.size by lia, by lia⟩

/--
The number of limbs of `s` without its trailing zero limbs: by `WordArray.topLenW` on machine
indices, and by `topSizeLoop` on `Nat`s were the array not below `2³² - 1` limbs.
-/
public def topSize (s : UInt32Array.Slice) : Nat :=
  if hs : s.array.size < 4294967295 then
    (WordArray.topLenW s.array s.start.toUSize s.size.toUSize (topSize_bound s hs)).toNat
  else topSizeLoop s s.size

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

private theorem topSize_spec (s : UInt32Array.Slice) :
    topSize s ≤ s.size ∧ (∀ k, topSize s ≤ k → k < s.size → s.getD k 0 = 0) ∧
      (0 < topSize s → s.getD (topSize s - 1) 0 ≠ 0) := by
  unfold topSize
  split
  · rename_i hs
    have := s.stop_le_array_size; have := s.start_le_stop; have := s.size_eq
    have := USize.le_size
    obtain ⟨h₁, h₂, h₃⟩ := WordArray.topLenW_spec s.array _ _ (topSize_bound s hs)
    have e₁ : s.start.toUSize.toNat = s.start := toNat_toUSize (by lia)
    have e₂ : s.size.toUSize.toNat = s.size := toNat_toUSize (by lia)
    simp only [e₁, e₂] at h₁ h₂ h₃
    have e : ∀ k, k < s.size → s.getD k 0 = s.array[s.start + k]! := fun k hk => by
      rw [UInt32Array.Slice.getD_eq, dite_eq_left hk, UInt32Array.Slice.getElem_eq_getElem!]
    refine ⟨h₁, fun k hk hks => ?_, fun hp => ?_⟩
    · rw [e k hks]; exact UInt32.toNat_inj.1 (h₂ k hk hks)
    · rw [e _ (by lia), ← Nat.add_sub_assoc hp]
      exact fun h => h₃ hp (by change UInt32.toNat s.array[_]! = 0; rw [h]; rfl)
  · exact topSizeLoop_spec s s.size

public theorem topSize_le (s : UInt32Array.Slice) : topSize s ≤ s.size :=
  (topSize_spec s).1

/-- The top limb below `topSize s` is not zero. -/
public theorem getD_topSize_ne_zero (s : UInt32Array.Slice) (h : 0 < topSize s) :
    s.getD (topSize s - 1) 0 ≠ 0 :=
  (topSize_spec s).2.2 h

/-- Cutting `s` to `topSize s` limbs keeps its value. -/
public theorem toNat_slice_topSize (s : UInt32Array.Slice) :
    toNat (s.slice 0 (topSize s)) = toNat s := by
  have hle := topSize_le s
  have hz : ∀ k, topSize s ≤ k → k < s.size → s.getD k 0 = 0 := (topSize_spec s).2.1
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

private theorem toNat_slice_lo (s : UInt32Array.Slice) (k : Nat) :
    toNat (s.slice 0 k) = toNat s % (2 ^ 32) ^ k := by
  rw [toNat_slice, toNat_eq_valAt, Nat.sub_zero, Nat.add_zero, ← Nat.pow_mul]
  by_cases hk : k ≤ s.size
  · rw [Nat.min_eq_left hk, UInt32Array.valAt_mod _ _ hk]
  · rw [Nat.min_eq_right (by lia), Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le
      (UInt32Array.valAt_lt ..) (Nat.pow_le_pow_right (by decide) (by lia)))]

/--
`(u / v, u % v)` by the schoolbook method alone: the divisor is cut to its nonzero limbs, then
`divRem1` for one limb and `divRemBasecase` for more. The base case of `ops32B.divNorm`.
-/
public def divBase32 (u v : UInt32Array) : UInt32Array × UInt32Array :=
  let n := topSize v.toSlice
  if n = 1 then
    let p := divRem1 u.toSlice (v.toSlice.getD 0 0)
    (p.1, UInt32Array.mk #[p.2])
  else if h : 2 ≤ n then
    divRemBasecase div32RecipU u.toSlice (v.toSlice.slice 0 n)
      (by have := topSize_le v.toSlice; simp at this ⊢; lia)
  else (UInt32Array.empty, u)

public theorem val_divBase32 (u v : UInt32Array) (hv : toNat v ≠ 0) :
    toNat (divBase32 u v).1 = toNat u / toNat v ∧ toNat (divBase32 u v).2 = toNat u % toNat v := by
  have hb := toNat_slice_topSize v.toSlice
  have hle : topSize v.toSlice ≤ v.size := by have := topSize_le v.toSlice; simpa using this
  have hV : 0 < toNat v := by lia
  by_cases h₁ : topSize v.toSlice = 1
  · have e : divBase32 u v = ((divRem1 u.toSlice (v.toSlice.getD 0 0)).1,
        UInt32Array.mk #[(divRem1 u.toSlice (v.toSlice.getD 0 0)).2]) := by
      simp only [divBase32, h₁, ↓reduceIte]
    rw [e]
    have hd := getD_topSize_ne_zero v.toSlice (by lia)
    rw [h₁] at hd
    have hb1 : toNat v = (v.toSlice.getD 0 0).toNat := by
      rw [← hb, toNat_of_size_eq_one (by simp [h₁]; lia)]
      simp [UInt32Array.Slice.getD_eq, show 0 < v.size by lia]
    obtain ⟨h₂, h₃⟩ := divRem1_spec u.toSlice (v.toSlice.getD 0 0) hd
    rw [← hb1] at h₂ h₃
    obtain ⟨hq, hr⟩ := div_mod_eq hV h₂ h₃
    refine ⟨hq, ?_⟩
    rw [← hr, toNat_toSlice]
    simp
  · by_cases h : 2 ≤ topSize v.toSlice
    · have e : divBase32 u v = divRemBasecase div32RecipU u.toSlice
          (v.toSlice.slice 0 (topSize v.toSlice)) (by simp; lia) := by
        simp only [divBase32, h₁, h, ↓reduceIte, ↓reduceDIte]
      rw [e]
      obtain ⟨h₂, h₃⟩ := divRemBasecase_spec div32RecipU u.toSlice
        (v.toSlice.slice 0 (topSize v.toSlice)) (by simp; lia)
        (top_slice_topSize_ne_zero v.toSlice (by lia))
      rw [hb] at h₂ h₃
      exact div_mod_eq hV h₂ h₃
    · have h₀ : topSize v.toSlice = 0 := by lia
      have : toNat v = 0 := by rw [← hb, toNat_of_size_eq_zero (by simp [h₀])]
      lia

/-- The value of `main`'s shared instances is `toNat`. -/
public theorem vA_eq_toNat (x : UInt32Array) : WordArray.vA x = toNat x :=
  (toNat_array_eq_valAt x).symm

/-- The operations of this library for `main`'s `WordArray.opsA`, on the slices of the arrays. -/
@[expose] public def numOps32 : WordArray.ArrayOps UInt32Array where
  mul x y := mulLimbs x.toSlice y.toSlice
  val_mul x y _ := by
    rw [vA_eq_toNat, vA_eq_toNat, vA_eq_toNat]; exact isMul_mulLimbs.toNat_eq x.toSlice y.toSlice
  sqr x := sqrLimbs x.toSlice
  val_sqr x _ := by rw [vA_eq_toNat, vA_eq_toNat]; exact toNat_sqrLimbs x.toSlice
  add x y := addLimbs x.toSlice y.toSlice
  val_add x y _ := by
    rw [vA_eq_toNat, vA_eq_toNat, vA_eq_toNat]; exact toNat_addLimbs x.toSlice y.toSlice
  sub x y := subVal x y
  val_sub x y _ hle := by
    rw [vA_eq_toNat, vA_eq_toNat] at hle
    rw [vA_eq_toNat, vA_eq_toNat, vA_eq_toNat]; exact toNat_subVal x y hle

/--
The operations of `NatOps` on arrays of 32-bit limbs, with the division `div`: `main`'s
`WordArray.opsA` on `numOps32`, trimmed to no limbs, with the thresholds of `config.mul`.
-/
@[expose] public def ops32With (div : UInt32Array → UInt32Array → UInt32Array × UInt32Array)
    (hdiv : ∀ x y : UInt32Array, toNat y ≠ 0 →
      toNat (div x y).1 = toNat x / toNat y ∧ toNat (div x y).2 = toNat x % toNat y) :
    NatOps UInt32Array :=
  WordArray.opsA 0 numOps32 config.mul div fun x y h => by
    rw [vA_eq_toNat] at h
    rw [vA_eq_toNat, vA_eq_toNat, vA_eq_toNat, vA_eq_toNat]; exact hdiv x y h

/-- The instance with the schoolbook division, for the divide-and-conquer division over it. -/
@[expose] public def ops32B : NatOps UInt32Array := ops32With divBase32 val_divBase32

@[simp] public theorem ops32B_val (x : UInt32Array) : ops32B.val x = toNat x := vA_eq_toNat x

@[simp] public theorem ops32B_B : ops32B.B = 2 ^ 32 := rfl

/-! ## Division of several limbs -/

private theorem hbase32 : ∀ U V, 0 < ops32B.val V →
    ops32B.val (divBase32 U V).1 = ops32B.val U / ops32B.val V ∧
      ops32B.val (divBase32 U V).2 = ops32B.val U % ops32B.val V :=
  fun U V h => by
    simp only [ops32B_val] at h ⊢
    exact val_divBase32 U V (by lia)

/-- `main`'s `Div.divRemG` on `ops32B`: the numbers are the arrays themselves. -/
private theorem driverOK : MPN.Div.DriverOK ops32B divBase32 id id where
  B_eq := rfl
  val_toα _ := rfl
  val_ofα _ := rfl
  base_ok := hbase32

/--
`u / v` and `u % v` for a divisor of at least two limbs with a nonzero top limb, untrimmed, by
`main`'s `Div.divRemG` with the thresholds of `c`: Algorithm D below `c.divDC` limbs in the
divisor, and from there the normalized operands divided by blocks or by Barrett's method on
`ops32B`.
-/
public def divModLimbsWith (c : Dispatch.DivConfig) (u v : UInt32Array.Slice) :
    UInt32Array × UInt32Array :=
  MPN.Div.divRemG ops32B divBase32 id id c
    div32RecipU div2RowsU u.array u.start u.size v.array v.start v.size

/-- The quotient of `divModLimbsWith`, without the last remainder (`main`'s `Div.divQG`). -/
public def divQLimbsWith (c : Dispatch.DivConfig) (u v : UInt32Array.Slice) : UInt32Array :=
  MPN.Div.divQG ops32B divBase32 id id c
    div32RecipU div2RowsU u.array u.start u.size v.array v.start v.size

/-- The top limb of a slice, as a limb of its array. -/
private theorem top_get (v : UInt32Array.Slice) (hn : 2 ≤ v.size)
    (hvt : v[v.size - 1]'(by lia) ≠ 0) :
    LimbArray.val UInt32Array (LimbArray.get v.array (v.start + v.size - 1)) ≠ 0 := by
  intro e
  apply hvt
  rw [UInt32Array.Slice.getElem_eq_getElem!,
    show v.start + (v.size - 1) = v.start + v.size - 1 by lia]
  exact UInt32.toNat_inj.1 e

public theorem divModLimbsWith_spec (c : Dispatch.DivConfig) (u v : UInt32Array.Slice)
    (hn : 2 ≤ v.size) (hvt : v[v.size - 1]'(by lia) ≠ 0) :
    toNat (divModLimbsWith c u v).1 = toNat u / toNat v ∧
      toNat (divModLimbsWith c u v).2 = toNat u % toNat v := by
  have h := MPN.Div.divRemG_spec driverOK c div32RecipU div2RowsU u.array u.start u.size v.array
    v.start v.size hn (top_get v hn hvt)
  rw [toNat_array_eq_valAt, toNat_array_eq_valAt]
  exact h

public theorem toNat_divQLimbsWith (c : Dispatch.DivConfig) (u v : UInt32Array.Slice)
    (hn : 2 ≤ v.size) (hvt : v[v.size - 1]'(by lia) ≠ 0) :
    toNat (divQLimbsWith c u v) = toNat u / toNat v := by
  have h := MPN.Div.divQG_spec driverOK c div32RecipU div2RowsU u.array u.start u.size v.array
    v.start v.size hn (top_get v hn hvt)
  rw [toNat_array_eq_valAt]
  exact h

/-- `divModLimbsWith` with the thresholds of `config`. -/
def divModLimbs (u v : UInt32Array.Slice) : UInt32Array × UInt32Array :=
  divModLimbsWith config.toDivConfig u v

/-- `divQLimbsWith` with the thresholds of `config`. -/
def divLimbsQ (u v : UInt32Array.Slice) : UInt32Array := divQLimbsWith config.toDivConfig u v

/-! ## Division -/

/-- `(a / b, a % b)`, trimmed, by Algorithm D and division by blocks. -/
public def divModSlow (a b : UInt32Array.Slice) : UInt32Array × UInt32Array :=
  let n := topSize b
  if n = 0 then
    (.empty, trim a.copy)
  else if n = 1 then
    let p := divRem1 a (b.getD 0 0)
    (trim p.1, trim (UInt32Array.mk #[p.2]))
  else if n = 2 then
    let p := divRem2 a (b.getD 1 0) (b.getD 0 0)
    (trim p.1, ofWord64 p.2)
  else
    let p := divModLimbs a (b.slice 0 n)
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
  else if 2 ≤ n then
    trim (divLimbsQ a (b.slice 0 n))
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
    divModSlow a b = (trim (divModLimbs a (b.slice 0 (topSize b))).1,
      trim (divModLimbs a (b.slice 0 (topSize b))).2) := by
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
    have hs := divModLimbsWith_spec config.toDivConfig a (b.slice 0 (topSize b))
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
@[expose] public def ops32 : NatOps UInt32Array :=
  ops32With (fun x y => divModSlow x.toSlice y.toSlice) fun x y _ =>
    toNat_divModSlow x.toSlice y.toSlice

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

@[simp] public theorem ops32_val (x : UInt32Array) : ops32.val x = toNat x := vA_eq_toNat x

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
  have e : divSlow a b = trim (divLimbsQ a (b.slice 0 (topSize b))) := by
    simp [divSlow, h₀, h₁, h₂, show 2 ≤ topSize b by lia]
  have hn : 2 ≤ (b.slice 0 (topSize b)).size := by simp; have := topSize_le b; lia
  have ht := top_slice_topSize_ne_zero b (show 0 < topSize b by lia)
  rw [e, divModSlow_of_two_le_topSize a b (by lia), toNat_trim, toNat_trim]
  exact (toNat_divQLimbsWith _ _ _ hn ht).trans (divModLimbsWith_spec _ _ _ hn ht).1.symm

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
