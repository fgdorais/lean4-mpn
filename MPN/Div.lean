/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import MPN.Div.Limb
public import MPN.Div.Basecase
public import MPN.Mul
public import MPN.Sqr
public import MPN.Cmp
public import MPN.Generic.DC
public import MPN.Div.Two
public import MPN.Bits
public import MPN.Generic.Barrett

/-!
# Division

`divMod a b` is `(a / b, a % b)`, trimmed, with `Nat`'s conventions: `a / 0 = 0` and `a % 0 = a`.
The divisor is first cut to its nonzero limbs. A divisor of one limb uses `divRem1`. A longer one
is normalized, like in GMP: both numbers are multiplied by a power of two `f` that sets the top bit
of the divisor, which keeps the corrections of the quotient estimates few, and
the remainder is divided by `f` again at the end. Normalization only affects speed: the quotient
of `a f` by `b f` is `a / b` and the remainder `(a % b) f` for any `f ≠ 0`.
-/

open ScalarArray

namespace MPN

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
    rw [toNat, ofLimbs_eq_zero_iff]
    intro d hd
    obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hd
    simp at hk
    have := hz (topSize s + k) (by lia) (by lia)
    rw [UInt32Array.Slice.getD_eq] at this
    simpa [show topSize s + k < s.size by lia] using this
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
  have hc : toNat (s.slice 0 k) = ofLimbs (s.copy.toList.take k) := by
    rw [toNat, UInt32Array.Slice.copy_slice, UInt32Array.toList_extract,
      List.extract_eq_take_drop, List.drop_zero, Nat.sub_zero]
  have hs : toNat s = ofLimbs (s.copy.toList.take k) +
      2 ^ (32 * k) * ofLimbs (s.copy.toList.drop k) := by
    have h := ofLimbs_append (s.copy.toList.take k) (s.copy.toList.drop k)
    rw [List.take_append_drop] at h
    rw [toNat, h]
    by_cases hk : k ≤ s.copy.toList.length
    · rw [List.length_take_of_le hk]
    · rw [List.drop_of_length_le (by lia)]; simp
  rw [hc, hs, ← Nat.pow_mul, Nat.add_mul_mod_self_left,
    Nat.mod_eq_of_lt (ofLimbs_take_lt _ _)]

public theorem toNat_slice_hi (s : UInt32Array.Slice) (k : Nat) :
    toNat (s.slice k s.size) = toNat s / (2 ^ 32) ^ k := by
  rw [← Nat.pow_mul]
  by_cases hk : k ≤ s.size
  · exact toNat_slice_from s k hk
  · rw [toNat_of_size_eq_zero (by simp; lia), Nat.div_eq_of_lt]
    exact Nat.lt_of_lt_of_le (toNat_lt s) (Nat.pow_le_pow_right (by decide) (by lia))

public theorem toNat_shl (k : Nat) (x : UInt32Array.Slice) :
    toNat (UInt32Array.replicate k 0 ++ x.copy).toSlice = toNat x * (2 ^ 32) ^ k := by
  rw [toNat_toSlice, UInt32Array.toList_append, UInt32Array.toList_replicate, ofLimbs_append,
    ofLimbs_replicate_zero, List.length_replicate, ← Nat.pow_mul, toNat]
  lia

public theorem toNat_pow (k : Nat) :
    toNat ((UInt32Array.replicate k 0).push 1).toSlice = (2 ^ 32) ^ k := by
  rw [toNat_toSlice, UInt32Array.toList_push, UInt32Array.toList_replicate, ofLimbs_concat,
    ofLimbs_replicate_zero, List.length_replicate, ← Nat.pow_mul]
  simp

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
    let p := divRemBasecase u (v.slice 0 n) (by simp; have := topSize_le v; lia)
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
      obtain ⟨h₂, h₃⟩ := divRemBasecase_spec u (v.slice 0 (topSize v))
        (by simp; lia) (top_slice_topSize_ne_zero v (by lia))
      rw [hb] at h₂ h₃
      exact div_mod_eq hV h₂ h₃
    · rename_i h₁ h
      have h₀ : topSize v = 0 := by lia
      have : toNat v = 0 := by rw [← hb, toNat_of_size_eq_zero (by simp [h₀])]
      lia

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
  pow k := ((UInt32Array.replicate k 0).push 1).toSlice
  val_pow k := toNat_pow k
  one := ((UInt32Array.replicate 0 0).push 1).toSlice
  val_one := by rw [toNat_pow, Nat.pow_zero]
  -- No wrapped product on 32-bit limbs yet: the product itself, which does not wrap.
  mulModSize n := n
  le_mulModSize _ := Nat.le_refl _
  mulMod _ x y :=
    let r := (mulLimbs x y).toSlice
    r.slice 0 (topSize r)
  val_mulMod _ x y := by
    show toNat ((mulLimbs x y).toSlice.slice 0 (topSize _)) % _ = _
    rw [toNat_slice_topSize, isMul_mulLimbs.toNat_eq x y]
  divRem := div
  val_divRem := hdiv

/-- The instance with the schoolbook division, for the divide-and-conquer division over it. -/
@[expose] public def ops32B : NatOps UInt32Array.Slice := ops32With divBase32 val_divBase32

@[simp] public theorem ops32B_val (x : UInt32Array.Slice) : ops32B.val x = toNat x := rfl

@[simp] public theorem ops32B_B : ops32B.B = 2 ^ 32 := rfl

/--
`(r / v, r % v)` by `main`'s divide-and-conquer division on `ops32B`, with `divBase32` below `T`
limbs, as arrays.
-/
public def dcGen (T : Nat) (r : UInt32Array) (v : UInt32Array.Slice) : UInt32Array × UInt32Array :=
  let p := ops32B.divNorm divBase32 T r.toSlice v v.size (r.size + 1 - v.size)
  (p.1.copy, p.2.copy)

private theorem dcGen_spec (T : Nat) (r : UInt32Array) (v : UInt32Array.Slice) (hn : 2 ≤ v.size)
    (hvt : v[v.size - 1]'(by lia) ≠ 0) :
    toNat (dcGen T r v).1 * toNat v + toNat (dcGen T r v).2 = toNat r ∧
      toNat (dcGen T r v).2 < toNat v := by
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
  have hV : 0 < toNat v := Nat.lt_of_lt_of_le (Nat.two_pow_pos _) htop
  have hr : toNat r.toSlice < 2 ^ (32 * r.size) := by
    have := toNat_lt r.toSlice; simpa using this
  have hrv : toNat r.toSlice < toNat v * (2 ^ 32) ^ (r.size + 1 - v.size) := by
    rw [← Nat.pow_mul]
    calc toNat r.toSlice < 2 ^ (32 * r.size) := hr
      _ ≤ 2 ^ (32 * (v.size - 1)) * 2 ^ (32 * (r.size + 1 - v.size)) := by
          rw [← Nat.pow_add]; exact Nat.pow_le_pow_right (by decide) (by lia)
      _ ≤ toNat v * 2 ^ (32 * (r.size + 1 - v.size)) := Nat.mul_le_mul_right _ htop
  obtain ⟨h₁, h₂⟩ := ops32B.divNorm_spec divBase32 (fun U V h => val_divBase32 U V (by
      simp only [ops32B_val] at h; lia)) T v.size (r.size + 1 - v.size) r.toSlice v
    (by simp only [ops32B_val]; exact hV)
    (by simp only [ops32B_val, ops32B_B]; rw [← Nat.pow_mul]; exact toNat_lt v)
    (by simp only [ops32B_val, ops32B_B]; exact hrv)
  simp only [ops32B_val] at h₁ h₂
  simp only [dcGen, toNat_copy]
  rw [h₁, h₂, toNat_toSlice]
  rw [toNat_toSlice] at hr
  refine ⟨?_, Nat.mod_lt _ hV⟩
  have := Nat.div_add_mod (ofLimbs r.toList) (toNat v)
  rw [Nat.mul_comm] at this
  exact this

/-! ## Normalized division -/

/-- The shift that brings the top bit of `vt ≠ 0` to the top of the limb. -/
@[expose] public def normShift (vt : UInt32) : Nat := (31 - vt.log2).toNat % 32

/-- `2 ^ normShift vt`, the factor of the normalization. -/
@[expose] public def normFactor (vt : UInt32) : UInt32 := (1 : UInt32) <<< (normShift vt).toUInt32

public theorem toNat_normFactor (vt : UInt32) : (normFactor vt).toNat = 2 ^ normShift vt :=
  toNat_pow_limb _ (Nat.mod_lt _ (by decide))

public theorem normFactor_ne_zero (vt : UInt32) : normFactor vt ≠ 0 := by
  intro h
  have := toNat_normFactor vt
  rw [h, UInt32.toNat_zero] at this
  exact absurd this.symm (Nat.ne_of_gt (Nat.two_pow_pos _))

/--
The division of the normalized dividend, an array of its own: below `T` limbs in the divisor,
`divRemBasecaseTop` divides it in place without a copy or an extra top limb, and from `T` on
`main`'s divide-and-conquer division (`dcGen`).
-/
public def divRemNormWith (T : Nat) (r : UInt32Array) (v : UInt32Array.Slice) (hn : 2 ≤ v.size) :
    UInt32Array × UInt32Array :=
  if v.size < T then divRemBasecaseTop r v hn else dcGen T r v

public theorem divRemNormWith_spec (T : Nat) (r : UInt32Array) (v : UInt32Array.Slice)
    (hn : 2 ≤ v.size) (hvt : v[v.size - 1]'(by lia) ≠ 0) :
    toNat (divRemNormWith T r v hn).1 * toNat v + toNat (divRemNormWith T r v hn).2 = toNat r ∧
      toNat (divRemNormWith T r v hn).2 < toNat v := by
  by_cases h : v.size < T
  · have e : divRemNormWith T r v hn = divRemBasecaseTop r v hn := by
      unfold divRemNormWith
      rw [ite_eq_left h]
    rw [e]
    exact divRemBasecaseTop_spec r v hn hvt
  · have e : divRemNormWith T r v hn = dcGen T r v := by
      unfold divRemNormWith
      rw [ite_eq_right h]
    rw [e]
    exact dcGen_spec T r v hn hvt

/-- `divRemNormWith` from `config.divDC` limbs. -/
def divRemNorm (r : UInt32Array) (v : UInt32Array.Slice) (hn : 2 ≤ v.size) :
    UInt32Array × UInt32Array :=
  divRemNormWith config.divDC r v hn

private theorem divRemNorm_spec (r : UInt32Array) (v : UInt32Array.Slice) (hn : 2 ≤ v.size)
    (hvt : v[v.size - 1]'(by lia) ≠ 0) :
    toNat (divRemNorm r v hn).1 * toNat v + toNat (divRemNorm r v hn).2 = toNat r ∧
      toNat (divRemNorm r v hn).2 < toNat v :=
  divRemNormWith_spec config.divDC r v hn hvt

/--
`u / v` and `u % v` for a divisor of at least two limbs with a nonzero top limb, untrimmed:
`u` and `v` are normalized, divided with `divRemNorm`, and the remainder shifted back.
-/
def divModLimbs (u v : UInt32Array.Slice) (hn : 2 ≤ v.size) : UInt32Array × UInt32Array :=
  let vt := v[v.size - 1]'(by lia)
  let f := normFactor vt
  let vf := mulRow v f
  let v' := vf.toSlice.slice 0 (topSize vf)
  if h : 2 ≤ v'.size then
    let p := divRemNorm (mulRow u f) v' h
    (p.1, shiftRight p.2 (normShift vt))
  else
    divRemBasecase u v hn

/-- The quotient of `divModLimbs`, without shifting the remainder back. -/
def divLimbsQ (u v : UInt32Array.Slice) (hn : 2 ≤ v.size) : UInt32Array :=
  let vt := v[v.size - 1]'(by lia)
  let f := normFactor vt
  let vf := mulRow v f
  let v' := vf.toSlice.slice 0 (topSize vf)
  if h : 2 ≤ v'.size then
    (divRemNorm (mulRow u f) v' h).1
  else
    (divRemBasecase u v hn).1

private theorem divLimbsQ_eq (u v : UInt32Array.Slice) (hn : 2 ≤ v.size) :
    divLimbsQ u v hn = (divModLimbs u v hn).1 := by
  unfold divLimbsQ divModLimbs
  simp only
  split <;> rfl

private theorem divModLimbs_spec (u v : UInt32Array.Slice) (hn : 2 ≤ v.size)
    (hvt : v[v.size - 1]'(by lia) ≠ 0) :
    toNat (divModLimbs u v hn).1 = toNat u / toNat v ∧
      toNat (divModLimbs u v hn).2 = toNat u % toNat v := by
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
  rw [toNat_toSlice, toNat_toSlice]
  simp only [divModLimbs]
  split
  · rename_i h
    -- Normalized: `u f = q (v f) + r'` with `r' < v f`, and `r' = r f + rem` with `rem < f`.
    have hF : 0 < (normFactor (v[v.size - 1]'(by lia))).toNat := by
      rw [toNat_normFactor]; exact Nat.two_pow_pos _
    simp only
    rw [← toNat_toSlice (shiftRight _ _), toNat_shiftRight, ← toNat_normFactor]
    generalize normFactor (v[v.size - 1]'(by lia)) = f at *
    have hv' : toNat ((mulRow v f).toSlice.slice 0 (topSize (mulRow v f))) = toNat v * f.toNat := by
      rw [toNat_slice_topSize, toNat_mulRow]
    have hpos : 0 < topSize (mulRow v f) := by
      simp only [UInt32Array.Slice.size_slice] at h
      lia
    obtain ⟨h₁, h₂⟩ := divRemNorm_spec (mulRow u f) _ h (top_slice_topSize_ne_zero _ hpos)
    rw [hv', toNat_mulRow] at h₁
    rw [hv'] at h₂
    simp only [toNat_toSlice] at h₁ h₂ ⊢
    obtain ⟨hq, hr⟩ := div_mod_eq (Nat.mul_pos hVpos hF) h₁ h₂
    rw [Nat.mul_div_mul_right _ _ hF] at hq
    rw [Nat.mul_mod_mul_right] at hr
    -- The remainder is `(u % v) f`, and the shift divides it by `f`.
    refine ⟨hq, ?_⟩
    rw [hr, Nat.mul_div_cancel _ hF]
  · -- The fallback, without normalization.
    obtain ⟨h₁, h₂⟩ := divRemBasecase_spec u v hn hvt
    simp only [toNat_toSlice] at h₁ h₂
    obtain ⟨hq, hr⟩ := div_mod_eq hVpos h₁ h₂
    exact ⟨hq, hr⟩

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

private theorem divSlow_eq_divModSlow (a b : UInt32Array.Slice) :
    divSlow a b = (divModSlow a b).1 := by
  unfold divSlow divModSlow
  simp only [div2_eq]
  by_cases h₀ : topSize b = 0
  · simp [h₀]
  · by_cases h₁ : topSize b = 1
    · simp [h₁]
    · by_cases h₂ : topSize b = 2
      · simp [h₂]
      · simp only [h₀, h₁, h₂, ↓reduceIte, ↓reduceDIte, show 2 ≤ topSize b by lia,
          divLimbsQ_eq]

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
      exact (isTrimmed_iff _).2 (by simp)
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

/-! ## Division by a reciprocal -/

/--
`u / v` and `u % v` by Barrett's division with Newton's reciprocal (`NatOps.divMu`), for a
divisor whose top limb is not zero: normalized as in `divModLimbs`, so that the reciprocal is
accurate, and the remainder shifted back.
-/
def divModMuLimbs (u v : UInt32Array.Slice) (hn : 1 ≤ v.size) : UInt32Array × UInt32Array :=
  let vt := v[v.size - 1]'(by lia)
  let f := normFactor vt
  let vf := mulRow v f
  let p := ops32.divMu (mulRow u f).toSlice (vf.toSlice.slice 0 (topSize vf))
  (p.1.copy, shiftRight p.2 (normShift vt))

private theorem divModMuLimbs_spec (u v : UInt32Array.Slice) (hn : 1 ≤ v.size)
    (hvt : v[v.size - 1]'(by lia) ≠ 0) :
    toNat (divModMuLimbs u v hn).1 = toNat u / toNat v ∧
      toNat (divModMuLimbs u v hn).2 = toNat u % toNat v := by
  have hvt' : 0 < (v[v.size - 1]'(by lia)).toNat := by
    rcases Nat.eq_zero_or_pos (v[v.size - 1]'(by lia)).toNat with h | h
    · exact absurd (UInt32.toNat_inj.1 (by simpa using h)) hvt
    · exact h
  have hVpos : 0 < toNat v := by
    have htop : (v[v.size - 1]'(by lia)).toNat ≤ toNat v := by
      have h := toNat_slice_add_toNat_slice v (v.size - 1) (by lia)
      have : toNat (v.slice (v.size - 1) v.size) = (v[v.size - 1]'(by lia)).toNat := by
        rw [toNat_of_size_eq_one (by simp; lia)]
        simp
      have := Nat.mul_le_mul_right (toNat (v.slice (v.size - 1) v.size))
        (Nat.one_le_two_pow (n := 32 * (v.size - 1)))
      lia
    lia
  have hF : 0 < (normFactor (v[v.size - 1]'(by lia))).toNat := by
    rw [toNat_normFactor]; exact Nat.two_pow_pos _
  simp only [divModMuLimbs, toNat_copy, toNat_shiftRight]
  rw [← toNat_normFactor]
  generalize normFactor (v[v.size - 1]'(by lia)) = f at *
  have hv' : toNat ((mulRow v f).toSlice.slice 0 (topSize (mulRow v f))) = toNat v * f.toNat := by
    rw [toNat_slice_topSize, toNat_mulRow]
  obtain ⟨hq, hr⟩ := ops32.divMu_spec (mulRow u f).toSlice
    ((mulRow v f).toSlice.slice 0 (topSize (mulRow v f)))
    (by show 0 < toNat _; rw [hv']; exact Nat.mul_pos hVpos hF)
  have hq' : toNat (ops32.divMu (mulRow u f).toSlice
      ((mulRow v f).toSlice.slice 0 (topSize (mulRow v f)))).1 =
        toNat u * f.toNat / (toNat v * f.toNat) := by
    rw [← hv', ← toNat_mulRow]; exact hq
  have hr' : toNat (ops32.divMu (mulRow u f).toSlice
      ((mulRow v f).toSlice.slice 0 (topSize (mulRow v f)))).2 =
        toNat u * f.toNat % (toNat v * f.toNat) := by
    rw [← hv', ← toNat_mulRow]; exact hr
  rw [hq', hr', Nat.mul_div_mul_right _ _ hF, Nat.mul_mod_mul_right, Nat.mul_div_cancel _ hF]
  exact ⟨rfl, rfl⟩

/-- `(a / b, a % b)`, trimmed, by Barrett's division with Newton's reciprocal from three limbs. -/
public def divModMu (a b : UInt32Array.Slice) : UInt32Array × UInt32Array :=
  let n := topSize b
  if h : 3 ≤ n then
    let p := divModMuLimbs a (b.slice 0 n) (by simp; have := topSize_le b; lia)
    (trim p.1, trim p.2)
  else divModSlow a b

private theorem divModMu_of_le (a b : UInt32Array.Slice) (h : 3 ≤ topSize b) :
    divModMu a b =
      (trim (divModMuLimbs a (b.slice 0 (topSize b)) (by simp; have := topSize_le b; lia)).1,
        trim (divModMuLimbs a (b.slice 0 (topSize b)) (by simp; have := topSize_le b; lia)).2) := by
  unfold divModMu
  rw [dite_eq_left h]

private theorem divModMu_of_lt (a b : UInt32Array.Slice) (h : ¬3 ≤ topSize b) :
    divModMu a b = divModSlow a b := by
  unfold divModMu
  rw [dite_eq_right h]

public theorem toNat_divModMu (a b : UInt32Array.Slice) :
    toNat (divModMu a b).1 = toNat a / toNat b ∧ toNat (divModMu a b).2 = toNat a % toNat b := by
  by_cases h : 3 ≤ topSize b
  · have hs := divModMuLimbs_spec a (b.slice 0 (topSize b))
      (by simp; have := topSize_le b; lia) (top_slice_topSize_ne_zero b (by lia))
    rw [toNat_slice_topSize] at hs
    rw [divModMu_of_le a b h, toNat_trim, toNat_trim]
    exact hs
  · rw [divModMu_of_lt a b h]
    exact toNat_divModSlow a b

private theorem isTrimmed_divModMu (a b : UInt32Array.Slice) :
    isTrimmed (divModMu a b).1 = true ∧ isTrimmed (divModMu a b).2 = true := by
  by_cases h : 3 ≤ topSize b
  · rw [divModMu_of_le a b h]
    exact ⟨isTrimmed_trim _, isTrimmed_trim _⟩
  · rw [divModMu_of_lt a b h]
    exact ⟨isTrimmed_divModSlow_fst a b, isTrimmed_divModSlow_snd a b⟩

/-! ## Division -/

/--
`(a / b, a % b)`, trimmed: by Barrett's division with Newton's reciprocal from `config.divMu`
limbs of divisor, and by Algorithm D or by blocks below (`divModSlow`).
-/
public def divMod (a b : UInt32Array.Slice) : UInt32Array × UInt32Array :=
  if config.divMu ≤ topSize b then divModMu a b else divModSlow a b

/-- Divides two numbers, with `a / 0 = 0`: `divMod` without the remainder. -/
public def div (a b : UInt32Array.Slice) : UInt32Array :=
  if config.divMu ≤ topSize b then (divModMu a b).1 else divSlow a b

/-- The remainder of dividing two numbers, with `a % 0 = a`. -/
public def mod (a b : UInt32Array.Slice) : UInt32Array := (divMod a b).2

private theorem divMod_of_le (a b : UInt32Array.Slice) (h : config.divMu ≤ topSize b) :
    divMod a b = divModMu a b := by
  unfold divMod; rw [ite_eq_left h]

private theorem divMod_of_lt (a b : UInt32Array.Slice) (h : ¬config.divMu ≤ topSize b) :
    divMod a b = divModSlow a b := by
  unfold divMod; rw [ite_eq_right h]

/-- `divMod` divides, with `Nat`'s conventions for a zero divisor. -/
public theorem toNat_divMod (a b : UInt32Array.Slice) :
    toNat (divMod a b).1 = toNat a / toNat b ∧ toNat (divMod a b).2 = toNat a % toNat b := by
  by_cases h : config.divMu ≤ topSize b
  · rw [divMod_of_le a b h]; exact toNat_divModMu a b
  · rw [divMod_of_lt a b h]; exact toNat_divModSlow a b

private theorem div_eq_divMod (a b : UInt32Array.Slice) : div a b = (divMod a b).1 := by
  by_cases h : config.divMu ≤ topSize b
  · rw [divMod_of_le a b h]; unfold div; rw [ite_eq_left h]
  · rw [divMod_of_lt a b h]; unfold div; rw [ite_eq_right h]; exact divSlow_eq_divModSlow a b

/-- Division is `Nat` division. -/
@[simp] public theorem toNat_div (a b : UInt32Array.Slice) :
    toNat (div a b) = toNat a / toNat b := by
  rw [div_eq_divMod]
  exact (toNat_divMod a b).1

/-- The remainder is `Nat`'s remainder. -/
@[simp] public theorem toNat_mod (a b : UInt32Array.Slice) : toNat (mod a b) = toNat a % toNat b :=
  (toNat_divMod a b).2

public theorem isTrimmed_div (a b : UInt32Array.Slice) : isTrimmed (div a b) = true := by
  rw [div_eq_divMod]
  by_cases h : config.divMu ≤ topSize b
  · rw [divMod_of_le a b h]; exact (isTrimmed_divModMu a b).1
  · rw [divMod_of_lt a b h]; exact isTrimmed_divModSlow_fst a b

public theorem isTrimmed_mod (a b : UInt32Array.Slice) : isTrimmed (mod a b) = true := by
  rw [mod]
  by_cases h : config.divMu ≤ topSize b
  · rw [divMod_of_le a b h]; exact (isTrimmed_divModMu a b).2
  · rw [divMod_of_lt a b h]; exact isTrimmed_divModSlow_snd a b

end MPN
