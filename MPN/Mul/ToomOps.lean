/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import MPN.AddDiff
public import MPN.Sub
public import MPN.Mul.DivExact
public import MPN.Mul.Basecase
public import MPN.Sqr.Basecase
public import MPN.Toom.Ops
public import MPN.UIntArray
public import MPN.ValAt

/-!
# The operations of the Karatsuba and Toom methods

The instance of `MPN.Toom.ToomOps` on `UInt32Array`, from the kernels of this library on its
slices, which return new arrays: each operation copies the window it writes into a new array with
`copyPadded`, applies its kernel, and copies the result back with `copySlice`. Each checks the
bounds its kernel needs; otherwise it writes the value of its specification with
`LimbArray.writeNat`, which never happens.
-/

open ScalarArray UInt32Array MPN.Toom

namespace MPN

/-! ## Fused passes -/

/--
`r - a v` in one pass, like GMP's `mpn_submul_1`, as `r.size` limbs: exact when `a v ≤ r`. The
borrow limb of `subMul1` is subtracted above `a`'s limbs.
-/
public def subMulVal (r a : UInt32Array) (v : UInt32) : UInt32Array :=
  let a' := a.toSlice 0 r.size
  let p := subMul1 r 0 a' v (by simp [a']; lia)
  if a'.size < r.size then subInto p.1 a'.size (limbArray p.2) else p.1

@[simp] public theorem size_subMulVal (r a : UInt32Array) (v : UInt32) :
    (subMulVal r a v).size = r.size := by
  simp only [subMulVal]
  split
  · rw [size_subInto _ _ _ (by rw [size_subMul1, size_limbArray]; lia), size_subMul1]
  · rw [size_subMul1]

/-- The last step of `subMulVal`: the borrow out of `m` limbs subtracted above them. -/
theorem toNat_subMulVal_aux (r : UInt32Array) (p : UInt32Array × UInt32) (m R A : Nat)
    (hp : p.1.size = r.size) (hm : m ≤ r.size) (hle : A ≤ R)
    (hsub : toNat p.1 + A = R + 2 ^ (32 * m) * p.2.toNat) :
    toNat (if m < r.size then subInto p.1 m (limbArray p.2) else p.1 : UInt32Array).toSlice =
      R - A := by
  have hP := toNat_lt p.1.toSlice
  simp only [UInt32Array.size_toSlice, Nat.min_self, Nat.sub_zero, hp] at hP
  by_cases h : m < r.size
  · rw [ite_eq_left h]
    have hpow : 2 ^ (32 * m) * toNat (limbArray p.2) ≤ toNat p.1 := by
      rw [toNat_limbArray]; lia
    rw [toNat_subInto_of_le _ _ _ (by rw [size_limbArray, hp]; lia) hpow, toNat_limbArray]
    lia
  · rw [ite_eq_right h]
    -- With no limb above, the borrow is zero.
    have hmr : 2 ^ (32 * r.size) ≤ 2 ^ (32 * m) := Nat.pow_le_pow_right (by decide) (by lia)
    have hc : p.2.toNat = 0 := by
      rcases Nat.eq_zero_or_pos p.2.toNat with h | h
      · exact h
      · have : 2 ^ (32 * m) ≤ 2 ^ (32 * m) * p.2.toNat := Nat.le_mul_of_pos_right _ h
        lia
    rw [hc, Nat.mul_zero, Nat.add_zero] at hsub
    lia

public theorem toNat_subMulVal (r a : UInt32Array) (v : UInt32)
    (hle : toNat a * v.toNat ≤ toNat r) :
    toNat (subMulVal r a v) = toNat r - toNat a * v.toNat := by
  have hR := toNat_lt r.toSlice
  simp only [UInt32Array.size_toSlice, Nat.min_self, Nat.sub_zero] at hR
  -- Cutting `a` to `r.size` limbs keeps its product.
  have ha' : toNat (a.toSlice 0 r.size) * v.toNat = toNat a * v.toNat := by
    rcases Nat.eq_zero_or_pos v.toNat with h | h
    · rw [h, Nat.mul_zero, Nat.mul_zero]
    · rw [toNat_toSlice_of_lt _ _ (by
        have : toNat a ≤ toNat a * v.toNat := Nat.le_mul_of_pos_right _ h
        lia)]
  have hsub := toNat_subMul1 r 0 (a.toSlice 0 r.size) v (by simp; lia)
  rw [ha'] at hsub
  simp only [Nat.mul_zero, Nat.pow_zero, Nat.one_mul, Nat.zero_add] at hsub
  simp only [subMulVal]
  exact toNat_subMulVal_aux r _ _ _ _ (size_subMul1 _ _ _ _ _)
    (by simp only [UInt32Array.size_toSlice]; lia) hle hsub

/--
`r + a v` in one pass, like GMP's `mpn_addmul_1`, as `r.size` limbs, for `a` shorter than `r` (and
`r` otherwise, which does not happen).
-/
public def addMulVal (r : UInt32Array) (a : UInt32Array.Slice) (v : UInt32) : UInt32Array :=
  if h : a.size < r.size then
    let p := addMul1 r 0 a v (by lia)
    addInto p.1 a.size (limbArray p.2)
  else r

@[simp] public theorem size_addMulVal (r : UInt32Array) (a : UInt32Array.Slice) (v : UInt32) :
    (addMulVal r a v).size = r.size := by
  simp only [addMulVal]
  split
  · rw [size_addInto _ _ _ (by rw [size_addMul1, size_limbArray]; lia), size_addMul1]
  · rfl

/-- The last step of `addMulVal`: the carry out of `m` limbs added above them. -/
theorem toNat_addMulVal_aux (r : UInt32Array) (p : UInt32Array × UInt32) (m S : Nat)
    (hp : p.1.size = r.size) (hm : m < r.size) (hlt : S < 2 ^ (32 * r.size))
    (hadd : toNat p.1 + 2 ^ (32 * m) * p.2.toNat = S) :
    toNat (addInto p.1 m (limbArray p.2)) = S := by
  rw [toNat_addInto_of_lt _ _ _ (by rw [size_limbArray, hp]; lia)
    (by rw [toNat_limbArray, hp]; lia), toNat_limbArray, hadd]

/-- When `a` is shorter than `r` and the sum fits in `r`, `addMulVal` adds. -/
public theorem toNat_addMulVal (r : UInt32Array) (a : UInt32Array.Slice) (v : UInt32)
    (h : a.size < r.size) (hlt : toNat r + toNat a * v.toNat < 2 ^ (32 * r.size)) :
    toNat (addMulVal r a v) = toNat r + toNat a * v.toNat := by
  have hadd := toNat_addMul1 r 0 a v (by lia)
  simp only [Nat.mul_zero, Nat.pow_zero, Nat.one_mul, Nat.zero_add] at hadd
  have e : addMulVal r a v = addInto (addMul1 r 0 a v (by lia)).1 a.size
      (limbArray (addMul1 r 0 a v (by lia)).2) := by
    simp [addMulVal, h]
  rw [e]
  exact toNat_addMulVal_aux r _ _ _ (size_addMul1 _ _ _ _ _) h hlt hadd

/-- `valAt` of windows whose limbs agree. -/
private theorem valAt_shift (a b : UInt32Array) :
    ∀ (n o p : Nat), (∀ i, i < n → a[o + i]! = b[p + i]!) → a.valAt o n = b.valAt p n
  | 0, _, _, _ => by simp
  | n + 1, o, p, h => by
    rw [valAt_succ, valAt_succ, show a[o]! = b[p]! from h 0 (by lia),
      valAt_shift a b n (o + 1) (p + 1) fun i hi => by
        rw [Nat.add_right_comm, Nat.add_right_comm p]; exact h (i + 1) (by lia)]

/-! ## Windows -/

/-- The window of `len` limbs of `a` from `o` on, as a library slice. -/
@[inline] public def winL (a : UInt32Array) (o len : Nat) : UInt32Array.Slice :=
  a.toSlice o (o + len)

private theorem winL_spec {a : UInt32Array} {o len : Nat} (h : o + len ≤ a.size) :
    (winL a o len).size = len ∧ MPN.toNat (winL a o len) = a.valAt o len := by
  have hs : (winL a o len).size = len := by rw [winL, UInt32Array.size_toSlice]; lia
  refine ⟨hs, ?_⟩
  rw [toNat_eq_valAt, hs, winL, UInt32Array.array_toSlice, UInt32Array.start_toSlice,
    show min o (min (o + len) a.size) = o by lia]

/-- The window in a new array of `n ≥ len` limbs, the limbs above zero. -/
@[inline] public def ext (a : UInt32Array) (o len n : Nat) : UInt32Array :=
  copyPadded (winL a o len) n

private theorem ext_spec {a : UInt32Array} {o len n : Nat} (h : o + len ≤ a.size) (hn : len ≤ n) :
    (ext a o len n).size = n ∧ MPN.toNat (ext a o len n) = a.valAt o len := by
  obtain ⟨s₁, s₂⟩ := winL_spec h
  exact ⟨size_copyPadded _ _ (by lia), by rw [ext, toNat_copyPadded, s₂]⟩

/-- The value of an array of `n` limbs. -/
private theorem toNat_arr {r : UInt32Array} {n : Nat} (h : r.size = n) :
    MPN.toNat r = r.valAt 0 n := by
  rw [toNat_array_eq_valAt, h]

/-- Writes the low `len` limbs of `r` into the limbs of `d` from `o` on. -/
@[inline] public def put (d : UInt32Array) (o len : Nat) (r : UInt32Array) : UInt32Array :=
  r.copySlice 0 d o len

private theorem getElem!_put {d r : UInt32Array} {o len : Nat} (h : o + len ≤ d.size)
    (hr : len ≤ r.size) (i : Nat) :
    (put d o len r)[i]! = if o ≤ i ∧ i < o + len then r[i - o]! else d[i]! := by
  unfold put
  have hsz : (r.copySlice 0 d o len).size = d.size := by
    rw [UInt32Array.size_copySlice]; lia
  by_cases hi : i < d.size
  · rw [getElem!_eq_getElem _ _ (by rw [hsz]; exact hi), UInt32Array.getElem_copySlice]
    have hmin : min o d.size = o := by lia
    have hmin2 : min len (r.size - 0) = len := by lia
    simp only [hmin, hmin2]
    split
    · rw [ite_eq_right_iff.2 (fun _ => by exfalso; lia), getElem!_eq_getElem _ _ hi]
    · split
      · rw [ite_eq_left_iff.2 (fun _ => by exfalso; lia), getElem!_eq_getElem _ _ (by lia)]
        simp
      · rw [ite_eq_right_iff.2 (fun _ => by exfalso; lia), getElem!_eq_getElem _ _ hi]
  · rw [getElem!_neg (r.copySlice 0 d o len) i (by rw [hsz]; exact hi), getElem!_neg d i hi,
      ite_eq_right_iff.2 (fun _ => by exfalso; lia)]

private theorem put_spec {d r : UInt32Array} {o len : Nat} (h : o + len ≤ d.size)
    (hr : len ≤ r.size) :
    Writes (put d o len r) d o len ∧ (put d o len r).valAt o len = r.valAt 0 len := by
  refine ⟨⟨by show (put d o len r).size = d.size; rw [put, UInt32Array.size_copySlice]; lia,
    fun i hi => ?_⟩, ?_⟩
  · show (put d o len r)[i]! = d[i]!
    rw [getElem!_put h hr]; simp only [show ¬(o ≤ i ∧ i < o + len) by lia, ↓reduceIte]
  · exact valAt_shift _ _ len o 0 fun i hi => by
      rw [getElem!_put h hr, ite_eq_left_iff.2 (fun h' => by exfalso; exact h' (by lia)),
        Nat.add_sub_cancel_left, Nat.zero_add]

/-- The window in a new array of `len` limbs, copied with one `memcpy`. -/
@[inline] public def cut (a : UInt32Array) (o len : Nat) : UInt32Array := a.extract o (o + len)

private theorem cut_spec {a : UInt32Array} {o len : Nat} (h : o + len ≤ a.size) :
    (cut a o len).size = len ∧ MPN.toNat (cut a o len) = a.valAt o len := by
  have hs : (cut a o len).size = len := by rw [cut, UInt32Array.size_extract]; lia
  refine ⟨hs, ?_⟩
  rw [toNat_toSlice, cut, UInt32Array.toList_extract, List.extract_eq_take_drop,
    show o + len - o = len by lia, ofLimbs_drop_take]

/--
Applies `K` to the window of `len` limbs of `d` from `o`: to `d` itself when the window is all of
it, and otherwise to a copy, written back.
-/
@[inline] public def onWin (d : UInt32Array) (o len : Nat) (K : UInt32Array → UInt32Array) :
    UInt32Array :=
  if o = 0 ∧ len = d.size then K d else put d o len (K (cut d o len))

/-- The fallback: the value of the specification, when it fits. -/
private theorem fallback (d : UInt32Array) (o len v : Nat) (h : o + len ≤ d.size)
    (hv : v < 2 ^ (32 * len)) :
    Writes (LimbArray.writeNat d o len v) d o len ∧
      LimbArray.valAt (LimbArray.writeNat d o len v) o len = v :=
  ⟨writes_writeNat .., by rw [LimbArray.valAt_writeNat _ _ _ _ h]; exact Nat.mod_eq_of_lt hv⟩

/-! ## The operations -/

/-- `D + S`. -/
public def addIntoT (d : UInt32Array) (o len : Nat) (s : UInt32Array) (so sl : Nat) : UInt32Array :=
  if o + len ≤ d.size ∧ so + sl ≤ s.size ∧ sl ≤ len then
    onWin d o len fun e => addInto e 0 (winL s so sl)
  else LimbArray.writeNat d o len (d.valAt o len + s.valAt so sl)

/-- `D - S`. -/
public def subIntoT (d : UInt32Array) (o len : Nat) (s : UInt32Array) (so sl : Nat) : UInt32Array :=
  if o + len ≤ d.size ∧ so + sl ≤ s.size ∧ sl ≤ len then
    onWin d o len fun e => subInto e 0 (winL s so sl)
  else LimbArray.writeNat d o len (d.valAt o len - s.valAt so sl)

/-- `D + S v`, for a source shorter than the window. -/
public def addMulIntoT (d : UInt32Array) (o len : Nat) (s : UInt32Array) (so sl v : Nat) :
    UInt32Array :=
  if o + len ≤ d.size ∧ so + sl ≤ s.size ∧ sl < len then
    onWin d o len fun e => addMulVal e (winL s so sl) v.toUInt32
  else LimbArray.writeNat d o len (d.valAt o len + s.valAt so sl * v)

/-- `D - S v`. -/
public def subMulIntoT (d : UInt32Array) (o len : Nat) (s : UInt32Array) (so sl v : Nat) :
    UInt32Array :=
  if o + len ≤ d.size ∧ so + sl ≤ s.size then
    onWin d o len fun e => subMulVal e (cut s so sl) v.toUInt32
  else LimbArray.writeNat d o len (d.valAt o len - s.valAt so sl * v)

/-- `D 2³¹`, wrapped. -/
public def shlTopT (d : UInt32Array) (o len : Nat) : UInt32Array :=
  if o + len ≤ d.size then put d o len (mulRow (winL d o len) 0x80000000)
  else LimbArray.writeNat d o len (d.valAt o len * 2 ^ 31 % 2 ^ (32 * len))

/-- `D / 2ˢ`. -/
public def shrT (d : UInt32Array) (o len s : Nat) : UInt32Array :=
  if o + len ≤ d.size ∧ s < 32 then
    onWin d o len fun e => copyPadded (shrLimbs e s.toUInt64).toSlice len
  else LimbArray.writeNat d o len (d.valAt o len / 2 ^ s)

/-- The inverse of an odd `q` modulo `2³²`, by Newton's iteration from `q`, exact to 3 bits. -/
public def inv32 (q : UInt32) : UInt32 :=
  let x := q * (2 - q * q)
  let x := x * (2 - q * x)
  let x := x * (2 - q * x)
  x * (2 - q * x)

/-- `D / q`, exactly, for an odd `q`. -/
public def divExactT (d : UInt32Array) (o len q : Nat) : UInt32Array :=
  if o + len ≤ d.size ∧ q.toUInt32 * inv32 q.toUInt32 = 1 ∧ q % 2 = 1 ∧ q.toUInt32.toNat = q then
    onWin d o len fun e => divExactOdd e q.toUInt32 (inv32 q.toUInt32)
  else LimbArray.writeNat d o len (d.valAt o len / q)

/-- `0`. -/
public def zeroIntoT (d : UInt32Array) (o len : Nat) : UInt32Array :=
  if o + len ≤ d.size then put d o len (UInt32Array.replicate len 0)
  else LimbArray.writeNat d o len 0

/-- `x + y` in a new array of `xl + 1` limbs. -/
public def sumT (x : UInt32Array) (xo xl : Nat) (y : UInt32Array) (yo yl : Nat) : UInt32Array :=
  if xo + xl ≤ x.size ∧ yo + yl ≤ y.size ∧ yl ≤ xl then addLimbs (winL x xo xl) (winL y yo yl)
  else
    LimbArray.writeNat (UInt32Array.replicate (xl + 1) 0) 0 (xl + 1)
      (x.valAt xo xl + y.valAt yo yl)

/--
The middle term of Karatsuba's method, by `addDiffInto` on a copy of the window with two more
limbs, which holds the sum.
-/
public def midT (d : UInt32Array) (o k n : Nat) (t : UInt32Array) : UInt32Array :=
  if o + n ≤ d.size ∧ t.size = k + k + 2 ∧ 3 * k ≤ n ∧ n ≤ 4 * k + 2 then
    let r := addDiffInto (ext d o n (n + 2)) k t (ext d o (k + k) (k + k))
      (ext d (o + (k + k)) (n - (k + k)) (n - (k + k)))
    if r.size = n + 2 then put d o n r
    else LimbArray.writeNat d o n (d.valAt o n)
  else
    LimbArray.writeNat d o n (d.valAt o (k + k) +
      2 ^ (32 * k) * (t.valAt 0 (k + k + 2) - d.valAt o (k + k) -
        d.valAt (o + (k + k)) (n - (k + k))) +
      2 ^ (32 * (k + k)) * d.valAt (o + (k + k)) (n - (k + k)))

/-- `x y`, with the rows over the shorter operand. -/
public def mulBaseT (d : UInt32Array) (o : Nat) (x : UInt32Array) (xo xl : Nat) (y : UInt32Array)
    (yo yl : Nat) : UInt32Array :=
  if o + (xl + yl) ≤ d.size ∧ xo + xl ≤ x.size ∧ yo + yl ≤ y.size then
    put d o (xl + yl)
      (if yl ≤ xl then mulBasecase (winL y yo yl) (winL x xo xl)
       else mulBasecase (winL x xo xl) (winL y yo yl))
  else LimbArray.writeNat d o (xl + yl) (x.valAt xo xl * y.valAt yo yl)

/-- `x²`. -/
public def sqrBaseT (d : UInt32Array) (o : Nat) (x : UInt32Array) (xo xl : Nat) : UInt32Array :=
  if o + (xl + xl) ≤ d.size ∧ xo + xl ≤ x.size then
    put d o (xl + xl)
      (if 2 ≤ xl then sqrBasecase (winL x xo xl) else mulBasecase (winL x xo xl) (winL x xo xl))
  else LimbArray.writeNat d o (xl + xl) (x.valAt xo xl * x.valAt xo xl)

/-! ## Their specifications -/

private theorem toNat_toUInt32 {v : Nat} (h : v < 2 ^ 32) : v.toUInt32.toNat = v := by
  rw [Nat.toUInt32_eq, UInt32.toNat_ofNat', Nat.mod_eq_of_lt h]

/-- The result of a kernel of `len` limbs with value `V`, written into the window. -/
private theorem put_val {d r : UInt32Array} {o len V : Nat} (h : o + len ≤ d.size)
    (hr : r.size = len) (hv : MPN.toNat r = V) :
    Writes (put d o len r) d o len ∧ (put d o len r).valAt o len = V := by
  obtain ⟨w, v⟩ := put_spec h (Nat.le_of_eq hr.symm)
  exact ⟨w, by rw [v, ← toNat_arr hr, hv]⟩

/-- `onWin` with a kernel that gives `len` limbs of value `V` from the window. -/
private theorem onWin_spec {d : UInt32Array} {o len V : Nat} (h : o + len ≤ d.size)
    (K : UInt32Array → UInt32Array)
    (hK : ∀ e : UInt32Array, e.size = len → MPN.toNat e = d.valAt o len →
      (K e).size = len ∧ MPN.toNat (K e) = V) :
    Writes (onWin d o len K) d o len ∧ (onWin d o len K).valAt o len = V := by
  rw [onWin]
  split
  · rename_i hw
    obtain ⟨rfl, rfl⟩ := hw
    obtain ⟨k₁, k₂⟩ := hK d rfl (toNat_arr rfl)
    refine ⟨⟨k₁, fun i hi => ?_⟩, by rw [← toNat_arr k₁, k₂]⟩
    show (K d)[i]! = d[i]!
    rw [getElem!_neg (K d) i (by lia), getElem!_neg d i (by lia)]
  · obtain ⟨c₁, c₂⟩ := cut_spec h
    obtain ⟨k₁, k₂⟩ := hK _ c₁ c₂
    exact put_val h k₁ k₂

public theorem addIntoT_spec (d : UInt32Array) (o len : Nat) (s : UInt32Array) (so sl : Nat)
    (h : o + len ≤ d.size) (hlt : d.valAt o len + s.valAt so sl < 2 ^ (32 * len)) :
    Writes (addIntoT d o len s so sl) d o len ∧
      (addIntoT d o len s so sl).valAt o len = d.valAt o len + s.valAt so sl := by
  rw [addIntoT]
  split
  · rename_i hg
    obtain ⟨s₁, s₂⟩ := winL_spec hg.2.1
    refine onWin_spec h _ fun e e₁ e₂ => ⟨(size_addInto e 0 _ (by rw [s₁, e₁]; lia)).trans e₁, ?_⟩
    rw [toNat_addInto_of_lt e 0 _ (by rw [s₁, e₁]; lia) (by rw [e₂, s₂, e₁]; simpa using hlt), e₂,
      s₂]
    simp
  · exact fallback _ _ _ _ h hlt

public theorem subIntoT_spec (d : UInt32Array) (o len : Nat) (s : UInt32Array) (so sl : Nat)
    (h : o + len ≤ d.size) (hle : s.valAt so sl ≤ d.valAt o len) :
    Writes (subIntoT d o len s so sl) d o len ∧
      (subIntoT d o len s so sl).valAt o len = d.valAt o len - s.valAt so sl := by
  rw [subIntoT]
  split
  · rename_i hg
    obtain ⟨s₁, s₂⟩ := winL_spec hg.2.1
    refine onWin_spec h _ fun e e₁ e₂ => ⟨(size_subInto e 0 _ (by rw [s₁, e₁]; lia)).trans e₁, ?_⟩
    rw [toNat_subInto_of_le e 0 _ (by rw [s₁, e₁]; lia) (by rw [e₂, s₂]; simpa using hle), e₂, s₂]
    simp
  · exact fallback _ _ _ _ h (Nat.lt_of_le_of_lt (Nat.sub_le ..) (valAt_lt ..))

public theorem addMulIntoT_spec (d : UInt32Array) (o len : Nat) (s : UInt32Array) (so sl v : Nat)
    (h : o + len ≤ d.size) (hv : v < 2 ^ 32)
    (hlt : d.valAt o len + s.valAt so sl * v < 2 ^ (32 * len)) :
    Writes (addMulIntoT d o len s so sl v) d o len ∧
      (addMulIntoT d o len s so sl v).valAt o len = d.valAt o len + s.valAt so sl * v := by
  rw [addMulIntoT]
  split
  · rename_i hg
    obtain ⟨s₁, s₂⟩ := winL_spec hg.2.1
    refine onWin_spec h _ fun e e₁ e₂ => ⟨(size_addMulVal ..).trans e₁, ?_⟩
    rw [toNat_addMulVal e _ _ (by rw [s₁, e₁]; lia)
      (by rw [e₂, s₂, e₁, toNat_toUInt32 hv]; exact hlt), e₂, s₂, toNat_toUInt32 hv]
  · exact fallback _ _ _ _ h hlt

public theorem subMulIntoT_spec (d : UInt32Array) (o len : Nat) (s : UInt32Array) (so sl v : Nat)
    (h : o + len ≤ d.size) (hv : v < 2 ^ 32) (hle : s.valAt so sl * v ≤ d.valAt o len) :
    Writes (subMulIntoT d o len s so sl v) d o len ∧
      (subMulIntoT d o len s so sl v).valAt o len = d.valAt o len - s.valAt so sl * v := by
  rw [subMulIntoT]
  split
  · rename_i hg
    obtain ⟨f₁, f₂⟩ := cut_spec hg.2
    refine onWin_spec h _ fun e e₁ e₂ => ⟨(size_subMulVal ..).trans e₁, ?_⟩
    rw [toNat_subMulVal e _ _ (by rw [e₂, f₂, toNat_toUInt32 hv]; exact hle), e₂, f₂,
      toNat_toUInt32 hv]
  · exact fallback _ _ _ _ h (Nat.lt_of_le_of_lt (Nat.sub_le ..) (valAt_lt ..))

public theorem shlTopT_spec (d : UInt32Array) (o len : Nat) (h : o + len ≤ d.size) :
    Writes (shlTopT d o len) d o len ∧
      (shlTopT d o len).valAt o len = d.valAt o len * 2 ^ 31 % 2 ^ (32 * len) := by
  simp only [shlTopT, h, ↓reduceIte]
  obtain ⟨s₁, s₂⟩ := winL_spec h
  have hr : (mulRow (winL d o len) 0x80000000).size = len + 1 := by rw [size_mulRow, s₁]
  obtain ⟨w, v⟩ := put_spec (r := mulRow (winL d o len) 0x80000000) h (by lia)
  refine ⟨w, ?_⟩
  rw [v, valAt_mod _ 0 (show len ≤ len + 1 by lia), ← toNat_arr hr, toNat_mulRow, s₂]
  rfl

public theorem shrT_spec (d : UInt32Array) (o len s : Nat) (h : o + len ≤ d.size) (_hs₀ : 0 < s)
    (hs : s < 32) :
    Writes (shrT d o len s) d o len ∧ (shrT d o len s).valAt o len = d.valAt o len / 2 ^ s := by
  simp only [shrT, h, hs, and_self, ↓reduceIte]
  refine onWin_spec h _ fun e e₁ e₂ => ⟨size_copyPadded _ _ (by
    have := size_shrLimbs_le e s.toUInt64; simp; lia), ?_⟩
  rw [toNat_copyPadded, toNat_shrLimbs _ _ hs, e₂]

private theorem inv_spec (q : Nat) (h : q.toUInt32 * inv32 q.toUInt32 = 1) :
    q.toUInt32.toNat * (inv32 q.toUInt32).toNat % 2 ^ 32 = 1 := by
  have := congrArg UInt32.toNat h
  rwa [UInt32.toNat_mul] at this

public theorem divExactT_spec (d : UInt32Array) (o len q : Nat) (h : o + len ≤ d.size)
    (hq : q % 2 = 1) (hd : d.valAt o len % q = 0) :
    Writes (divExactT d o len q) d o len ∧ (divExactT d o len q).valAt o len = d.valAt o len / q := by
  rw [divExactT]
  split
  · rename_i hg
    obtain ⟨-, hinv, -, hq'⟩ := hg
    refine onWin_spec h _ fun e e₁ e₂ => ⟨(size_divExactOdd ..).trans e₁, ?_⟩
    exact toNat_divExactOdd e q.toUInt32 (inv32 q.toUInt32) (inv_spec q hinv)
      (by rw [hq']; exact hq) (d.valAt o len / q)
      (by rw [e₂, hq']; exact (Nat.mul_div_cancel' (Nat.dvd_of_mod_eq_zero hd)).symm)
  · exact fallback _ _ _ _ h (Nat.lt_of_le_of_lt (Nat.div_le_self ..) (valAt_lt ..))

public theorem zeroIntoT_spec (d : UInt32Array) (o len : Nat) (h : o + len ≤ d.size) :
    Writes (zeroIntoT d o len) d o len ∧ (zeroIntoT d o len).valAt o len = 0 := by
  simp only [zeroIntoT, h, ↓reduceIte]
  exact put_val h (by simp) (toNat_zeros len)

public theorem sumT_spec (x : UInt32Array) (xo xl : Nat) (y : UInt32Array) (yo yl : Nat)
    (hyx : yl ≤ xl) :
    (sumT x xo xl y yo yl).size = xl + 1 ∧
      (sumT x xo xl y yo yl).valAt 0 (xl + 1) = x.valAt xo xl + y.valAt yo yl := by
  rw [sumT]
  split
  · rename_i hg
    obtain ⟨x₁, x₂⟩ := winL_spec hg.1
    obtain ⟨y₁, y₂⟩ := winL_spec hg.2.1
    have hs : (addLimbs (winL x xo xl) (winL y yo yl)).size = xl + 1 := by
      rw [size_addLimbs, x₁, y₁]; lia
    refine ⟨hs, ?_⟩
    rw [← toNat_arr hs, toNat_addLimbs, x₂, y₂]
  · have hR : (UInt32Array.replicate (xl + 1) 0).size = xl + 1 := by simp
    refine ⟨(LimbArray.size_writeNat (A := UInt32Array) ..).trans hR,
      (LimbArray.valAt_writeNat _ _ _ (x.valAt xo xl + y.valAt yo yl) (by
        show 0 + (xl + 1) ≤ (UInt32Array.replicate (xl + 1) 0).size; rw [hR]; lia)).trans ?_⟩
    apply Nat.mod_eq_of_lt
    show _ < 2 ^ (32 * (xl + 1))
    have := valAt_lt x xo xl
    have := valAt_lt y yo yl
    have : 2 ^ (32 * yl) ≤ 2 ^ (32 * xl) := Nat.pow_le_pow_right (by decide) (by lia)
    rw [Nat.mul_succ, Nat.pow_add]
    lia

public theorem midT_spec (d : UInt32Array) (o k n : Nat) (t : UInt32Array) (h : o + n ≤ d.size) :
    Writes (midT d o k n t) d o n ∧
      ∀ Z₁, t.valAt 0 (k + k + 2) = d.valAt o (k + k) + Z₁ + d.valAt (o + (k + k)) (n - (k + k)) →
        d.valAt o (k + k) + 2 ^ (32 * k) * Z₁ +
            2 ^ (32 * (k + k)) * d.valAt (o + (k + k)) (n - (k + k)) < 2 ^ (32 * n) →
        (midT d o k n t).valAt o n = d.valAt o (k + k) + 2 ^ (32 * k) * Z₁ +
          2 ^ (32 * (k + k)) * d.valAt (o + (k + k)) (n - (k + k)) := by
  rw [midT]
  split
  · rename_i hg
    obtain ⟨-, ht, h₃, h₄⟩ := hg
    dsimp only
    split
    · rename_i hr
      obtain ⟨w, v⟩ := put_spec (r := addDiffInto (ext d o n (n + 2)) k t (ext d o (k + k) (k + k))
        (ext d (o + (k + k)) (n - (k + k)) (n - (k + k)))) h (by lia)
      refine ⟨w, fun Z₁ hT hlt => ?_⟩
      obtain ⟨r₁, r₂⟩ := ext_spec (n := n + 2) h (by lia)
      obtain ⟨z₁, z₂⟩ := ext_spec (n := k + k) (o := o) (len := k + k) (a := d) (by lia) (Nat.le_refl _)
      obtain ⟨y₁, y₂⟩ := ext_spec (n := n - (k + k)) (o := o + (k + k)) (len := n - (k + k)) (a := d)
        (by lia) (Nat.le_refl _)
      have hR : d.valAt o n = d.valAt o (k + k) +
          2 ^ (32 * (k + k)) * d.valAt (o + (k + k)) (n - (k + k)) := by
        rw [← valAt_add, show k + k + (n - (k + k)) = n by lia]
      have hT' : MPN.toNat t = t.valAt 0 (k + k + 2) := toNat_arr ht
      obtain ⟨-, a₂⟩ := addDiffInto_spec (ext d o n (n + 2)) k t (ext d o (k + k) (k + k))
        (ext d (o + (k + k)) (n - (k + k)) (n - (k + k))) (by rw [ht, r₁]; lia)
        (by rw [z₁, ht]; lia) (by rw [y₁, ht]; lia) (by rw [z₂, y₂, hT', hT]; lia)
        (by
          rw [r₂, z₂, y₂, hT', hT, r₁, hR,
            show d.valAt o (k + k) + Z₁ + d.valAt (o + (k + k)) (n - (k + k)) -
              d.valAt o (k + k) - d.valAt (o + (k + k)) (n - (k + k)) = Z₁ by lia]
          have : 2 ^ (32 * n) ≤ 2 ^ (32 * (n + 2)) := Nat.pow_le_pow_right (by decide) (by lia)
          lia)
      rw [r₂, z₂, y₂, hT', hT,
        show d.valAt o (k + k) + Z₁ + d.valAt (o + (k + k)) (n - (k + k)) -
          d.valAt o (k + k) - d.valAt (o + (k + k)) (n - (k + k)) = Z₁ by lia, hR] at a₂
      rw [v, valAt_mod _ 0 (show n ≤ n + 2 by lia), ← toNat_arr hr, a₂,
        Nat.mod_eq_of_lt (by lia)]
      lia
    · -- The size is always `n + 2`, so this does not happen.
      refine ⟨writes_writeNat .., fun Z₁ hT hlt => ?_⟩
      exfalso
      obtain ⟨r₁, r₂⟩ := ext_spec (n := n + 2) h (by lia)
      obtain ⟨z₁, z₂⟩ := ext_spec (n := k + k) (o := o) (len := k + k) (a := d) (by lia) (Nat.le_refl _)
      obtain ⟨y₁, y₂⟩ := ext_spec (n := n - (k + k)) (o := o + (k + k)) (len := n - (k + k)) (a := d)
        (by lia) (Nat.le_refl _)
      have hR : d.valAt o n = d.valAt o (k + k) +
          2 ^ (32 * (k + k)) * d.valAt (o + (k + k)) (n - (k + k)) := by
        rw [← valAt_add, show k + k + (n - (k + k)) = n by lia]
      have hT' : MPN.toNat t = t.valAt 0 (k + k + 2) := toNat_arr ht
      obtain ⟨a₁, -⟩ := addDiffInto_spec (ext d o n (n + 2)) k t (ext d o (k + k) (k + k))
        (ext d (o + (k + k)) (n - (k + k)) (n - (k + k))) (by rw [ht, r₁]; lia)
        (by rw [z₁, ht]; lia) (by rw [y₁, ht]; lia) (by rw [z₂, y₂, hT', hT]; lia)
        (by
          rw [r₂, z₂, y₂, hT', hT, r₁, hR,
            show d.valAt o (k + k) + Z₁ + d.valAt (o + (k + k)) (n - (k + k)) -
              d.valAt o (k + k) - d.valAt (o + (k + k)) (n - (k + k)) = Z₁ by lia]
          have : 2 ^ (32 * n) ≤ 2 ^ (32 * (n + 2)) := Nat.pow_le_pow_right (by decide) (by lia)
          lia)
      rename_i hr
      exact hr (a₁.trans r₁)
  · refine ⟨writes_writeNat .., fun Z₁ hT hlt => ?_⟩
    rw [show (LimbArray.writeNat d o n _).valAt o n = _ from LimbArray.valAt_writeNat _ _ _ _ h, hT,
      show d.valAt o (k + k) + Z₁ + d.valAt (o + (k + k)) (n - (k + k)) - d.valAt o (k + k) -
        d.valAt (o + (k + k)) (n - (k + k)) = Z₁ by lia]
    exact Nat.mod_eq_of_lt hlt

private theorem lt_mul (x y : UInt32Array) (xo xl yo yl : Nat) :
    x.valAt xo xl * y.valAt yo yl < 2 ^ (32 * (xl + yl)) := by
  rw [Nat.mul_add, Nat.pow_add]
  exact Nat.mul_lt_mul_of_lt_of_lt (valAt_lt ..) (valAt_lt ..)

public theorem mulBaseT_spec (d : UInt32Array) (o : Nat) (x : UInt32Array) (xo xl : Nat)
    (y : UInt32Array) (yo yl : Nat) (h : o + (xl + yl) ≤ d.size) :
    Writes (mulBaseT d o x xo xl y yo yl) d o (xl + yl) ∧
      (mulBaseT d o x xo xl y yo yl).valAt o (xl + yl) = x.valAt xo xl * y.valAt yo yl := by
  rw [mulBaseT]
  split
  · rename_i hg
    obtain ⟨x₁, x₂⟩ := winL_spec hg.2.1
    obtain ⟨y₁, y₂⟩ := winL_spec hg.2.2
    by_cases hyx : yl ≤ xl
    · simp only [hyx, ↓reduceIte]
      exact put_val h (by rw [size_mulBasecase, x₁, y₁]; lia)
        (by rw [toNat_mulBasecase, x₂, y₂, Nat.mul_comm])
    · simp only [hyx, ↓reduceIte]
      exact put_val h (by rw [size_mulBasecase, x₁, y₁]) (by rw [toNat_mulBasecase, x₂, y₂])
  · exact fallback _ _ _ _ h (lt_mul ..)

public theorem sqrBaseT_spec (d : UInt32Array) (o : Nat) (x : UInt32Array) (xo xl : Nat)
    (h : o + (xl + xl) ≤ d.size) :
    Writes (sqrBaseT d o x xo xl) d o (xl + xl) ∧
      (sqrBaseT d o x xo xl).valAt o (xl + xl) = x.valAt xo xl * x.valAt xo xl := by
  rw [sqrBaseT]
  split
  · rename_i hg
    obtain ⟨x₁, x₂⟩ := winL_spec hg.2
    by_cases h2 : 2 ≤ xl
    · simp only [h2, ↓reduceIte]
      exact put_val h (by rw [(sqrBasecase_spec _).1, x₁]) (by rw [(sqrBasecase_spec _).2, x₂])
    · simp only [h2, ↓reduceIte]
      exact put_val h (by rw [size_mulBasecase, x₁]) (by rw [toNat_mulBasecase, x₂])
  · exact fallback _ _ _ _ h (lt_mul ..)

/-- The operations of the Karatsuba and Toom methods on arrays of 32-bit limbs. -/
public instance toomOps32 : ToomOps UInt32Array UInt32 where
  w_ge := by show 32 ≤ 32; decide
  zeros n := UInt32Array.replicate n 0
  size_zeros n := by simp [LimbArray.size]
  val_get_zeros n i := by
    show (UInt32Array.replicate n 0)[i]!.toNat = 0
    rw [UInt32Array.getElem!_eq_getElem!_toArray]
    simp only [UInt32Array.toArray_replicate]
    by_cases hi : i < n
    · simp [hi]
    · simp [hi]; rfl
  addInto := addIntoT
  addInto_spec := addIntoT_spec
  subInto := subIntoT
  subInto_spec := subIntoT_spec
  addMulInto := addMulIntoT
  addMulInto_spec := addMulIntoT_spec
  subMulInto := subMulIntoT
  subMulInto_spec := subMulIntoT_spec
  shlTop := shlTopT
  shlTop_spec := shlTopT_spec
  shr := shrT
  shr_spec := shrT_spec
  divExact := divExactT
  divExact_spec d o len q h hq _ hd := divExactT_spec d o len q h hq hd
  zeroInto := zeroIntoT
  zeroInto_spec := zeroIntoT_spec
  sum := sumT
  sum_spec := sumT_spec
  mid := midT
  mid_spec := midT_spec
  mulBase := mulBaseT
  mulBase_spec := mulBaseT_spec
  sqrBase := sqrBaseT
  sqrBase_spec := sqrBaseT_spec

end MPN
