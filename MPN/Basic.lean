/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ScalarArray.UInt32
public import MPN.Limbs
public import MPN.FoldInPlace

/-!
# Natural numbers as limbs

A natural number is stored as little-endian base 2³² limbs in a `UInt32Array`. The arithmetic
works on slices of limbs, so it accepts trailing zero limbs, and its results are trimmed so that
the most significant limb is nonzero.

The specification is `toNat`, defined through `ofLimbs` on the list of limbs. Trimmed arrays
represent each natural number exactly once, and `ofNat` and `toNat` are inverse bijections
between them and `Nat`.
-/

open ScalarArray

namespace MPN

/-- Removes the trailing zero limbs. -/
public def trim (a : UInt32Array) : UInt32Array := a.popWhile (· == 0)

/-- Whether the most significant limb is nonzero. -/
public def isTrimmed (a : UInt32Array) : Bool :=
  if h : 0 < a.size then a[a.size - 1] != 0 else true

/-- The limbs of a natural number. -/
public def ofNat (n : Nat) : UInt32Array := loop n (.emptyWithCapacity (n.log2 / 32 + 1))
where
  loop (n : Nat) (acc : UInt32Array) : UInt32Array :=
    if h : n = 0 then acc else loop (n / 2 ^ 32) (acc.push n.toUInt32)
  termination_by n
  decreasing_by exact Nat.div_lt_self (Nat.pos_of_ne_zero h) (by decide)

/-- The natural number that a slice of limbs denotes. -/
@[expose] public def toNat (s : UInt32Array.Slice) : Nat := ofLimbs s.copy.toList

/-! ## Specification -/

@[simp] public theorem toNat_toSlice (a : UInt32Array) : toNat a.toSlice = ofLimbs a.toList := by
  simp [toNat]

public theorem toNat_of_size_eq_zero {s : UInt32Array.Slice} (h : s.size = 0) : toNat s = 0 := by
  have : s.copy.toList = [] := List.eq_nil_of_length_eq_zero (by simp [h])
  simp [toNat, this]

public theorem toNat_of_size_eq_one {s : UInt32Array.Slice} (h : s.size = 1) :
    toNat s = (s[0]'(by lia)).toNat := by
  obtain ⟨x, hx⟩ := List.length_eq_one_iff.1 (by simp [h] : s.copy.toList.length = 1)
  have : s[0]'(by lia) = x := by
    have := congrArg (·[0]?) hx
    simp only [UInt32Array.getElem?_toList, List.getElem?_cons_zero] at this
    rw [getElem?_pos s.copy 0 (by simp [h]), Option.some.injEq] at this
    simpa using this
  simp [toNat, hx, this]

/-- Reading a limb past the end of a slice gives `0`, as past the end of its list. -/
public theorem getD_eq_getD_toList_copy (s : UInt32Array.Slice) (j : Nat) :
    s.getD j 0 = s.copy.toList.getD j 0 := by
  rw [UInt32Array.Slice.getD_eq]
  by_cases h : j < s.size
  · simp [h, List.getD_eq_getElem?_getD]
  · simp [h, List.getD_eq_getElem?_getD]

/-- Splitting a slice at `k` splits its value. -/
public theorem toNat_slice_add_toNat_slice (s : UInt32Array.Slice) (k : Nat) (hk : k ≤ s.size) :
    toNat (s.slice 0 k) + 2 ^ (32 * k) * toNat (s.slice k s.size) = toNat s := by
  have h := ofLimbs_append (s.copy.toList.take k) (s.copy.toList.drop k)
  rw [List.take_append_drop, List.length_take_of_le (by simpa using hk)] at h
  simp only [toNat, UInt32Array.Slice.copy_slice, UInt32Array.toList_extract, h]
  simp [List.extract_eq_take_drop, List.take_of_length_le]

/-- Splitting the part of a slice from `i` at `i + k`. -/
private theorem toNat_slice_split_of_le (s : UInt32Array.Slice) (i k : Nat) (h : i + k ≤ s.size) :
    toNat (s.slice i s.size) =
      toNat (s.slice i (i + k)) + 2 ^ (32 * k) * toNat (s.slice (i + k) s.size) := by
  have h₁ := toNat_slice_add_toNat_slice (s.slice i s.size) k (by simp; lia)
  have e₁ : toNat ((s.slice i s.size).slice 0 k) = toNat (s.slice i (i + k)) := by
    simp only [toNat, UInt32Array.Slice.copy_slice, UInt32Array.extract_extract]
    rw [show i + 0 = i by lia, show min (i + k) s.size = i + k by lia]
  have e₂ : toNat ((s.slice i s.size).slice k (s.slice i s.size).size) =
      toNat (s.slice (i + k) s.size) := by
    simp only [toNat, UInt32Array.Slice.copy_slice, UInt32Array.extract_extract,
      UInt32Array.Slice.size_slice]
    rw [show min (i + (min s.size s.size - i)) s.size = s.size by lia]
  rw [e₁, e₂] at h₁
  exact h₁.symm

/-- Splitting the limbs of `s` from `i` at `i + m`, also when `i + m` is past the end. -/
public theorem toNat_slice_split (s : UInt32Array.Slice) (i m : Nat) :
    toNat (s.slice i s.size) =
      toNat (s.slice i (i + m)) + 2 ^ (32 * m) * toNat (s.slice (i + m) s.size) := by
  by_cases h : i + m ≤ s.size
  · exact toNat_slice_split_of_le s i m h
  · have h₀ : toNat (s.slice (i + m) s.size) = 0 :=
      toNat_of_size_eq_zero (by simp only [UInt32Array.Slice.size_slice]; lia)
    have e : toNat (s.slice i (i + m)) = toNat (s.slice i s.size) := by
      simp only [toNat, UInt32Array.Slice.copy_slice, UInt32Array.toList_extract,
        List.extract_eq_take_drop]
      rw [List.take_of_length_le (l := List.drop i s.copy.toList) (by simp; lia),
        List.take_of_length_le (l := List.drop i s.copy.toList) (by simp)]
    rw [h₀, e, Nat.mul_zero, Nat.add_zero]

/-- The value of an array is its low `m` limbs plus `2^(32 m)` times the rest. -/
public theorem toNat_split (x : UInt32Array) (m : Nat) (hm : m ≤ x.size) :
    toNat x = toNat (x.toSlice 0 m) + 2 ^ (32 * m) * toNat (x.toSlice m x.size) := by
  have h := toNat_slice_add_toNat_slice x.toSlice m (by simp; lia)
  have e₁ : toNat (x.toSlice.slice 0 m) = toNat (x.toSlice 0 m) := by
    simp [toNat, UInt32Array.Slice.copy_slice]
  have e₂ : toNat (x.toSlice.slice m x.toSlice.size) = toNat (x.toSlice m x.size) := by
    simp [toNat, UInt32Array.Slice.copy_slice]
  rw [e₁, e₂] at h
  exact h.symm

/-- Cutting an array to its first `n` limbs keeps a value below `2^(32 n)`. -/
public theorem toNat_toSlice_of_lt (a : UInt32Array) (n : Nat) (h : toNat a < 2 ^ (32 * n)) :
    toNat (a.toSlice 0 n) = toNat a := by
  rw [toNat_toSlice] at h
  simp only [toNat, UInt32Array.copy_toSlice, UInt32Array.toList_extract, List.extract_eq_take_drop,
    List.drop_zero, Nat.sub_zero, ofLimbs_take_of_lt h]
  rw [List.take_of_length_le (by simp)]

public theorem toNat_lt (s : UInt32Array.Slice) : toNat s < 2 ^ (32 * s.size) := by
  have := ofLimbs_lt s.copy.toList
  rwa [UInt32Array.length_toList, UInt32Array.Slice.size_copy] at this

/-- An array whose limbs from `m` on are zero is below `2^(32 m)`. -/
public theorem toNat_lt_of_zero_from (a : UInt32Array) (m : Nat)
    (h : ∀ k (hk : k < a.size), m ≤ k → a[k] = 0) : toNat a < 2 ^ (32 * m) := by
  rw [toNat_toSlice]
  have hsplit := ofLimbs_append (a.toList.take m) (a.toList.drop m)
  rw [List.take_append_drop] at hsplit
  have hz : ofLimbs (a.toList.drop m) = 0 := by
    refine ofLimbs_eq_zero_iff.2 fun d hd => ?_
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hd
    simp only [List.getElem_drop, UInt32Array.getElem_toList]
    exact h _ _ (by lia)
  rw [hsplit, hz, Nat.mul_zero, Nat.add_zero]
  exact ofLimbs_take_lt _ _

public theorem isTrimmed_iff (a : UInt32Array) : isTrimmed a = true ↔ IsTrimmed a.toList := by
  rw [isTrimmed, IsTrimmed, List.getLast?_eq_getElem?, UInt32Array.getElem?_toList,
    UInt32Array.length_toList]
  by_cases h : 0 < a.size
  · simp [h, getElem?_pos a (a.size - 1) (by lia)]
  · simp [h, getElem?_neg a (a.size - 1) (by lia)]

public theorem toList_trim (a : UInt32Array) : (trim a).toList = trimLimbs a.toList := by
  simp [trim, trimLimbs]

@[simp] public theorem toNat_trim (a : UInt32Array) : toNat (trim a) = toNat a := by
  simp [toList_trim]

public theorem isTrimmed_trim (a : UInt32Array) : isTrimmed (trim a) = true := by
  simp [isTrimmed_iff, toList_trim, isTrimmed_trimLimbs]

/--
`trim` as a loop that pops zero limbs, which the compiler uses in its place: `popWhile` takes its
predicate as a closure, called through `lean_apply_1` for each limb it checks.
-/
public def trimFast (a : UInt32Array) : UInt32Array :=
  if h : 0 < a.size then
    if a[a.size - 1] = 0 then trimFast a.pop else a
  else
    a
termination_by a.size
decreasing_by simp only [UInt32Array.size_pop]; lia

private theorem trimLimbs_of_getLast (l : List UInt32) (hne : l ≠ []) :
    trimLimbs l = if l.getLast hne = 0 then trimLimbs l.dropLast else l := by
  conv => lhs; rw [← List.dropLast_concat_getLast hne]
  split
  · rename_i h
    rw [h]
    simp [trimLimbs]
  · rename_i h
    conv => rhs; rw [← List.dropLast_concat_getLast hne]
    simp [trimLimbs, h]

@[csimp] public theorem trim_eq_trimFast : @trim = @trimFast := by
  funext a
  induction a using trimFast.induct with
  | case1 a h hz ih =>
    rw [trimFast, dite_eq_left h, ite_eq_left hz, ← ih, ← UInt32Array.toList_inj, toList_trim,
      toList_trim, UInt32Array.toList_pop]
    have hne : a.toList ≠ [] := by
      intro h'; have := congrArg List.length h'; simp at this; lia
    rw [trimLimbs_of_getLast _ hne, ite_eq_left (by simpa [List.getLast_eq_getElem] using hz)]
  | case2 a h hz =>
    rw [trimFast, dite_eq_left h, ite_eq_right hz, ← UInt32Array.toList_inj, toList_trim]
    have hne : a.toList ≠ [] := by
      intro h'; have := congrArg List.length h'; simp at this; lia
    rw [trimLimbs_of_getLast _ hne, ite_eq_right (by simpa [List.getLast_eq_getElem] using hz)]
  | case3 a h =>
    rw [trimFast, dite_eq_right h, ← UInt32Array.toList_inj, toList_trim]
    have : a.toList = [] := List.eq_nil_of_length_eq_zero (by simp; lia)
    rw [this]
    rfl

private theorem ofLimbs_ofNat_loop (n : Nat) (acc : UInt32Array) :
    ofLimbs (ofNat.loop n acc).toList = ofLimbs acc.toList + 2 ^ (32 * acc.size) * n := by
  induction n, acc using ofNat.loop.induct with
  | case1 acc => simp [ofNat.loop]
  | case2 n acc h ih =>
    rw [ofNat.loop]
    simp only [h, ↓reduceDIte]
    rw [ih, UInt32Array.toList_push, ofLimbs_concat, UInt32Array.length_toList,
      UInt32Array.size_push, Nat.toUInt32_eq,
      UInt32.toNat_ofNat']
    have := Nat.mod_add_div n (2 ^ 32)
    rw [Nat.mul_add, Nat.mul_one, Nat.pow_add]
    grind

private theorem isTrimmed_ofNat_loop (n : Nat) (acc : UInt32Array) (hn : n ≠ 0) :
    IsTrimmed (ofNat.loop n acc).toList := by
  induction n, acc using ofNat.loop.induct with
  | case1 => contradiction
  | case2 n acc h ih =>
    rw [ofNat.loop]
    simp only [h, ↓reduceDIte]
    by_cases hq : n / 2 ^ 32 = 0
    · rw [ofNat.loop]
      simp only [hq, ↓reduceDIte, UInt32Array.toList_push, IsTrimmed, List.getLast?_concat, ne_eq,
        Option.some.injEq]
      rw [← UInt32.toNat_inj, Nat.toUInt32_eq, UInt32.toNat_ofNat']
      simp only [UInt32.toNat_zero]
      lia
    · exact ih hq

@[simp] public theorem toNat_ofNat (n : Nat) : toNat (ofNat n) = n := by
  simp [ofNat, ofLimbs_ofNat_loop]

public theorem isTrimmed_ofNat (n : Nat) : isTrimmed (ofNat n) = true := by
  rw [isTrimmed_iff, ofNat]
  by_cases hn : n = 0
  · simp [hn, ofNat.loop]
  · exact isTrimmed_ofNat_loop n _ hn

/-- A trimmed array is the limbs of the number it denotes. -/
public theorem ofNat_toNat {a : UInt32Array} (h : isTrimmed a = true) : ofNat (toNat a) = a := by
  apply UInt32Array.toList_inj.1
  apply IsTrimmed.ofLimbs_inj ((isTrimmed_iff _).1 (isTrimmed_ofNat _)) ((isTrimmed_iff _).1 h)
  rw [← toNat_toSlice, ← toNat_toSlice, toNat_ofNat]

public theorem toList_copy_drop {a : UInt32Array.Slice} {j : Nat} (h : j < a.size) :
    a.copy.toList.drop j = a[j] :: a.copy.toList.drop (j + 1) := by
  rw [List.drop_eq_getElem_cons (by simpa using h)]
  simp

/-! ## `USize` indices

The compiled loops use `USize` indices, which need these facts to agree with the `Nat` indices of
the specifications.
-/

/-- `x + y` in `USize` does not wrap when the sum is below `USize.size`. -/
public theorem toNat_add_usize {x y : USize} (h : x.toNat + y.toNat < USize.size) :
    (x + y).toNat = x.toNat + y.toNat := by
  rw [USize.toNat_add]
  exact Nat.mod_eq_of_lt h

public theorem toNat_toUSize {n : Nat} (h : n < USize.size) : n.toUSize.toNat = n := by
  simp [Nat.mod_eq_of_lt h]

/--
The guard of the compiled loops: below `2³² - 1`, a literal that the compiler builds cheaply and
that is a small `Nat` on 64-bit platforms, where comparing with `USize.size = 2⁶⁴` goes through a
big number. (A literal of `2³²` or more is built from a string at each use.)
-/
public theorem lt_usizeSize {n : Nat} (h : n < 4294967295) : n < USize.size :=
  Nat.lt_of_lt_of_le (Nat.lt_succ_of_lt h) USize.le_size

public theorem uget_eq_getElem (a : UInt32Array) (i : USize) (k : Nat) (hk : i.toNat = k)
    (h : i.toNat < a.size) : a.uget i h = a[k]'(hk ▸ h) := by
  subst hk
  rfl

public theorem uset_eq_set (a : UInt32Array) (i : USize) (k : Nat) (hk : i.toNat = k) (v : UInt32)
    (h : i.toNat < a.size) : a.uset i v h = a.set k v (hk ▸ h) := by
  subst hk
  rfl

/--
Limb `k` of the `len` limbs of `arr` from `st` on, read with `USize` indices, as the folds of the
compiled loops do. They bind `arr` and `st` before the fold so that its loop reads neither from the
slice.
-/
@[inline] public def limbU (arr : UInt32Array) (st len : USize) (has : arr.size < USize.size)
    (h : st.toNat + len.toNat ≤ arr.size) (k : USize) (hk : k.toNat < len.toNat) : UInt32 :=
  arr.uget (st + k) (by rw [toNat_add_usize (by lia)]; lia)

/-- `limbU` reads the element of `arr` at `st + k`. -/
public theorem limbU_eq_getElem (arr : UInt32Array) (st len : USize) (has : arr.size < USize.size)
    (h : st.toNat + len.toNat ≤ arr.size) (k : USize) (hk : k.toNat < len.toNat) (i : Nat)
    (hi : st.toNat + k.toNat = i) : limbU arr st len has h k hk = arr[i]'(by lia) := by
  rw [limbU, uget_eq_getElem _ _ i (by rw [toNat_add_usize (by lia)]; exact hi)]

/-- The bound that `limbU` needs to read the limbs of a slice. -/
public theorem limbU_bound (a : UInt32Array.Slice) (has : a.array.size < USize.size) :
    a.start.toUSize.toNat + a.size.toUSize.toNat ≤ a.array.size := by
  have := a.stop_le_array_size
  have := a.start_le_stop
  have := a.size_eq
  rw [toNat_toUSize (by lia), toNat_toUSize (by lia)]
  lia

public theorem limbU_eq (a : UInt32Array.Slice) (has : a.array.size < USize.size) (k : Nat)
    (hk) (hk' : k < a.size) :
    limbU a.array a.start.toUSize a.size.toUSize has (limbU_bound a has) k.toUSize hk = a[k] := by
  have := a.stop_le_array_size
  have := a.start_le_stop
  have := a.size_eq
  have hidx : (a.start.toUSize + k.toUSize).toNat = a.start + k := by
    rw [toNat_add_usize (by rw [toNat_toUSize (by lia), toNat_toUSize (by lia)]; lia),
      toNat_toUSize (by lia), toNat_toUSize (by lia)]
  rw [limbU, uget_eq_getElem _ _ _ hidx]
  rfl

/-- `a` followed by `n` zero limbs, which has the same value. -/
public def padZeros (a : UInt32Array) (n : Nat) : UInt32Array := a ++ .replicate n 0

@[simp] public theorem size_padZeros (a : UInt32Array) (n : Nat) :
    (padZeros a n).size = a.size + n := by
  simp [padZeros]

@[simp] public theorem toNat_padZeros (a : UInt32Array) (n : Nat) :
    toNat (padZeros a n) = toNat a := by
  rw [toNat_toSlice, toNat_toSlice, padZeros, UInt32Array.toList_append,
    UInt32Array.toList_replicate, ofLimbs_append_replicate_zero]

/-- The limbs of `a` in a new array of `n` limbs, padded with zeros, copied with one `memcpy`. -/
public def copyPadded (a : UInt32Array.Slice) (n : Nat) : UInt32Array :=
  a.array.copySlice a.start (.replicate n 0) 0 a.size

public theorem toList_copyPadded (a : UInt32Array.Slice) (n : Nat) :
    (copyPadded a n).toList = a.copy.toList ++ List.replicate (n - a.size) 0 := by
  have := a.stop_le_array_size
  have := a.start_le_stop
  have hs := a.size_eq
  have hstop : a.start + a.size = a.stop := by lia
  have hmin : min a.size (a.array.size - a.start) = a.size := by lia
  simp only [copyPadded, UInt32Array.toList_copySlice, UInt32Array.toList_replicate,
    UInt32Array.size_replicate, Nat.zero_add, hstop, hmin, List.extract_eq_take_drop,
    List.drop_replicate, Nat.sub_zero, List.take_replicate, Nat.min_def, UInt32Array.Slice.copy,
    UInt32Array.toList_extract]
  simp only [Nat.le_refl, ↓reduceIte]
  rfl

@[simp] public theorem size_copyPadded (a : UInt32Array.Slice) (n : Nat) (h : a.size ≤ n) :
    (copyPadded a n).size = n := by
  rw [← UInt32Array.length_toList, toList_copyPadded a n, List.length_append,
    UInt32Array.length_toList, UInt32Array.Slice.size_copy, List.length_replicate]
  lia

public theorem toNat_copyPadded (a : UInt32Array.Slice) (n : Nat) :
    toNat (copyPadded a n) = toNat a := by
  rw [toNat_toSlice, toList_copyPadded a n, ofLimbs_append_replicate_zero]
  rfl

/--
Writing the first `len` limbs of `src` into `dest` at limb `off` with `copySlice`: the value
changes by the limbs written minus those they replace, of which there are `min len src.size`.
-/
public theorem ofLimbs_copySlice (src dest : UInt32Array) (off len : Nat)
    (hfit : off + len ≤ dest.size) :
    (src.copySlice 0 dest off len).size = dest.size ∧
      ofLimbs (src.copySlice 0 dest off len).toList +
          2 ^ (32 * off) * ofLimbs ((dest.toList.drop off).take (min len src.size)) =
        ofLimbs dest.toList + 2 ^ (32 * off) * ofLimbs (src.toList.take len) := by
  rw [UInt32Array.copySlice_eq_append]
  simp only [Nat.sub_zero, Nat.zero_add]
  refine ⟨by simp; lia, ?_⟩
  simp only [UInt32Array.toList_append, UInt32Array.toList_extract, List.extract_eq_take_drop,
    List.drop_zero, Nat.sub_zero]
  -- `src.take len` has `c = min len src.size` limbs.
  have hc : src.toList.take len = src.toList.take (min len src.size) := by
    rw [List.take_eq_take_iff]; simp
  rw [hc]
  generalize hcd : min len src.size = c
  have hcl : c ≤ len := by lia
  have hcs : c ≤ src.size := by lia
  have hD := ofLimbs_append (dest.toList.take off) (dest.toList.drop off)
  rw [List.take_append_drop] at hD
  have hD' := ofLimbs_append ((dest.toList.drop off).take c) ((dest.toList.drop off).drop c)
  rw [List.take_append_drop, List.drop_drop] at hD'
  have hlo : (dest.toList.take off).length = off := by simp; lia
  have hmid : (src.toList.take c).length = c := by simp; lia
  have hwin : ((dest.toList.drop off).take c).length = c := by simp; lia
  rw [hlo] at hD
  rw [hwin] at hD'
  rw [ofLimbs_append, ofLimbs_append, hlo, List.length_append, hlo, hmid,
    List.take_of_length_le (l := List.drop (off + c) dest.toList) (by simp), hD, hD']
  rw [Nat.mul_add 32 off c, Nat.pow_add, Nat.mul_add (2 ^ (32 * off)), ← Nat.mul_assoc]
  lia

/-- Shifts a number left by `k` limbs. -/
public def shiftLimbs (a : UInt32Array) (k : Nat) : UInt32Array :=
  if a.isEmpty then a else .replicate k 0 ++ a

@[simp] public theorem toNat_shiftLimbs (a : UInt32Array) (k : Nat) :
    toNat (shiftLimbs a k) = toNat a * 2 ^ (32 * k) := by
  by_cases h : a.isEmpty = true
  · have hs : a.size = 0 := by simpa [UInt32Array.isEmpty] using h
    have h0 : toNat a = 0 := toNat_of_size_eq_zero (by simpa using hs)
    rw [shiftLimbs, ite_eq_left h, h0, Nat.zero_mul]
  · rw [shiftLimbs, ite_eq_right h, toNat_toSlice, toNat_toSlice, UInt32Array.toList_append,
      ofLimbs_append, UInt32Array.toList_replicate, ofLimbs_replicate_zero, List.length_replicate,
      Nat.zero_add, Nat.mul_comm]

/-- One limb as an array. -/
@[expose] public def limbArray (c : UInt32) : UInt32Array := .replicate 1 c

public theorem size_limbArray (c : UInt32) : (limbArray c).toSlice.size = 1 := by
  simp [limbArray]

public theorem toNat_limbArray (c : UInt32) : toNat (limbArray c) = c.toNat := by
  rw [toNat_toSlice]
  simp [limbArray, UInt32Array.toList_replicate]

/-- An array of zeros is zero. -/
public theorem toNat_zeros (n : Nat) : toNat (UInt32Array.replicate n 0) = 0 := by
  rw [toNat_toSlice]
  simp [UInt32Array.toList_replicate]

/-- The value of the copy of a slice. -/
@[simp] public theorem toNat_copy (a : UInt32Array.Slice) : toNat a.copy = toNat a := by
  rw [toNat_toSlice]
  rfl

/-- The limbs `j` to `k` of `r` hold `⌊r / βʲ⌋` when `r < βᵏ`. -/
public theorem toNat_window (r : UInt32Array) (j k : Nat) (hjk : j ≤ k)
    (hr : toNat r < 2 ^ (32 * k)) :
    toNat (r.toSlice j k) = toNat r / 2 ^ (32 * j) := by
  rw [toNat_toSlice] at hr ⊢
  have hsplit := ofLimbs_append (r.toList.take j) (r.toList.drop j)
  rw [List.take_append_drop] at hsplit
  have hlow := ofLimbs_take_lt r.toList j
  have hlen : (r.toList.take j).length = j ∨ r.toList.length < j := by
    simp only [List.length_take]; lia
  have hdrop : ofLimbs (r.toList.drop j) = ofLimbs r.toList / 2 ^ (32 * j) := by
    rcases hlen with hl | hl
    · rw [hl] at hsplit
      rw [hsplit, Nat.add_mul_div_left _ _ (Nat.two_pow_pos _), Nat.div_eq_of_lt hlow,
        Nat.zero_add]
    · rw [List.drop_of_length_le (by lia), ofLimbs_nil]
      have := ofLimbs_lt r.toList
      have : 2 ^ (32 * r.toList.length) ≤ 2 ^ (32 * j) :=
        Nat.pow_le_pow_right (by decide) (by lia)
      exact (Nat.div_eq_of_lt (by lia)).symm
  have hbound : ofLimbs (r.toList.drop j) < 2 ^ (32 * (k - j)) := by
    rw [hdrop, Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _), ← Nat.pow_add]
    rw [show 32 * (k - j) + 32 * j = 32 * k by lia]
    exact hr
  simp only [toNat, UInt32Array.copy_toSlice, UInt32Array.toList_extract,
    List.extract_eq_take_drop, ofLimbs_take_of_lt hbound, hdrop]

/-! ## Compiled conversions

`toNat` and `ofNat` go one limb at a time, as `ofLimbs` does, multiplying or dividing a growing
`Nat` at each limb, which takes quadratic time. Their compiled twins split the limbs in halves
and join or split the halves with shifts, which `Nat` does in linear time, so that the conversions
take `O(n log n)`. `@[csimp]` makes the compiler use them.
-/

/-- The value of the `n` limbs of `s` from `i` on, by halves. -/
def toNatRange (s : UInt32Array.Slice) (i n : Nat) : Nat :=
  if n = 0 then 0
  else if n = 1 then (s.getD i 0).toNat
  else if n = 2 then
    ((s.getD (i + 1) 0).toUInt64 * 4294967296 + (s.getD i 0).toUInt64).toNat
  else
    toNatRange s i (n / 2) + toNatRange s (i + n / 2) (n - n / 2) <<< (32 * (n / 2))
termination_by n

private theorem toNatRange_eq (s : UInt32Array.Slice) (i n : Nat) (h : i + n ≤ s.size) :
    toNatRange s i n = ofLimbs ((s.copy.toList.drop i).take n) := by
  induction n using Nat.strongRecOn generalizing i with
  | ind n ih =>
    rw [toNatRange]
    have hg : ∀ j (hj : j < s.size), s.getD j 0 = s[j]'hj := fun j hj => by
      simp [UInt32Array.Slice.getD_eq, hj]
    split
    · subst n; simp
    · split
      · subst n
        rw [toList_copy_drop (by lia), hg i (by lia)]
        simp
      · split
        · subst n
          rw [toList_copy_drop (by lia), toList_copy_drop (by lia), hg i (by lia),
            hg (i + 1) (by lia)]
          have := (s[i]'(by lia)).toNat_lt
          have := (s[i + 1]'(by lia)).toNat_lt
          simp only [List.take_succ_cons, List.take_zero, ofLimbs_cons, ofLimbs_nil]
          simp only [UInt64.toNat_add, UInt64.toNat_mul, UInt32.toNat_toUInt64,
            UInt64.reduceToNat]
          lia
        · rename_i h0 h1 h2
          rw [ih _ (by lia) i (by lia), ih _ (by lia) (i + n / 2) (by lia),
            Nat.shiftLeft_eq]
          have hlen : (s.copy.toList.drop i).length = s.size - i := by simp
          have e : (s.copy.toList.drop i).take n = (s.copy.toList.drop i).take (n / 2) ++
              (s.copy.toList.drop (i + n / 2)).take (n - n / 2) := by
            conv => lhs; rw [show n = n / 2 + (n - n / 2) by lia]
            rw [List.take_add, List.drop_drop]
          rw [e, ofLimbs_append, List.length_take, hlen, Nat.min_eq_left (by lia), Nat.mul_comm]

/-- `toNat` by halves, which the compiler uses in its place. -/
public def toNatFast (s : UInt32Array.Slice) : Nat := toNatRange s 0 s.size

@[csimp] public theorem toNat_eq_toNatFast : @toNat = @toNatFast := by
  funext s
  rw [toNatFast, toNatRange_eq s 0 s.size (by lia), List.drop_zero,
    List.take_of_length_le (by simp), toNat]

/--
Pushes the `k` limbs of `x % 2^(32 k)` onto `acc`: by halves above `64` limbs, and below, two limbs
at a time from the low word of `x`, which `toUInt64` reads without an operation on `Nat`.
-/
def ofNatPush (x k : Nat) (acc : UInt32Array) : UInt32Array :=
  if k = 0 then acc
  else if k = 1 then acc.push x.toUInt32
  else if k ≤ 64 then
    let u := x.toUInt64
    ofNatPush (x >>> 64) (k - 2) ((acc.push u.toUInt32).push (u >>> 32).toUInt32)
  else
    let hi := x >>> (32 * (k / 2))
    ofNatPush hi (k - k / 2) (ofNatPush (x - hi <<< (32 * (k / 2))) (k / 2) acc)
termination_by k

private theorem ofNatPush_spec (x k : Nat) (acc : UInt32Array) :
    ∃ L, (ofNatPush x k acc).toList = acc.toList ++ L ∧ L.length = k ∧
      ofLimbs L = x % 2 ^ (32 * k) := by
  induction k using Nat.strongRecOn generalizing x acc with
  | ind k ih =>
    rw [ofNatPush]
    split
    · subst k
      exact ⟨[], by simp, rfl, by simp [Nat.mod_one]⟩
    · split
      · subst k
        refine ⟨[x.toUInt32], by simp, rfl, ?_⟩
        simp [Nat.toUInt32_eq, UInt32.toNat_ofNat']
      · split
        · rename_i h0 h1 h2
          dsimp only
          obtain ⟨L, hL, hl, hv⟩ := ih (k - 2) (by lia) (x >>> 64)
            ((acc.push x.toUInt64.toUInt32).push (x.toUInt64 >>> 32).toUInt32)
          refine ⟨[x.toUInt64.toUInt32, (x.toUInt64 >>> 32).toUInt32] ++ L, by rw [hL]; simp,
            by simp; lia, ?_⟩
          have hu : x.toUInt64.toNat = x % 2 ^ 64 := by simp [Nat.toUInt64_eq, UInt64.toNat_ofNat']
          rw [ofLimbs_append, hv]
          simp only [ofLimbs_cons, ofLimbs_nil, List.length_cons, List.length_nil,
            UInt64.toNat_toUInt32, UInt64.toNat_shiftRight, hu, Nat.shiftRight_eq_div_pow,
            UInt64.reduceToNat, Nat.reduceMod]
          rw [show 32 * k = 64 + 32 * (k - 2) by lia, Nat.pow_add, Nat.mod_mul]
          lia
        · rename_i h0 h1 h2
          dsimp only
          have hP : 0 < 2 ^ (32 * (k / 2)) := Nat.two_pow_pos _
          have hlo : x - (x >>> (32 * (k / 2))) <<< (32 * (k / 2)) = x % 2 ^ (32 * (k / 2)) := by
            rw [Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq, Nat.mod_def, Nat.mul_comm]
          obtain ⟨L₁, h₁, hl₁, hv₁⟩ := ih (k / 2) (by lia)
            (x - (x >>> (32 * (k / 2))) <<< (32 * (k / 2))) acc
          obtain ⟨L₂, h₂, hl₂, hv₂⟩ := ih (k - k / 2) (by lia) (x >>> (32 * (k / 2)))
            (ofNatPush (x - (x >>> (32 * (k / 2))) <<< (32 * (k / 2))) (k / 2) acc)
          refine ⟨L₁ ++ L₂, by rw [h₂, h₁, List.append_assoc], by simp; lia, ?_⟩
          rw [ofLimbs_append, hv₁, hv₂, hl₁, hlo, Nat.mod_mod, Nat.shiftRight_eq_div_pow,
            show 32 * k = 32 * (k / 2) + 32 * (k - k / 2) by lia, Nat.pow_add, Nat.mod_mul]

/-- `ofNat` by halves, which the compiler uses in its place. -/
public def ofNatFast (n : Nat) : UInt32Array :=
  if n = 0 then .empty
  else ofNatPush n (n.log2 / 32 + 1) (.emptyWithCapacity (n.log2 / 32 + 1))

@[csimp] public theorem ofNat_eq_ofNatFast : @ofNat = @ofNatFast := by
  funext n
  rw [ofNatFast]
  split
  · subst n
    simp [ofNat, ofNat.loop]
  · rename_i hn
    obtain ⟨L, hL, hl, hv⟩ := ofNatPush_spec n (n.log2 / 32 + 1)
      (.emptyWithCapacity (n.log2 / 32 + 1))
    simp only [UInt32Array.emptyWithCapacity_eq_empty, UInt32Array.toList_empty,
      List.nil_append] at hL
    have hlt : n < 2 ^ (32 * (n.log2 / 32 + 1)) :=
      Nat.lt_of_lt_of_le (Nat.lt_log2_self) (Nat.pow_le_pow_right (by decide) (by lia))
    have hge : 2 ^ (32 * (n.log2 / 32)) ≤ n :=
      Nat.le_trans (Nat.pow_le_pow_right (by decide) (by lia)) (Nat.log2_self_le hn)
    rw [Nat.mod_eq_of_lt hlt] at hv
    -- `L` is trimmed: its top limb is not zero, since `n ≥ 2^(32 (k - 1))`.
    have htr : IsTrimmed L := by
      intro hlast
      rw [List.getLast?_eq_getElem?, hl, show n.log2 / 32 + 1 - 1 = n.log2 / 32 by lia] at hlast
      have hk : n.log2 / 32 < L.length := by lia
      rw [List.getElem?_eq_getElem hk, Option.some.injEq] at hlast
      have hsplit := ofLimbs_take_add_one L (n.log2 / 32) hk
      rw [List.take_of_length_le (by lia), hlast] at hsplit
      have := ofLimbs_take_lt L (n.log2 / 32)
      simp only [UInt32.toNat_zero, Nat.mul_zero, Nat.add_zero] at hsplit
      lia
    apply UInt32Array.toList_inj.1
    rw [UInt32Array.emptyWithCapacity_eq_empty, hL]
    apply IsTrimmed.ofLimbs_inj ((isTrimmed_iff _).1 (isTrimmed_ofNat _)) htr
    rw [← toNat_toSlice, toNat_ofNat, hv]

end MPN
