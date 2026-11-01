/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ScalarArray.UInt32
public import MPN32.Limbs
public import MPN32.FoldInPlace
public import MPN32.Arch.UIntArray
public import MPN.Trim

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

namespace MPN.W32

/-- Removes the trailing zero limbs, in place when `a` is not shared (`WordArray.trimTo 0`). -/
public def trim (a : UInt32Array) : UInt32Array := WordArray.trimTo 0 a

/-- Whether the most significant limb is nonzero. -/
public def isTrimmed (a : UInt32Array) : Bool :=
  if h : 0 < a.size then a[a.size - 1] != 0 else true

/-- The limbs of a natural number: none for `0`, and `main`'s `WordArray.ofNatW`, by halves. -/
public def ofNat (n : Nat) : UInt32Array := if n = 0 then .empty else WordArray.ofNatW n

/-- The natural number that a slice of limbs denotes. -/
@[expose] public def toNat (s : UInt32Array.Slice) : Nat := ofLimbs s.copy.toList

/-! ## Specification -/

@[simp] public theorem toNat_toSlice (a : UInt32Array) : toNat a.toSlice = ofLimbs a.toList := by
  simp [toNat]

/-! ## Values by `valAt`

`toNat` of a slice or an array is `valAt` of its range of limbs, for the parts that work on windows
of arrays: `main`'s kernels, the FFT and the instance of the Toom methods.
-/

/-- The limbs `lo` to `lo + n - 1` of `a`, read as a list, have the value `valAt`. -/
public theorem ofLimbs_drop_take (a : UInt32Array) (lo n : Nat) :
    ofLimbs ((a.toList.drop lo).take n) = a.valAt lo n := by
  have hz : ∀ m lo', a.size ≤ lo' → a.valAt lo' m = 0 := by
    intro m
    induction m with
    | zero => simp
    | succ m ihm =>
      intro lo' h'
      rw [UInt32Array.valAt_succ, ihm (lo' + 1) (by lia), getElem!_neg a lo' (by lia)]; rfl
  induction n generalizing lo with
  | zero => simp
  | succ n ih =>
    rcases Nat.lt_or_ge lo a.size with h | h
    · rw [UInt32Array.valAt_succ, List.drop_eq_getElem_cons (by simpa using h), List.take_succ_cons,
        ofLimbs_cons, ih (lo + 1), UInt32Array.getElem!_eq_getElem _ _ h]
      simp
    · rw [List.drop_eq_nil_of_le (by simpa using h), hz _ lo h]
      simp

/-- The value of a library slice, by `valAt`. -/
public theorem toNat_eq_valAt (s : UInt32Array.Slice) :
    MPN.W32.toNat s = s.array.valAt s.start s.size := by
  rw [MPN.W32.toNat, ← ofLimbs_drop_take]
  congr 1
  rw [UInt32Array.Slice.copy, UInt32Array.toList_extract, List.extract_eq_take_drop,
    UInt32Array.Slice.size_eq]

/-- The value of an array, by `valAt`. -/
public theorem toNat_array_eq_valAt (a : UInt32Array) :
    MPN.W32.toNat a.toSlice = a.valAt 0 a.size := by
  rw [toNat_toSlice, ← ofLimbs_drop_take, List.drop_zero, List.take_of_length_le (by simp)]


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

public theorem toList_trim (a : UInt32Array) : (trim a).toList = trimLimbs a.toList := by
  induction hn : a.size using Nat.strongRecOn generalizing a with
  | ind n ih =>
  rw [trim, WordArray.trimTo]
  split
  · rename_i h
    change 0 < a.size at h
    have hne : a.toList ≠ [] := by
      intro h'; have := congrArg List.length h'; simp at this; lia
    have hl : a.toList.getLast hne = a[a.size - 1] := by simp [List.getLast_eq_getElem]
    rw [trimLimbs_of_getLast _ hne, hl]
    split
    · rename_i hz
      have hz' : a[a.size - 1] = 0 := by
        have := (WordArray.isZero_iff _).1 hz
        change a[a.size - 1]!.toNat = 0 at this
        rw [UInt32Array.getElem!_eq_getElem _ _ (by lia)] at this
        exact UInt32.toNat_inj.1 this
      rw [ite_eq_left hz', ← UInt32Array.toList_pop]
      exact ih (n - 1) (by lia) a.pop (by rw [UInt32Array.size_pop, hn])
    · rename_i hz
      have hz' : ¬a[a.size - 1] = 0 := fun e => hz ((WordArray.isZero_iff _).2 (by
        change a[a.size - 1]!.toNat = 0
        rw [UInt32Array.getElem!_eq_getElem _ _ (by lia), e]; rfl))
      rw [ite_eq_right hz']
  · rename_i h
    change ¬0 < a.size at h
    have : a.toList = [] := List.eq_nil_of_length_eq_zero (by simp; lia)
    rw [this]
    rfl

@[simp] public theorem toNat_trim (a : UInt32Array) : toNat (trim a) = toNat a := by
  simp [toList_trim]

public theorem size_trim_le (a : UInt32Array) : (trim a).size ≤ a.size :=
  WordArray.size_trimTo_le 0 a

public theorem isTrimmed_trim (a : UInt32Array) : isTrimmed (trim a) = true := by
  simp [isTrimmed_iff, toList_trim, isTrimmed_trimLimbs]

@[simp] public theorem toNat_ofNat (n : Nat) : toNat (ofNat n) = n := by
  by_cases hn : n = 0
  · have e : ofNat n = .empty := by rw [ofNat, ite_eq_left hn]
    rw [e, hn]; rfl
  · have e : ofNat n = WordArray.ofNatW n := by rw [ofNat, ite_eq_right hn]
    rw [e, toNat_array_eq_valAt]
    exact WordArray.valAt_ofNatW n

public theorem isTrimmed_ofNat (n : Nat) : isTrimmed (ofNat n) = true := by
  by_cases hn : n = 0
  · have e : ofNat n = .empty := by rw [ofNat, ite_eq_left hn]
    rw [e]; rfl
  · have e : ofNat n = WordArray.ofNatW n := by rw [ofNat, ite_eq_right hn]
    rw [e]
    have hpos : 0 < (WordArray.ofNatW (A := UInt32Array) n).size := by
      rw [show (WordArray.ofNatW (A := UInt32Array) n).size =
        LimbArray.size (WordArray.ofNatW (A := UInt32Array) n) from rfl, WordArray.size_ofNatW]
      lia
    have ht := WordArray.top_ofNatW (A := UInt32Array) hn
    rw [isTrimmed, dite_eq_left hpos, bne_iff_ne, ne_eq]
    intro h0
    apply ht
    change (WordArray.ofNatW (A := UInt32Array) n)[
      (WordArray.ofNatW (A := UInt32Array) n).size - 1]!.toNat = 0
    rw [UInt32Array.getElem!_eq_getElem _ _ (by exact Nat.sub_lt hpos (by decide))]
    rw [h0]; rfl

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

end MPN.W32
