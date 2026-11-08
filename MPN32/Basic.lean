/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ScalarArray.UInt32
public import MPN32.FoldInPlace
public import MPN32.Arch.UIntArray
public import MPN.Trim

/-!
# Natural numbers as limbs

A natural number is stored as little-endian base 2³² limbs in a `UInt32Array`. The arithmetic
works on slices of limbs, so it accepts trailing zero limbs, and its results are trimmed so that
the most significant limb is nonzero.

The specification is `toNat`, the value of the limbs of a slice by `valAt`, as in `main`'s
kernels. Trimmed arrays represent each natural number exactly once, and `ofNat` and `toNat` are
inverse bijections between them and `Nat`.
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

/-- The natural number that a slice of limbs denotes: its limbs by `valAt`. -/
@[expose] public def toNat (s : UInt32Array.Slice) : Nat := s.array.valAt s.start s.size

/-! ## Specification -/

/-- The value of a library slice, by `valAt`. -/
public theorem toNat_eq_valAt (s : UInt32Array.Slice) :
    MPN.W32.toNat s = s.array.valAt s.start s.size := rfl

/-- The limbs `i` to `j - 1` of an array, which are zero past its end. -/
@[simp] public theorem toNat_toSlice (a : UInt32Array) (i j : Nat) :
    toNat (a.toSlice i j) = a.valAt i (j - i) := by
  rw [toNat_eq_valAt, UInt32Array.array_toSlice, UInt32Array.start_toSlice,
    UInt32Array.size_toSlice]
  by_cases h : i ≤ min j a.size
  · rw [Nat.min_eq_left h, ← UInt32Array.valAt_size_sub a i (j - i)]
    congr 1
    lia
  · rw [show min j a.size - i = 0 by lia, UInt32Array.valAt_zero]
    by_cases hj : j ≤ i
    · rw [show j - i = 0 by lia, UInt32Array.valAt_zero]
    · rw [UInt32Array.valAt_of_size_le _ _ (by lia)]

/-- The value of an array, by `valAt`. -/
public theorem toNat_array_eq_valAt (a : UInt32Array) :
    MPN.W32.toNat a.toSlice = a.valAt 0 a.size := by
  simp

/-- The limbs `i` to `j - 1` of a slice, which are zero past its end. -/
@[simp] public theorem toNat_slice (s : UInt32Array.Slice) (i j : Nat) :
    toNat (s.slice i j) = s.array.valAt (s.start + i) (min j s.size - i) := by
  rw [UInt32Array.Slice.slice, toNat_toSlice]
  by_cases h : i ≤ s.size
  · rw [Nat.min_eq_left h]
    congr 1
    lia
  · rw [Nat.min_eq_right (by lia), show min j s.size - i = 0 by lia,
      show s.start + min j s.size - (s.start + s.size) = 0 by lia]
    simp

/-- The limbs of `s` from `j` on, with limb `j` apart, which `getD` reads as `0` past the end. -/
public theorem valAt_from (s : UInt32Array.Slice) (j : Nat) :
    s.array.valAt (s.start + j) (s.size - j) =
      (s.getD j 0).toNat + 2 ^ 32 * s.array.valAt (s.start + (j + 1)) (s.size - (j + 1)) := by
  rw [UInt32Array.Slice.getD_eq]
  by_cases h : j < s.size
  · rw [show s.size - j = s.size - (j + 1) + 1 by lia, UInt32Array.valAt_succ, dite_eq_left h,
      UInt32Array.Slice.getElem_eq_getElem!, Nat.add_assoc]
  · rw [show s.size - j = 0 by lia, show s.size - (j + 1) = 0 by lia, dite_eq_right h]
    simp

/-- The limbs of `s` from `j` on, with limb `j` apart. -/
public theorem valAt_from_of_lt (s : UInt32Array.Slice) {j : Nat} (h : j < s.size) :
    s.array.valAt (s.start + j) (s.size - j) =
      s[j].toNat + 2 ^ 32 * s.array.valAt (s.start + (j + 1)) (s.size - (j + 1)) := by
  rw [valAt_from, UInt32Array.Slice.getD_eq, dite_eq_left h]

/-- No limbs of `s` from `j` on. -/
public theorem valAt_from_of_le (s : UInt32Array.Slice) {j : Nat} (h : s.size ≤ j) :
    s.array.valAt (s.start + j) (s.size - j) = 0 := by
  rw [show s.size - j = 0 by lia, UInt32Array.valAt_zero]

/-- `valAt` only depends on the limbs it reads, wherever they sit. -/
public theorem valAt_shift {a b : UInt32Array} {i j : Nat} :
    ∀ n, (∀ k, k < n → b[j + k]! = a[i + k]!) → b.valAt j n = a.valAt i n
  | 0, _ => rfl
  | n + 1, h => by
    rw [UInt32Array.valAt_succ, UInt32Array.valAt_succ, ← Nat.add_zero j, ← Nat.add_zero i,
      h 0 (by lia), Nat.add_zero, Nat.add_zero,
      valAt_shift (i := i + 1) (j := j + 1) n fun k hk => by
        rw [Nat.add_right_comm, Nat.add_right_comm i, Nat.add_assoc, Nat.add_assoc]
        exact h (k + 1) (by lia)]

/-- The value of the limbs `i` to `j - 1` of an array, extracted. -/
@[simp] public theorem toNat_extract (a : UInt32Array) (i j : Nat) :
    toNat (a.extract i j) = a.valAt i (j - i) := by
  rw [toNat_array_eq_valAt, UInt32Array.size_extract, ← UInt32Array.valAt_size_sub a i (j - i),
    show min (j - i) (a.size - i) = min j a.size - i by lia]
  exact valAt_shift _ fun k hk => by
    rw [Nat.zero_add, getElem!_pos _ k (by simp; lia), getElem!_pos a (i + k) (by lia),
      UInt32Array.getElem_extract]

public theorem toNat_of_size_eq_zero {s : UInt32Array.Slice} (h : s.size = 0) : toNat s = 0 := by
  rw [toNat_eq_valAt, h, UInt32Array.valAt_zero]

public theorem toNat_of_size_eq_one {s : UInt32Array.Slice} (h : s.size = 1) :
    toNat s = (s[0]'(by lia)).toNat := by
  rw [toNat_eq_valAt, h, UInt32Array.valAt_one, UInt32Array.Slice.getElem_eq_getElem!,
    Nat.add_zero]

/-- Splitting a slice at `k` splits its value. -/
public theorem toNat_slice_add_toNat_slice (s : UInt32Array.Slice) (k : Nat) (hk : k ≤ s.size) :
    toNat (s.slice 0 k) + 2 ^ (32 * k) * toNat (s.slice k s.size) = toNat s := by
  have h := UInt32Array.valAt_add s.array s.start k (s.size - k)
  rw [show k + (s.size - k) = s.size by lia] at h
  rw [toNat_slice, toNat_slice, toNat_eq_valAt, h, Nat.min_eq_left hk, Nat.min_self,
    Nat.add_zero, Nat.sub_zero]

/-- Splitting the limbs of `s` from `i` at `i + m`, also when `i + m` is past the end. -/
public theorem toNat_slice_split (s : UInt32Array.Slice) (i m : Nat) :
    toNat (s.slice i s.size) =
      toNat (s.slice i (i + m)) + 2 ^ (32 * m) * toNat (s.slice (i + m) s.size) := by
  rw [toNat_slice, toNat_slice, toNat_slice, Nat.min_self, ← Nat.add_assoc]
  by_cases h : i + m ≤ s.size
  · rw [Nat.min_eq_left h, show s.size - i = (i + m - i) + (s.size - (i + m)) by lia,
      UInt32Array.valAt_add, show i + m - i = m by lia, Nat.add_assoc]
  · rw [Nat.min_eq_right (by lia), show s.size - (i + m) = 0 by lia, UInt32Array.valAt_zero,
      Nat.mul_zero, Nat.add_zero]

/-- The value of an array is its low `m` limbs plus `2^(32 m)` times the rest. -/
public theorem toNat_split (x : UInt32Array) (m : Nat) (hm : m ≤ x.size) :
    toNat x = toNat (x.toSlice 0 m) + 2 ^ (32 * m) * toNat (x.toSlice m x.size) := by
  rw [toNat_toSlice, toNat_toSlice, toNat_toSlice, Nat.sub_zero, Nat.sub_zero,
    show x.size = m + (x.size - m) by lia, UInt32Array.valAt_add, Nat.zero_add,
    show m + (x.size - m) - m = x.size - m by lia]

/-- Cutting an array to its first `n` limbs keeps a value below `2^(32 n)`. -/
public theorem toNat_toSlice_of_lt (a : UInt32Array) (n : Nat) (h : toNat a < 2 ^ (32 * n)) :
    toNat (a.toSlice 0 n) = toNat a := by
  simp only [toNat_toSlice, Nat.sub_zero] at h ⊢
  by_cases hn : a.size ≤ n
  · exact UInt32Array.valAt_extend a n (by lia) hn
  · rw [UInt32Array.valAt_mod a 0 (show n ≤ a.size by lia), Nat.mod_eq_of_lt h]

public theorem toNat_lt (s : UInt32Array.Slice) : toNat s < 2 ^ (32 * s.size) :=
  UInt32Array.valAt_lt ..

/-- An array whose limbs from `m` on are zero is below `2^(32 m)`. -/
public theorem toNat_lt_of_zero_from (a : UInt32Array) (m : Nat)
    (h : ∀ k (hk : k < a.size), m ≤ k → a[k] = 0) : toNat a < 2 ^ (32 * m) := by
  rw [toNat_toSlice, Nat.sub_zero]
  by_cases hm : a.size ≤ m
  · rw [← UInt32Array.valAt_extend a m (by lia) hm]
    exact UInt32Array.valAt_lt ..
  · have hz : a.valAt m (a.size - m) = 0 :=
      MPN.LimbArray.valAt_eq_zero _ fun i h₁ h₂ => by
        change a[i]!.toNat = 0
        rw [UInt32Array.getElem!_eq_getElem _ _ (by lia), h i (by lia) h₁]
        rfl
    rw [show a.size = m + (a.size - m) by lia, UInt32Array.valAt_add, Nat.zero_add, hz,
      Nat.mul_zero, Nat.add_zero]
    exact UInt32Array.valAt_lt ..

/-- The top limb of a trimmed array is not zero. -/
public theorem getElem_top_ne_zero {a : UInt32Array} (h : isTrimmed a = true) (hs : 0 < a.size) :
    a[a.size - 1] ≠ 0 := by
  simpa [isTrimmed, hs] using h

@[simp] public theorem toNat_trim (a : UInt32Array) : toNat (trim a) = toNat a := by
  rw [toNat_array_eq_valAt, toNat_array_eq_valAt]
  exact WordArray.valAt_trimTo 0 a

public theorem size_trim_le (a : UInt32Array) : (trim a).size ≤ a.size :=
  WordArray.size_trimTo_le 0 a

/-- `main`'s `WordArray.isTrimmedTo 0` is `isTrimmed`. -/
public theorem isTrimmed_of_isTrimmedTo {a : UInt32Array} (h : WordArray.isTrimmedTo 0 a = true) :
    isTrimmed a = true := by
  rw [WordArray.isTrimmedTo_iff] at h
  unfold isTrimmed
  split
  · rename_i hp
    rcases h with h | h
    · exact absurd h (by show ¬a.size ≤ 0; lia)
    · have h' : (a[a.size - 1]!).toNat ≠ 0 := h
      rw [getElem!_pos a (a.size - 1) (by lia)] at h'
      simp only [bne_iff_ne, ne_eq]
      exact fun e => h' (by rw [e]; rfl)
  · rfl

public theorem isTrimmed_trim (a : UInt32Array) : isTrimmed (trim a) = true :=
  isTrimmed_of_isTrimmedTo (WordArray.isTrimmedTo_trimTo 0 a)

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

/-- A trimmed array is at least `β^(n - 1)`, for its `n` limbs. -/
private theorem pow_le_toNat {b : UInt32Array} (hb : isTrimmed b = true) (hs : 0 < b.size) :
    2 ^ (32 * (b.size - 1)) ≤ toNat b := by
  have ht := getElem_top_ne_zero hb hs
  have e := UInt32Array.valAt_add b 0 (b.size - 1) 1
  rw [show b.size - 1 + 1 = b.size by lia, UInt32Array.valAt_one, Nat.zero_add,
    UInt32Array.getElem!_eq_getElem _ _ (by lia)] at e
  have hpos : 1 ≤ b[b.size - 1].toNat :=
    Nat.pos_of_ne_zero fun h0 => ht (UInt32.toNat_inj.1 (by rw [h0]; rfl))
  have := Nat.mul_le_mul_left (2 ^ (32 * (b.size - 1))) hpos
  rw [toNat_array_eq_valAt, e]
  lia

/-- An array with fewer limbs than a trimmed array is below it. -/
private theorem toNat_lt_of_size_lt {a b : UInt32Array} (hb : isTrimmed b = true)
    (h : a.size < b.size) : toNat a < toNat b := by
  have := UInt32Array.valAt_lt a 0 a.size
  have := Nat.pow_le_pow_right (show 0 < 2 by decide) (show 32 * a.size ≤ 32 * (b.size - 1) by lia)
  have := pow_le_toNat hb (by lia)
  rw [toNat_array_eq_valAt] at this
  rw [toNat_array_eq_valAt, toNat_array_eq_valAt]
  lia

/-- Trimmed arrays of the same value have the same size. -/
public theorem size_eq_of_toNat_eq {a b : UInt32Array} (ha : isTrimmed a = true)
    (hb : isTrimmed b = true) (h : toNat a = toNat b) : a.size = b.size := by
  rcases Nat.lt_trichotomy a.size b.size with hl | he | hg
  · exact absurd h (Nat.ne_of_lt (toNat_lt_of_size_lt hb hl))
  · exact he
  · exact absurd h (Nat.ne_of_gt (toNat_lt_of_size_lt ha hg))

/-- A trimmed array is the limbs of the number it denotes. -/
public theorem ofNat_toNat {a : UInt32Array} (h : isTrimmed a = true) : ofNat (toNat a) = a := by
  have hv := toNat_ofNat (toNat a)
  refine UInt32Array.eq_of_valAt_eq (size_eq_of_toNat_eq (isTrimmed_ofNat _) h hv) ?_
  rw [← toNat_array_eq_valAt, ← toNat_array_eq_valAt, hv]

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

/-- The value of the copy of a slice. -/
@[simp] public theorem toNat_copy (a : UInt32Array.Slice) : toNat a.copy = toNat a := by
  rw [toNat_array_eq_valAt, UInt32Array.Slice.size_copy, toNat_eq_valAt]
  exact valAt_shift _ fun k hk => by
    rw [Nat.zero_add, getElem!_pos _ k (by simp; lia), UInt32Array.Slice.getElem_copy,
      UInt32Array.Slice.getElem_eq_getElem!]

/-- `a` followed by `n` zero limbs, which has the same value. -/
public def padZeros (a : UInt32Array) (n : Nat) : UInt32Array := a ++ .replicate n 0

@[simp] public theorem size_padZeros (a : UInt32Array) (n : Nat) :
    (padZeros a n).size = a.size + n := by
  simp [padZeros]

@[simp] public theorem toNat_padZeros (a : UInt32Array) (n : Nat) :
    toNat (padZeros a n) = toNat a := by
  rw [toNat_array_eq_valAt, toNat_array_eq_valAt, size_padZeros, UInt32Array.valAt_add,
    Nat.zero_add]
  have hz : (padZeros a n).valAt a.size n = 0 :=
    MPN.LimbArray.valAt_eq_zero _ fun i h₁ h₂ => by
      change (padZeros a n)[i]!.toNat = 0
      rw [getElem!_pos _ i (by simp; lia)]
      simp only [padZeros, UInt32Array.getElem_append, dite_eq_right (show ¬i < a.size by lia),
        UInt32Array.getElem_replicate]
      rfl
  rw [hz, Nat.mul_zero, Nat.add_zero]
  exact valAt_shift _ fun k hk => by
    rw [Nat.zero_add, getElem!_pos _ k (by simp; lia), getElem!_pos a k hk]
    simp only [padZeros, UInt32Array.getElem_append, dite_eq_left hk]

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
  have e : copyPadded a n = padZeros a.copy (n - a.size) := UInt32Array.toList_inj.1 (by
    rw [toList_copyPadded, padZeros, UInt32Array.toList_append, UInt32Array.toList_replicate])
  rw [e, toNat_padZeros, toNat_copy]

/-- Shifts a number left by `k` limbs. -/
public def shiftLimbs (a : UInt32Array) (k : Nat) : UInt32Array :=
  if a.isEmpty then a else .replicate k 0 ++ a

@[simp] public theorem toNat_shiftLimbs (a : UInt32Array) (k : Nat) :
    toNat (shiftLimbs a k) = toNat a * 2 ^ (32 * k) := by
  by_cases h : a.isEmpty = true
  · have hs : a.size = 0 := by simpa [UInt32Array.isEmpty] using h
    have h0 : toNat a = 0 := toNat_of_size_eq_zero (by simpa using hs)
    rw [shiftLimbs, ite_eq_left h, h0, Nat.zero_mul]
  · rw [shiftLimbs, ite_eq_right h, toNat_array_eq_valAt, toNat_array_eq_valAt,
      UInt32Array.size_append, UInt32Array.size_replicate, UInt32Array.valAt_add, Nat.zero_add]
    have hz : (UInt32Array.replicate k 0 ++ a).valAt 0 k = 0 :=
      MPN.LimbArray.valAt_eq_zero _ fun i h₁ h₂ => by
        change (UInt32Array.replicate k 0 ++ a)[i]!.toNat = 0
        rw [getElem!_pos _ i (by simp; lia)]
        simp only [UInt32Array.getElem_append, UInt32Array.size_replicate,
          dite_eq_left (show i < k by lia), UInt32Array.getElem_replicate]
        rfl
    rw [hz, Nat.zero_add, Nat.mul_comm]
    congr 1
    exact valAt_shift _ fun j hj => by
      rw [Nat.zero_add, getElem!_pos _ (k + j) (by simp; lia), getElem!_pos a j hj]
      simp only [UInt32Array.getElem_append, UInt32Array.size_replicate,
        dite_eq_right (show ¬k + j < k by lia), Nat.add_sub_cancel_left]

@[simp] public theorem toNat_empty : toNat UInt32Array.empty = 0 := rfl

public theorem isTrimmed_empty : isTrimmed UInt32Array.empty = true := by
  simp [isTrimmed]

/-- A limb pushed on top of `a`. -/
@[simp] public theorem toNat_push (a : UInt32Array) (x : UInt32) :
    toNat (a.push x) = toNat a + 2 ^ (32 * a.size) * x.toNat := by
  rw [toNat_array_eq_valAt, toNat_array_eq_valAt, UInt32Array.size_push, UInt32Array.valAt_add,
    UInt32Array.valAt_one, Nat.zero_add, getElem!_pos _ a.size (by simp)]
  simp only [UInt32Array.getElem_push, dite_eq_right (Nat.lt_irrefl _)]
  congr 1
  exact valAt_shift _ fun k hk => by
    rw [Nat.zero_add, getElem!_pos _ k (by simp; lia), getElem!_pos a k hk]
    simp only [UInt32Array.getElem_push, dite_eq_left hk]

/-- A nonzero limb pushed on top of an array makes it trimmed. -/
public theorem isTrimmed_push (a : UInt32Array) {x : UInt32} (hx : x ≠ 0) :
    isTrimmed (a.push x) = true := by
  simpa [isTrimmed] using hx

/-- One limb as an array. -/
@[expose] public def limbArray (c : UInt32) : UInt32Array := .replicate 1 c

public theorem size_limbArray (c : UInt32) : (limbArray c).toSlice.size = 1 := by
  simp [limbArray]

public theorem toNat_limbArray (c : UInt32) : toNat (limbArray c) = c.toNat := by
  rw [toNat_array_eq_valAt, limbArray, UInt32Array.size_replicate, UInt32Array.valAt_one,
    getElem!_pos _ 0 (by simp), UInt32Array.getElem_replicate]

/-- An array of zeros is zero. -/
public theorem toNat_zeros (n : Nat) : toNat (UInt32Array.replicate n 0) = 0 := by
  rw [toNat_array_eq_valAt]
  simp

/-- The limbs `j` to `k` of `r` hold `⌊r / βʲ⌋` when `r < βᵏ`. -/
public theorem toNat_window (r : UInt32Array) (j k : Nat) (hjk : j ≤ k)
    (hr : toNat r < 2 ^ (32 * k)) :
    toNat (r.toSlice j k) = toNat r / 2 ^ (32 * j) := by
  rw [toNat_toSlice, toNat_array_eq_valAt]
  rw [toNat_array_eq_valAt] at hr
  have hN := UInt32Array.valAt_extend r (lo := 0) (m := r.size) (max k r.size) (by lia) (by lia)
  have hsplit := UInt32Array.valAt_add r 0 j (max k r.size - j)
  rw [show j + (max k r.size - j) = max k r.size by lia, hN, Nat.zero_add] at hsplit
  have hdiv : r.valAt 0 r.size / 2 ^ (32 * j) = r.valAt j (max k r.size - j) := by
    rw [hsplit, Nat.add_mul_div_left _ _ (Nat.two_pow_pos _),
      Nat.div_eq_of_lt (UInt32Array.valAt_lt ..), Nat.zero_add]
  have hbound : r.valAt j (max k r.size - j) < 2 ^ (32 * (k - j)) := by
    rw [← hdiv, Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _), ← Nat.pow_add,
      show 32 * (k - j) + 32 * j = 32 * k by lia]
    exact hr
  rw [hdiv, UInt32Array.valAt_mod r j (show k - j ≤ max k r.size - j by lia),
    Nat.mod_eq_of_lt hbound]

/-! ## Compiled conversions

`toNat` and `ofNat` go one limb at a time, multiplying or dividing a growing
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
    toNatRange s i n = s.array.valAt (s.start + i) n := by
  induction n using Nat.strongRecOn generalizing i with
  | ind n ih =>
    rw [toNatRange]
    have hg : ∀ j (hj : j < s.size), s.getD j 0 = s[j]'hj := fun j hj => by
      simp [UInt32Array.Slice.getD_eq, hj]
    split
    · subst n; simp
    · split
      · subst n
        rw [UInt32Array.valAt_one, hg i (by lia), UInt32Array.Slice.getElem_eq_getElem!]
      · split
        · subst n
          rw [UInt32Array.valAt_succ, UInt32Array.valAt_one, hg i (by lia), hg (i + 1) (by lia),
            UInt32Array.Slice.getElem_eq_getElem!, UInt32Array.Slice.getElem_eq_getElem!,
            ← Nat.add_assoc]
          have := (s.array[s.start + i]!).toNat_lt
          have := (s.array[s.start + i + 1]!).toNat_lt
          simp only [UInt64.toNat_add, UInt64.toNat_mul, UInt32.toNat_toUInt64,
            UInt64.reduceToNat]
          lia
        · rename_i h0 h1 h2
          rw [ih _ (by lia) i (by lia), ih _ (by lia) (i + n / 2) (by lia), Nat.shiftLeft_eq]
          conv => rhs; rw [show n = n / 2 + (n - n / 2) by lia]
          rw [UInt32Array.valAt_add, show s.start + i + n / 2 = s.start + (i + n / 2) by lia,
            Nat.mul_comm (2 ^ (32 * (n / 2)))]

/-- `toNat` by halves, which the compiler uses in its place. -/
public def toNatFast (s : UInt32Array.Slice) : Nat := toNatRange s 0 s.size

@[csimp] public theorem toNat_eq_toNatFast : @toNat = @toNatFast := by
  funext s
  rw [toNatFast, toNatRange_eq s 0 s.size (by lia), Nat.add_zero, toNat_eq_valAt]

end MPN.W32
