/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import MPN.Mul.Toom4
public import MPN.Cmp
public import MPN.Mul.FFT

/-!
# Residues modulo `2ᴺ + 1`

The FFT computes modulo the Fermat number `F = 2ᴺ + 1` with `N = 32 n`. A residue is `n + 1`
limbs holding a value below `F`, and each operation returns one: its value is the result reduced
modulo `F`. Since `2ᴺ ≡ -1`, a value `lo + 2ᴺ hi` reduces to `lo - hi`, and multiplying by `2ˢ` is
a rotation of the limbs in which the limbs that wrap around change sign, then a shift by
`s mod 32` bits.
-/

open ScalarArray

namespace MPN.Fermat

/-- The Fermat number `2^(32 n) + 1`. -/
@[expose] public def fermat (n : Nat) : Nat := 2 ^ (32 * n) + 1

/-- `fermat n` as `n + 1` limbs. -/
public def fermatArray (n : Nat) : UInt32Array :=
  addInto (addInto (.replicate (n + 1) 0) n (limbArray 1)) 0 (limbArray 1)

private theorem size_fermatArray₁ (n : Nat) :
    (addInto (.replicate (n + 1) 0) n (limbArray 1)).size = n + 1 := by
  rw [size_addInto _ _ _ (by rw [size_limbArray]; simp)]; simp

public theorem size_fermatArray (n : Nat) : (fermatArray n).size = n + 1 := by
  simp only [fermatArray]
  rw [size_addInto _ _ _ (by rw [size_limbArray, size_fermatArray₁]; lia), size_fermatArray₁]

public theorem toNat_fermatArray (n : Nat) : toNat (fermatArray n) = fermat n := by
  have hz := toNat_zeros (n + 1)
  have s₁ := size_fermatArray₁ n
  have hp : 2 ^ (32 * n) < 2 ^ (32 * (n + 1)) := Nat.pow_lt_pow_right (by decide) (by lia)
  have v₁ : toNat (addInto (.replicate (n + 1) 0) n (limbArray 1)) = 2 ^ (32 * n) := by
    rw [toNat_addInto_of_lt _ _ _ (by rw [size_limbArray]; simp)
      (by rw [hz, toNat_limbArray]; simpa using hp), hz, toNat_limbArray]
    simp
  simp only [fermatArray]
  rw [toNat_addInto_of_lt _ _ _ (by rw [size_limbArray, s₁]; lia)
    (by rw [v₁, toNat_limbArray, s₁]; simp; have : 1 ≤ 2 ^ (32 * n) := Nat.one_le_two_pow; lia),
    v₁, toNat_limbArray]
  simp [fermat]

/-- `fermat n` as an array, with its size and value: built once per product. -/
public structure FermatMod (n : Nat) where
  arr : UInt32Array
  size_eq : arr.size = n + 1
  toNat_eq : toNat arr = fermat n

/-- The array of `fermat n`. -/
public def fermatMod (n : Nat) : FermatMod n :=
  ⟨fermatArray n, size_fermatArray n, toNat_fermatArray n⟩

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

public theorem toNat_copy (s : UInt32Array.Slice) : toNat s.copy = toNat s := by
  rw [toNat_toSlice]; rfl

/-! ## Reduction -/

/--
`lo - hi` modulo `F` for `x = lo + 2ᴺ hi` with `hi` below `2³²`: `lo - hi` when it is not
negative, and `F - (hi - lo)` otherwise.
-/
public def reduceSmall {n : Nat} (M : FermatMod n) (x : UInt32Array) : UInt32Array :=
  let lo := copyPadded (x.toSlice 0 n) (n + 1)
  let hi := (x.toSlice n x.size).copy
  if lt lo hi then subVal (M.arr) (subVal hi lo) else subVal lo hi

public theorem size_reduceSmall {n : Nat} (M : FermatMod n) (x : UInt32Array) :
    (reduceSmall M x).size = n + 1 := by
  simp only [reduceSmall]
  split
  · rw [size_subVal, M.size_eq]
  · rw [size_subVal]; exact size_copyPadded _ _ (by simp; lia)

public theorem toNat_reduceSmall {n : Nat} (M : FermatMod n) (x : UInt32Array) (hn1 : 1 ≤ n)
    (hn : n ≤ x.size)
    (hx : toNat x < 2 ^ (32 * n) * 2 ^ 32) : toNat (reduceSmall M x) = toNat x % fermat n := by
  have hsplit := toNat_split x n hn
  have hlo : toNat (x.toSlice 0 n) < 2 ^ (32 * n) := by
    have := toNat_lt (x.toSlice 0 n)
    simp only [UInt32Array.size_toSlice] at this
    exact Nat.lt_of_lt_of_le this (Nat.pow_le_pow_right (by decide) (by lia))
  have hhi : toNat (x.toSlice n x.size) < 2 ^ 32 := by
    rw [hsplit] at hx
    have : 2 ^ (32 * n) * toNat (x.toSlice n x.size) < 2 ^ (32 * n) * 2 ^ 32 := by lia
    exact Nat.lt_of_mul_lt_mul_left this
  have hP : 2 ^ 32 ≤ 2 ^ (32 * n) := Nat.pow_le_pow_right (by decide) (by lia)
  generalize hL : toNat (x.toSlice 0 n) = L at *
  generalize hH : toNat (x.toSlice n x.size) = H at *
  have tlo : toNat (copyPadded (x.toSlice 0 n) (n + 1)) = L := by rw [toNat_copyPadded, hL]
  have thi : toNat (x.toSlice n x.size).copy = H := by rw [toNat_copy, hH]
  rw [hsplit]
  by_cases hlt : L < H
  · have e : reduceSmall M x = subVal (M.arr)
        (subVal (x.toSlice n x.size).copy (copyPadded (x.toSlice 0 n) (n + 1))) := by
      have : lt (copyPadded (x.toSlice 0 n) (n + 1)) (x.toSlice n x.size).copy = true := by
        rw [lt_iff, tlo, thi]; exact hlt
      simp only [reduceSmall, this, ↓reduceIte]
    have hF := M.toNat_eq
    have hd : toNat (subVal (x.toSlice n x.size).copy (copyPadded (x.toSlice 0 n) (n + 1))) =
        H - L := by rw [toNat_subVal _ _ (by rw [tlo, thi]; lia), tlo, thi]
    rw [e, toNat_subVal _ _ (by rw [hd, hF]; simp only [fermat]; lia), hd, hF]
    -- `L + 2ᴺ H = (F - (H - L)) + (H - 1) F`.
    obtain ⟨H', rfl⟩ : ∃ H', H = H' + 1 := ⟨H - 1, by lia⟩
    have e₂ : L + 2 ^ (32 * n) * (H' + 1) = (fermat n - (H' + 1 - L)) + H' * fermat n := by
      simp only [fermat, Nat.mul_add, Nat.mul_one]
      lia
    rw [e₂, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt (by simp only [fermat]; lia)]
  · have e : reduceSmall M x =
        subVal (copyPadded (x.toSlice 0 n) (n + 1)) (x.toSlice n x.size).copy := by
      have : lt (copyPadded (x.toSlice 0 n) (n + 1)) (x.toSlice n x.size).copy = false := by
        rw [Bool.eq_false_iff, ne_eq, lt_iff, tlo, thi]; exact hlt
      simp only [reduceSmall, this, Bool.false_eq_true, ↓reduceIte]
    rw [e, toNat_subVal _ _ (by rw [tlo, thi]; lia), tlo, thi]
    -- `L + 2ᴺ H = (L - H) + H F`.
    have e₂ : L + 2 ^ (32 * n) * H = (L - H) + H * fermat n := by
      simp only [fermat]; rw [Nat.mul_add, Nat.mul_one, Nat.mul_comm H]; lia
    rw [e₂, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt (by simp only [fermat]; lia)]

/-! ## Sums and differences -/

/-- `x + y` modulo `F`, for residues `x` and `y`. -/
public def addMod {n : Nat} (M : FermatMod n) (x y : UInt32Array) : UInt32Array := reduceSmall M
    (addLimbs x y)

public theorem size_addMod {n : Nat} (M : FermatMod n) (x y : UInt32Array) :
    (addMod M x y).size = n + 1 :=
  size_reduceSmall M _

public theorem toNat_addMod {n : Nat} (M : FermatMod n) (x y : UInt32Array) (hn : 1 ≤ n)
    (hx : x.size = n + 1)
    (hy : y.size = n + 1) (hxF : toNat x < fermat n) (hyF : toNat y < fermat n) :
    toNat (addMod M x y) = (toNat x + toNat y) % fermat n := by
  have hP : 2 ^ 32 ≤ 2 ^ (32 * n) := Nat.pow_le_pow_right (by decide) (by lia)
  have hb : toNat (addLimbs x y) < 2 ^ (32 * n) * 2 ^ 32 := by
    rw [toNat_addLimbs]
    simp only [fermat] at hxF hyF
    have : 4 ≤ 2 ^ 32 := by decide
    have := Nat.mul_le_mul_left (2 ^ (32 * n)) this
    lia
  simp only [addMod]
  rw [toNat_reduceSmall M _ hn (by simp [hx, hy]; lia) hb, toNat_addLimbs]

/-- `x - y` modulo `F`, for residues `x` and `y`: `F - (y - x)` when `x < y`. -/
public def subMod {n : Nat} (M : FermatMod n) (x y : UInt32Array) : UInt32Array :=
  if lt x y then subVal (M.arr) (subVal y x) else subVal x y

public theorem size_subMod {n : Nat} (M : FermatMod n) (x y : UInt32Array) (hx : x.size = n + 1) :
    (subMod M x y).size = n + 1 := by
  simp only [subMod]
  split
  · rw [size_subVal, M.size_eq]
  · rw [size_subVal, hx]

public theorem toNat_subMod {n : Nat} (M : FermatMod n) (x y : UInt32Array)
    (hxF : toNat x < fermat n)
    (hyF : toNat y < fermat n) :
    toNat (subMod M x y) = (toNat x + fermat n - toNat y) % fermat n := by
  by_cases h : toNat x < toNat y
  · have e : subMod M x y = subVal (M.arr) (subVal y x) := by
      have : lt x y = true := by rw [lt_iff]; exact h
      simp only [subMod, this, ↓reduceIte]
    rw [e, toNat_subVal _ _ (by rw [toNat_subVal _ _ (by lia), M.toNat_eq]; lia),
      toNat_subVal _ _ (by lia), M.toNat_eq, Nat.mod_eq_of_lt (by lia)]
    lia
  · have e : subMod M x y = subVal x y := by
      have : lt x y = false := by rw [Bool.eq_false_iff, ne_eq, lt_iff]; exact h
      simp only [subMod, this, Bool.false_eq_true, ↓reduceIte]
    rw [e, toNat_subVal _ _ (by lia),
      show toNat x + fermat n - toNat y = (toNat x - toNat y) + 1 * fermat n by lia,
      Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt (by lia)]

public theorem toNat_subMod_lt {n : Nat} (M : FermatMod n) (x y : UInt32Array)
    (hxF : toNat x < fermat n)
    (hyF : toNat y < fermat n) : toNat (subMod M x y) < fermat n := by
  rw [toNat_subMod M x y hxF hyF]
  exact Nat.mod_lt _ (by simp [fermat])

/-! ## Multiplication by a power of two -/

/--
`x 2^(32 w)` modulo `F`, for `w < n`: the low `n - w` limbs of `x` move up by `w` limbs, and the
top `w + 1` limbs, which pass `2ᴺ`, come back subtracted.
-/
public def rotWords {n : Nat} (M : FermatMod n) (x : UInt32Array) (w : Nat) : UInt32Array :=
  subMod M (addInto (.replicate (n + 1) 0) w (x.toSlice 0 (n - w))) (x.toSlice (n - w) x.size).copy

/-- `y 2ᵇ` modulo `F`, for `b < 32`, by `mulRow` and `reduceSmall`. -/
public def shiftBits {n : Nat} (M : FermatMod n) (y : UInt32Array) (b : Nat) : UInt32Array :=
  reduceSmall M (mulRow y (2 ^ b).toUInt32)

/-- `x 2ˢ` modulo `F`: since `2^(2N) ≡ 1` and `2ᴺ ≡ -1`, a rotation by words, a shift by bits and
a negation for the second half of the period. -/
public def mulPow2 {n : Nat} (M : FermatMod n) (x : UInt32Array) (s : Nat) : UInt32Array :=
  let t := s % (64 * n)
  if t < 32 * n then shiftBits M (rotWords M x (t / 32)) (t % 32)
  else subMod M (.replicate (n + 1) 0)
    (shiftBits M (rotWords M x ((t - 32 * n) / 32)) ((t - 32 * n) % 32))

public theorem size_rotWords {n : Nat} (M : FermatMod n) (x : UInt32Array) (w : Nat) (hw : w < n) :
    (rotWords M x w).size = n + 1 := by
  simp only [rotWords]
  exact size_subMod M _ _ (by rw [size_addInto _ _ _ (by simp; lia)]; simp)

public theorem toNat_rotWords {n : Nat} (M : FermatMod n) (x : UInt32Array) (w : Nat) (hw : w < n)
    (hx : x.size = n + 1) (hxF : toNat x < fermat n) :
    toNat (rotWords M x w) = (toNat x * 2 ^ (32 * w)) % fermat n := by
  have hsplit := toNat_split x (n - w) (by lia)
  have hLlt : toNat (x.toSlice 0 (n - w)) < 2 ^ (32 * (n - w)) := by
    have := toNat_lt (x.toSlice 0 (n - w))
    simpa [show min (n - w) x.size = n - w by lia] using this
  have hpow : 2 ^ (32 * n) = 2 ^ (32 * (n - w)) * 2 ^ (32 * w) := by
    rw [← Nat.pow_add]; congr 1; lia
  have hwn : 2 ^ (32 * w) < 2 ^ (32 * n) := Nat.pow_lt_pow_right (by decide) (by lia)
  have hz := toNat_zeros (n + 1)
  -- The low part, moved up by `w` limbs, is below `2ᴺ`.
  have hAlt : 2 ^ (32 * w) * toNat (x.toSlice 0 (n - w)) < 2 ^ (32 * n) := by
    rw [hpow, Nat.mul_comm (2 ^ (32 * (n - w)))]
    exact Nat.mul_lt_mul_of_pos_left hLlt (Nat.two_pow_pos _)
  have hz' : toNat ((UInt32Array.replicate (n + 1) 0).toSlice 0 (n + 1)) = 0 := by
    simpa using hz
  have hA : toNat (addInto (.replicate (n + 1) 0) w (x.toSlice 0 (n - w))) =
      2 ^ (32 * w) * toNat (x.toSlice 0 (n - w)) := by
    have hle : 2 ^ (32 * n) ≤ 2 ^ (32 * (n + 1)) := Nat.pow_le_pow_right (by decide) (by lia)
    have hfit : w + (x.toSlice 0 (n - w)).size ≤ (UInt32Array.replicate (n + 1) 0).size := by
      simp; lia
    have hlt : toNat (UInt32Array.replicate (n + 1) 0) + 2 ^ (32 * w) *
        toNat (x.toSlice 0 (n - w)) < 2 ^ (32 * (UInt32Array.replicate (n + 1) 0).size) := by
      simp only [UInt32Array.size_replicate, hz']; lia
    rw [toNat_addInto_of_lt _ _ _ hfit hlt]
    simp_all
  have hH := toNat_copy (x.toSlice (n - w) x.size)
  generalize toNat (x.toSlice 0 (n - w)) = L at *
  generalize toNat (x.toSlice (n - w) x.size) = Hv at *
  -- The wrapped part is at most `2^(32 w)`, since `x ≤ 2ᴺ`.
  have hHv : Hv ≤ 2 ^ (32 * w) := by
    have : 2 ^ (32 * (n - w)) * Hv ≤ 2 ^ (32 * (n - w)) * 2 ^ (32 * w) := by
      simp only [fermat] at hxF; lia
    exact Nat.le_of_mul_le_mul_left this (Nat.two_pow_pos _)
  simp only [rotWords]
  rw [toNat_subMod M _ _ (by rw [hA]; simp only [fermat]; lia)
    (by rw [hH]; simp only [fermat]; lia), hA, hH, hsplit]
  -- `(L + 2^(32(n - w)) H) 2^(32 w) + F = (2^(32 w) L + F - H) + H F`.
  have e : (L + 2 ^ (32 * (n - w)) * Hv) * 2 ^ (32 * w) + fermat n =
      (2 ^ (32 * w) * L + fermat n - Hv) + Hv * fermat n := by
    simp only [fermat]
    rw [Nat.add_mul, Nat.mul_assoc, Nat.mul_comm Hv, ← Nat.mul_assoc, ← hpow, Nat.mul_comm L,
      Nat.mul_add, Nat.mul_one, Nat.mul_comm Hv]
    lia
  rw [← Nat.add_mod_right ((L + 2 ^ (32 * (n - w)) * Hv) * 2 ^ (32 * w)), e,
    Nat.add_mul_mod_self_right]

public theorem toNat_rotWords_lt {n : Nat} (M : FermatMod n) (x : UInt32Array) (w : Nat)
    (hw : w < n)
    (hx : x.size = n + 1) (hxF : toNat x < fermat n) : toNat (rotWords M x w) < fermat n := by
  rw [toNat_rotWords M x w hw hx hxF]
  exact Nat.mod_lt _ (by simp [fermat])

public theorem size_shiftBits {n : Nat} (M : FermatMod n) (y : UInt32Array) (b : Nat) :
    (shiftBits M y b).size = n + 1 :=
  size_reduceSmall M _

public theorem toNat_shiftBits {n : Nat} (M : FermatMod n) (y : UInt32Array) (b : Nat)
    (hn : 1 ≤ n) (hb : b < 32)
    (hy : y.size = n + 1) (hyF : toNat y < fermat n) :
    toNat (shiftBits M y b) = (toNat y * 2 ^ b) % fermat n := by
  have hb' : ((2 ^ b : Nat).toUInt32).toNat = 2 ^ b := by
    simp only [Nat.toUInt32_eq, UInt32.toNat_ofNat']
    exact Nat.mod_eq_of_lt (Nat.pow_lt_pow_right (by decide) hb)
  have hP : 2 ^ b ≤ 2 ^ 31 := Nat.pow_le_pow_right (by decide) (by lia)
  have hlt : toNat (mulRow y (2 ^ b).toUInt32) < 2 ^ (32 * n) * 2 ^ 32 := by
    rw [toNat_mulRow, hb']
    simp only [fermat] at hyF
    have := Nat.mul_le_mul (show toNat y ≤ 2 ^ (32 * n) by lia) hP
    have : 2 ^ (32 * n) * 2 ^ 31 < 2 ^ (32 * n) * 2 ^ 32 :=
      Nat.mul_lt_mul_of_pos_left (by decide) (Nat.two_pow_pos _)
    lia
  simp only [shiftBits]
  rw [toNat_reduceSmall M _ hn (by simp [hy]; lia) hlt, toNat_mulRow, hb']

public theorem toNat_shiftBits_lt {n : Nat} (M : FermatMod n) (y : UInt32Array) (b : Nat)
    (hn : 1 ≤ n)
    (hb : b < 32) (hy : y.size = n + 1) (hyF : toNat y < fermat n) :
    toNat (shiftBits M y b) < fermat n := by
  rw [toNat_shiftBits M y b hn hb hy hyF]
  exact Nat.mod_lt _ (by simp [fermat])

/-- `2^(2N) ≡ 1` modulo `F`. -/
public theorem two_pow_period (n : Nat) : 2 ^ (64 * n) % fermat n = 1 % fermat n := by
  have h := FFT.sq_of_neg_one (y := 2 ^ (32 * n)) (F := fermat n) (by simp [fermat])
  rw [← Nat.pow_add, show 32 * n + 32 * n = 64 * n by lia] at h
  exact h

public theorem size_mulPow2 {n : Nat} (M : FermatMod n) (x : UInt32Array) (s : Nat) :
    (mulPow2 M x s).size = n + 1 := by
  simp only [mulPow2]
  split
  · exact size_shiftBits M _ _
  · exact size_subMod M _ _ (by simp)

public theorem toNat_mulPow2 {n : Nat} (M : FermatMod n) (x : UInt32Array) (s : Nat) (hn : 1 ≤ n)
    (hx : x.size = n + 1) (hxF : toNat x < fermat n) :
    toNat (mulPow2 M x s) = (toNat x * 2 ^ s) % fermat n := by
  -- `2ˢ ≡ 2ᵗ` with `t = s mod 2N`.
  have hq : (2 ^ s) % fermat n = (2 ^ (s % (64 * n))) % fermat n := by
    have hA : ((2 ^ (64 * n)) ^ (s / (64 * n))) % fermat n = 1 % fermat n := by
      rw [Nat.pow_mod, two_pow_period, ← Nat.pow_mod, Nat.one_pow]
    conv => lhs; rw [← Nat.div_add_mod s (64 * n), Nat.pow_add, Nat.pow_mul]
    rw [Nat.mul_mod, hA, ← Nat.mul_mod, Nat.one_mul]
  have hs : (toNat x * 2 ^ s) % fermat n = (toNat x * 2 ^ (s % (64 * n))) % fermat n := by
    rw [Nat.mul_mod, hq, ← Nat.mul_mod]
  rw [hs]
  have ht : s % (64 * n) < 64 * n := Nat.mod_lt _ (by lia)
  have hFpos : 0 < fermat n := by simp [fermat]
  by_cases h : s % (64 * n) < 32 * n
  · have e : mulPow2 M x s =
        shiftBits M (rotWords M x (s % (64 * n) / 32)) (s % (64 * n) % 32) := by
      simp only [mulPow2, h, ↓reduceIte]
    rw [e]
    generalize s % (64 * n) = t at *
    rw [toNat_shiftBits M _ _ hn (Nat.mod_lt _ (by decide)) (size_rotWords M _ _ (by lia))
        (toNat_rotWords_lt M _ _ (by lia) hx hxF),
      toNat_rotWords M _ _ (by lia) hx hxF, Nat.mod_mul_mod, Nat.mul_assoc, ← Nat.pow_add,
      Nat.div_add_mod]
  · have e : mulPow2 M x s = subMod M (.replicate (n + 1) 0)
        (shiftBits M (rotWords M x ((s % (64 * n) - 32 * n) / 32))
          ((s % (64 * n) - 32 * n) % 32)) := by
      simp only [mulPow2, h, ↓reduceIte]
    rw [e]
    generalize s % (64 * n) = t at *
    have hz : toNat (UInt32Array.replicate (n + 1) 0) = 0 := toNat_zeros _
    have hr := toNat_shiftBits M _ ((t - 32 * n) % 32) hn (Nat.mod_lt _ (by decide))
      (size_rotWords M _ ((t - 32 * n) / 32) (by lia))
      (toNat_rotWords_lt M _ _ (by lia) hx hxF)
    rw [toNat_rotWords M _ _ (by lia) hx hxF, Nat.mod_mul_mod, Nat.mul_assoc, ← Nat.pow_add,
      Nat.div_add_mod] at hr
    rw [toNat_subMod M _ _ (by rw [hz]; exact hFpos)
      (toNat_shiftBits_lt M _ _ hn (Nat.mod_lt _ (by decide)) (size_rotWords M _ _ (by lia))
        (toNat_rotWords_lt M _ _ (by lia) hx hxF)), hr, hz, Nat.zero_add]
    -- `x 2ᵗ = x 2^(t - N) 2ᴺ ≡ r (F - 1) ≡ F - r`, with `r = x 2^(t - N) mod F`.
    have hsplit : toNat x * 2 ^ t = toNat x * 2 ^ (t - 32 * n) * (fermat n - 1) := by
      rw [show fermat n - 1 = 2 ^ (32 * n) by simp [fermat], Nat.mul_assoc, ← Nat.pow_add,
        show t - 32 * n + 32 * n = t by lia]
    have hmod : (toNat x * 2 ^ t) % fermat n =
        ((toNat x * 2 ^ (t - 32 * n)) % fermat n * (fermat n - 1)) % fermat n := by
      rw [hsplit, Nat.mul_mod, Nat.mod_eq_of_lt (show fermat n - 1 < fermat n by lia)]
    rw [hmod]
    generalize hR : toNat x * 2 ^ (t - 32 * n) % fermat n = r
    have hrF : r < fermat n := by rw [← hR]; exact Nat.mod_lt _ hFpos
    rcases Nat.eq_zero_or_pos r with h0 | h0
    · subst h0; simp
    · have e₂ : r * (fermat n - 1) = (fermat n - r) + (r - 1) * fermat n := by
        obtain ⟨r', rfl⟩ : ∃ r', r = r' + 1 := ⟨r - 1, by lia⟩
        rw [show r' + 1 - 1 = r' by lia, Nat.add_mul, Nat.one_mul, Nat.mul_sub, Nat.mul_one]
        have : r' ≤ r' * fermat n := Nat.le_mul_of_pos_right _ hFpos
        lia
      rw [e₂, Nat.add_mul_mod_self_right]

public theorem toNat_mulPow2_lt {n : Nat} (M : FermatMod n) (x : UInt32Array) (s : Nat) (hn : 1 ≤ n)
    (hx : x.size = n + 1) (hxF : toNat x < fermat n) : toNat (mulPow2 M x s) < fermat n := by
  rw [toNat_mulPow2 M x s hn hx hxF]
  exact Nat.mod_lt _ (by simp [fermat])

/-! ## Products -/

/-- Adding the same number to both sides of a congruence modulo `F > 0` can be undone. -/
public theorem mod_cancel_add {a b c F : Nat} (hF : 0 < F) (h : (a + c) % F = (b + c) % F) :
    a % F = b % F := by
  have e : ∀ x, x + c + (F - c % F) = x + F * (c / F + 1) := fun x => by
    have := Nat.div_add_mod c F
    have := Nat.mod_lt c hF
    rw [Nat.mul_add, Nat.mul_one]; lia
  have h' : (a + c + (F - c % F)) % F = (b + c + (F - c % F)) % F := by
    rw [Nat.add_mod, h, ← Nat.add_mod]
  rwa [e a, e b, Nat.add_mul_mod_self_left, Nat.add_mul_mod_self_left] at h'

/--
A product `p` of two residues, at most `2^(2N)`, reduced modulo `F`: its low `n` limbs minus the
rest, which is reduced first.
-/
public def normProd {n : Nat} (M : FermatMod n) (p : UInt32Array) : UInt32Array :=
  subMod M (copyPadded (p.toSlice 0 n) (n + 1))
    (reduceSmall M (copyPadded (p.toSlice n p.size) (n + 2)))

public theorem size_normProd {n : Nat} (M : FermatMod n) (p : UInt32Array) :
    (normProd M p).size = n + 1 :=
  size_subMod M _ _ (size_copyPadded _ _ (by simp; lia))

public theorem toNat_normProd {n : Nat} (M : FermatMod n) (p : UInt32Array) (hn : 1 ≤ n)
    (hp : p.size ≤ 2 * n + 2)
    (hn' : n ≤ p.size) (hval : toNat p ≤ 2 ^ (32 * n) * 2 ^ (32 * n)) :
    toNat (normProd M p) = toNat p % fermat n := by
  have hFpos : 0 < fermat n := by simp [fermat]
  have hsplit := toNat_split p n hn'
  have hlo : toNat (p.toSlice 0 n) < 2 ^ (32 * n) := by
    have := toNat_lt (p.toSlice 0 n)
    simpa [show min n p.size = n by lia] using this
  have hhi : toNat (p.toSlice n p.size) ≤ 2 ^ (32 * n) := by
    rw [hsplit] at hval
    have : 2 ^ (32 * n) * toNat (p.toSlice n p.size) ≤ 2 ^ (32 * n) * 2 ^ (32 * n) := by lia
    exact Nat.le_of_mul_le_mul_left this (Nat.two_pow_pos _)
  have hP : 1 ≤ 2 ^ 32 := by decide
  have hcp : (copyPadded (p.toSlice n p.size) (n + 2)).size = n + 2 :=
    size_copyPadded _ _ (by simp; lia)
  have hh := toNat_reduceSmall M (copyPadded (p.toSlice n p.size) (n + 2)) hn (by lia) (by
    rw [toNat_copyPadded]
    have := Nat.mul_le_mul_left (2 ^ (32 * n)) hP
    have : 2 ^ (32 * n) * 1 < 2 ^ (32 * n) * 2 ^ 32 :=
      Nat.mul_lt_mul_of_pos_left (by decide) (Nat.two_pow_pos _)
    lia)
  rw [toNat_copyPadded] at hh
  simp only [normProd]
  rw [toNat_subMod M _ _ (by rw [toNat_copyPadded]; simp only [fermat]; lia)
    (by rw [hh]; exact Nat.mod_lt _ hFpos), toNat_copyPadded, hh, hsplit]
  generalize toNat (p.toSlice 0 n) = L at *
  generalize toNat (p.toSlice n p.size) = H at *
  -- Add `h = H mod F` to both sides: each becomes `L` modulo `F`.
  apply mod_cancel_add hFpos (c := H % fermat n)
  have hHF : H % fermat n < fermat n := Nat.mod_lt _ hFpos
  rw [show L + fermat n - H % fermat n + H % fermat n = L + 1 * fermat n by lia,
    Nat.add_mul_mod_self_right]
  -- `2ᴺ H + h ≡ 2ᴺ h + h = F h ≡ 0`.
  have hz : (2 ^ (32 * n) * H + H % fermat n) % fermat n = 0 := by
    have e : 2 ^ (32 * n) * H + H % fermat n =
        fermat n * (2 ^ (32 * n) * (H / fermat n) + H % fermat n) := by
      have hd := Nat.div_add_mod H (fermat n)
      generalize H / fermat n = q at hd ⊢
      generalize H % fermat n = r at hd ⊢
      rw [← hd]
      simp only [fermat]
      grind
    rw [e, Nat.mul_mod_right]
  rw [Nat.add_assoc, Nat.add_mod, hz, Nat.add_zero, Nat.mod_mod]

public theorem toNat_normProd_lt {n : Nat} (M : FermatMod n) (p : UInt32Array) (hn : 1 ≤ n)
    (hp : p.size ≤ 2 * n + 2) (hn' : n ≤ p.size) (hval : toNat p ≤ 2 ^ (32 * n) * 2 ^ (32 * n)) :
    toNat (normProd M p) < fermat n := by
  rw [toNat_normProd M p hn hp hn' hval]
  exact Nat.mod_lt _ (by simp [fermat])

/-! ## In-place sums and differences -/

/-- `2F` fits in `n + 1` limbs. -/
private theorem two_fermat_lt (n : Nat) (hn : 1 ≤ n) : 2 * fermat n < 2 ^ (32 * (n + 1)) := by
  have h₁ : 2 ^ (32 * (n + 1)) = 2 ^ (32 * n) * 2 ^ 32 := by rw [← Nat.pow_add]; congr 1
  have h₂ : 2 ^ (32 * n) * 4 ≤ 2 ^ (32 * n) * 2 ^ 32 := Nat.mul_le_mul_left _ (by decide)
  have h₃ : 2 ≤ 2 ^ (32 * n) := by
    have := Nat.pow_le_pow_right (show 0 < 2 by decide) (show 1 ≤ 32 * n by lia)
    simpa using this
  simp only [fermat]; lia

/--
`x + y` modulo `F`, in place in `x` (a residue of `n + 1` limbs) when `x` is not shared: the sum
fits in `n + 1` limbs, and `F` is subtracted when it is not below `F`.
-/
public def addModI {n : Nat} (M : FermatMod n) (x : UInt32Array) (y : UInt32Array.Slice) :
    UInt32Array :=
  let s := addInto x 0 y
  if lt s M.arr then s else subInto s 0 M.arr

public theorem size_addModI {n : Nat} (M : FermatMod n) (x : UInt32Array) (y : UInt32Array.Slice)
    (hx : x.size = n + 1) (hy : y.size ≤ n + 1) : (addModI M x y).size = n + 1 := by
  have hMs := M.size_eq
  have hss : (addInto x 0 y).size = n + 1 := by rw [size_addInto _ _ _ (by lia), hx]
  simp only [addModI]
  split
  · exact hss
  · rw [size_subInto _ _ _ (by simp [hss, hMs]), hss]

public theorem toNat_addModI {n : Nat} (M : FermatMod n) (x : UInt32Array) (y : UInt32Array.Slice)
    (hn : 1 ≤ n) (hx : x.size = n + 1) (hy : y.size ≤ n + 1) (hxF : toNat x < fermat n)
    (hyF : toNat y < fermat n) : toNat (addModI M x y) = (toNat x + toNat y) % fermat n := by
  have h2 := two_fermat_lt n hn
  have hMs := M.size_eq
  have hF := M.toNat_eq
  have hlt : toNat x + 2 ^ (32 * 0) * toNat y < 2 ^ (32 * x.size) := by
    rw [hx]; simp only [Nat.mul_zero, Nat.pow_zero, Nat.one_mul]; lia
  have hs : toNat (addInto x 0 y) = toNat x + toNat y := by
    rw [toNat_addInto_of_lt _ _ _ (by lia) hlt]; simp
  have hss : (addInto x 0 y).size = n + 1 := by rw [size_addInto _ _ _ (by lia), hx]
  by_cases h : toNat x + toNat y < fermat n
  · have e : addModI M x y = addInto x 0 y := by
      have : lt (addInto x 0 y) M.arr = true := by rw [lt_iff, hs, hF]; exact h
      simp only [addModI, this, ↓reduceIte]
    rw [e, hs, Nat.mod_eq_of_lt h]
  · have e : addModI M x y = subInto (addInto x 0 y) 0 M.arr := by
      have : lt (addInto x 0 y) M.arr = false := by
        rw [Bool.eq_false_iff, ne_eq, lt_iff, hs, hF]; exact h
      simp only [addModI, this, Bool.false_eq_true, ↓reduceIte]
    have hle : 2 ^ (32 * 0) * toNat M.arr ≤ toNat (addInto x 0 y) := by
      simp only [Nat.mul_zero, Nat.pow_zero, Nat.one_mul, hs, hF]; lia
    rw [e, toNat_subInto_of_le _ _ _ (by simp [hss, hMs]) hle, hs, hF]
    simp only [Nat.mul_zero, Nat.pow_zero, Nat.one_mul]
    rw [Nat.mod_eq_sub_mod (by lia), Nat.mod_eq_of_lt (by lia)]

/--
`x - y` modulo `F`, in place in `x` (a residue of `n + 1` limbs) when `x` is not shared: `x - y`
when `y ≤ x`, and `(x + F) - y` otherwise, which also fits in `n + 1` limbs.
-/
public def subModI {n : Nat} (M : FermatMod n) (x : UInt32Array) (y : UInt32Array.Slice) :
    UInt32Array :=
  if lt x y then subInto (addInto x 0 M.arr) 0 y else subInto x 0 y

public theorem size_subModI {n : Nat} (M : FermatMod n) (x : UInt32Array) (y : UInt32Array.Slice)
    (hx : x.size = n + 1) (hy : y.size ≤ n + 1) : (subModI M x y).size = n + 1 := by
  have hMs := M.size_eq
  have has : (addInto x 0 M.arr).size = n + 1 := by
    rw [size_addInto _ _ _ (by simp [hx, hMs]), hx]
  simp only [subModI]
  split
  · rw [size_subInto _ _ _ (by rw [has]; lia), has]
  · rw [size_subInto _ _ _ (by lia), hx]

public theorem toNat_subModI {n : Nat} (M : FermatMod n) (x : UInt32Array) (y : UInt32Array.Slice)
    (hn : 1 ≤ n) (hx : x.size = n + 1) (hy : y.size ≤ n + 1) (hxF : toNat x < fermat n)
    (hyF : toNat y < fermat n) :
    toNat (subModI M x y) = (toNat x + fermat n - toNat y) % fermat n := by
  have h2 := two_fermat_lt n hn
  have hMs := M.size_eq
  have hF := M.toNat_eq
  by_cases h : toNat x < toNat y
  · have e : subModI M x y = subInto (addInto x 0 M.arr) 0 y := by
      have : lt x y = true := by rw [lt_iff]; exact h
      simp only [subModI, this, ↓reduceIte]
    have hlt : toNat x + 2 ^ (32 * 0) * toNat M.arr < 2 ^ (32 * x.size) := by
      rw [hx, hF]; simp only [Nat.mul_zero, Nat.pow_zero, Nat.one_mul]; lia
    have ha : toNat (addInto x 0 M.arr) = toNat x + fermat n := by
      rw [toNat_addInto_of_lt _ _ _ (by simp [hx, hMs]) hlt, hF]; simp
    have has : (addInto x 0 M.arr).size = n + 1 := by
      rw [size_addInto _ _ _ (by simp [hx, hMs]), hx]
    have hle : 2 ^ (32 * 0) * toNat y ≤ toNat (addInto x 0 M.arr) := by
      simp only [Nat.mul_zero, Nat.pow_zero, Nat.one_mul, ha]; lia
    rw [e, toNat_subInto_of_le _ _ _ (by rw [has]; lia) hle, ha]
    simp only [Nat.mul_zero, Nat.pow_zero, Nat.one_mul]
    rw [Nat.mod_eq_of_lt (by lia)]
  · have e : subModI M x y = subInto x 0 y := by
      have : lt x y = false := by rw [Bool.eq_false_iff, ne_eq, lt_iff]; exact h
      simp only [subModI, this, Bool.false_eq_true, ↓reduceIte]
    have hle : 2 ^ (32 * 0) * toNat y ≤ toNat x := by
      simp only [Nat.mul_zero, Nat.pow_zero, Nat.one_mul]; lia
    rw [e, toNat_subInto_of_le _ _ _ (by lia) hle]
    simp only [Nat.mul_zero, Nat.pow_zero, Nat.one_mul]
    rw [show toNat x + fermat n - toNat y = (toNat x - toNat y) + 1 * fermat n by lia,
      Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt (by lia)]

/-! ## Multiplication by a power of two, with fewer arrays -/

/--
`x 2^(32 w + b)` modulo `F`, negated when `neg`: `y = x 2ᵇ` by `mulRow`, then its low `n - w`
limbs `w` limbs up minus its top limbs, which are read in place; the other way round for the
negation.
-/
public def mulPow2Core {n : Nat} (M : FermatMod n) (x : UInt32Array) (w b : Nat) (neg : Bool) :
    UInt32Array :=
  let y := mulRow x (2 ^ b).toUInt32
  let A := addInto (.replicate (n + 1) 0) w (y.toSlice 0 (n - w))
  if neg then subModI M (copyPadded (y.toSlice (n - w) (n + 2)) (n + 1)) A
  else subModI M A (y.toSlice (n - w) (n + 2))

/-- `x 2ˢ` modulo `F`, by `mulPow2Core` with `32 w + b = s mod N` and the sign of `2^(s mod 2N)`. -/
public def mulPow2I {n : Nat} (M : FermatMod n) (x : UInt32Array) (s : Nat) : UInt32Array :=
  let t := s % (64 * n)
  if t = 0 then x
  else if t < 32 * n then mulPow2Core M x (t / 32) (t % 32) false
  else mulPow2Core M x ((t - 32 * n) / 32) ((t - 32 * n) % 32) true

public theorem size_mulPow2Core {n : Nat} (M : FermatMod n) (x : UInt32Array) (w b : Nat)
    (neg : Bool) (hw : w < n) (hx : x.size = n + 1) : (mulPow2Core M x w b neg).size = n + 1 := by
  have hA : (addInto (.replicate (n + 1) 0) w
      ((mulRow x (2 ^ b).toUInt32).toSlice 0 (n - w))).size = n + 1 := by
    rw [size_addInto _ _ _ (by simp; lia)]; simp
  simp only [mulPow2Core]
  split
  · exact size_subModI M _ _ (size_copyPadded _ _ (by simp [hx]; lia)) (by simp; lia)
  · exact size_subModI M _ _ hA (by simp [hx]; lia)

public theorem size_mulPow2I {n : Nat} (M : FermatMod n) (x : UInt32Array) (s : Nat)
    (hn : 1 ≤ n) (hx : x.size = n + 1) : (mulPow2I M x s).size = n + 1 := by
  have ht : s % (64 * n) < 64 * n := Nat.mod_lt _ (by lia)
  simp only [mulPow2I]
  split
  · exact hx
  split
  · exact size_mulPow2Core M _ _ _ _ (by lia) hx
  · exact size_mulPow2Core M _ _ _ _ (by lia) hx

private theorem rot_val (L H P Q R : Int) (h : Q * P = R) :
    P * L + (R + 1) - H - (L + Q * H) * P = (R + 1) * (1 - H) := by
  subst h; grind

private theorem rot_val_neg (L H P Q R : Int) (h : Q * P = R) :
    H + (R + 1) - P * L - (L + Q * H) * P * R = (R + 1) * (1 - P * L - (R - 1) * H) := by
  subst h; grind

public theorem toNat_mulPow2Core {n : Nat} (M : FermatMod n) (x : UInt32Array) (w b : Nat)
    (neg : Bool) (hn : 1 ≤ n) (hw : w < n) (hb : b < 32) (hx : x.size = n + 1)
    (hxF : toNat x < fermat n) :
    toNat (mulPow2Core M x w b neg) =
      (toNat x * 2 ^ (32 * w + b) * (if neg then 2 ^ (32 * n) else 1)) % fermat n := by
  have hb' : ((2 ^ b : Nat).toUInt32).toNat = 2 ^ b := by
    simp only [Nat.toUInt32_eq, UInt32.toNat_ofNat']
    exact Nat.mod_eq_of_lt (Nat.pow_lt_pow_right (by decide) hb)
  have e₀ : mulPow2Core M x w b false = subModI M (addInto (.replicate (n + 1) 0) w
      ((mulRow x (2 ^ b).toUInt32).toSlice 0 (n - w)))
      ((mulRow x (2 ^ b).toUInt32).toSlice (n - w) (n + 2)) := by
    simp only [mulPow2Core, Bool.false_eq_true, ↓reduceIte]
  have e₁ : mulPow2Core M x w b true = subModI M
      (copyPadded ((mulRow x (2 ^ b).toUInt32).toSlice (n - w) (n + 2)) (n + 1))
      (addInto (.replicate (n + 1) 0) w ((mulRow x (2 ^ b).toUInt32).toSlice 0 (n - w))) := by
    simp only [mulPow2Core, ↓reduceIte]
  -- `y = x 2ᵇ`, below `2ᴺ 2³²`.
  have hy : toNat (mulRow x (2 ^ b).toUInt32) = toNat x * 2 ^ b := by rw [toNat_mulRow, hb']
  have hys : (mulRow x (2 ^ b).toUInt32).size = n + 2 := by simp [hx]
  have hylt : toNat x * 2 ^ b < 2 ^ (32 * n) * 2 ^ 32 := by
    have hP : 2 ^ b ≤ 2 ^ 31 := Nat.pow_le_pow_right (by decide) (by lia)
    simp only [fermat] at hxF
    have := Nat.mul_le_mul (show toNat x ≤ 2 ^ (32 * n) by lia) hP
    have : 2 ^ (32 * n) * 2 ^ 31 < 2 ^ (32 * n) * 2 ^ 32 :=
      Nat.mul_lt_mul_of_pos_left (by decide) (Nat.two_pow_pos _)
    lia
  generalize mulRow x (2 ^ b).toUInt32 = y at e₀ e₁ hy hys
  have hsplit := toNat_split y (n - w) (by lia)
  have hLlt : toNat (y.toSlice 0 (n - w)) < 2 ^ (32 * (n - w)) := by
    have := toNat_lt (y.toSlice 0 (n - w))
    simpa [show min (n - w) y.size = n - w by lia] using this
  have hpow : 2 ^ (32 * n) = 2 ^ (32 * (n - w)) * 2 ^ (32 * w) := by
    rw [← Nat.pow_add]; congr 1; lia
  -- The top limbs are below `2^(32 (w + 1)) ≤ 2ᴺ`.
  have hH : toNat (y.toSlice (n - w) y.size) < 2 ^ (32 * n) := by
    have h₁ : 2 ^ (32 * (n - w)) * toNat (y.toSlice (n - w) y.size) <
        2 ^ (32 * (n - w)) * (2 ^ (32 * w) * 2 ^ 32) := by
      rw [← Nat.mul_assoc, ← hpow]; lia
    have h₂ := Nat.lt_of_mul_lt_mul_left h₁
    have h₃ : 2 ^ (32 * w) * 2 ^ 32 ≤ 2 ^ (32 * n) := by
      rw [← Nat.pow_add]; exact Nat.pow_le_pow_right (by decide) (by lia)
    lia
  have hHs : toNat (y.toSlice (n - w) (n + 2)) = toNat (y.toSlice (n - w) y.size) := by
    rw [hys]
  -- The low limbs, moved up by `w` limbs.
  have hz := toNat_zeros (n + 1)
  have hz' : toNat ((UInt32Array.replicate (n + 1) 0).toSlice 0 (n + 1)) = 0 := by
    simpa using hz
  have hAlt : 2 ^ (32 * w) * toNat (y.toSlice 0 (n - w)) < 2 ^ (32 * n) := by
    rw [hpow, Nat.mul_comm (2 ^ (32 * (n - w)))]
    exact Nat.mul_lt_mul_of_pos_left hLlt (Nat.two_pow_pos _)
  have hA : toNat (addInto (.replicate (n + 1) 0) w (y.toSlice 0 (n - w))) =
      2 ^ (32 * w) * toNat (y.toSlice 0 (n - w)) := by
    have hle : 2 ^ (32 * n) ≤ 2 ^ (32 * (n + 1)) := Nat.pow_le_pow_right (by decide) (by lia)
    have hfit : w + (y.toSlice 0 (n - w)).size ≤ (UInt32Array.replicate (n + 1) 0).size := by
      simp; lia
    have hlt : toNat (UInt32Array.replicate (n + 1) 0) + 2 ^ (32 * w) *
        toNat (y.toSlice 0 (n - w)) < 2 ^ (32 * (UInt32Array.replicate (n + 1) 0).size) := by
      simp only [UInt32Array.size_replicate, hz']; lia
    rw [toNat_addInto_of_lt _ _ _ hfit hlt]
    simp_all
  have hAs : (addInto (.replicate (n + 1) 0) w (y.toSlice 0 (n - w))).size = n + 1 := by
    rw [size_addInto _ _ _ (by simp; lia)]; simp
  have hx2 : toNat x * 2 ^ (32 * w + b) = toNat y * 2 ^ (32 * w) := by
    rw [Nat.pow_add, hy, Nat.mul_comm (2 ^ (32 * w)), Nat.mul_assoc]
  have hPQ : ((2 ^ (32 * (n - w)) : Nat) : Int) * ((2 ^ (32 * w) : Nat) : Int) =
      ((2 ^ (32 * n) : Nat) : Int) := by rw [← Int.natCast_mul, ← hpow]
  generalize toNat (y.toSlice 0 (n - w)) = L at *
  generalize toNat (y.toSlice (n - w) y.size) = H at *
  cases neg
  · rw [e₀]
    simp only [Bool.false_eq_true, ↓reduceIte, Nat.mul_one]
    rw [toNat_subModI M _ _ hn hAs (by simp; lia) (by rw [hA]; simp only [fermat]; lia)
      (by rw [hHs]; simp only [fermat]; lia), hA, hHs, hx2, hsplit]
    apply FFT.mod_eq_iff_dvd.2
    -- `(L + Q H) P - (P L + F - H) = (H - 1) F` with `P Q = 2ᴺ`, `F = 2ᴺ + 1`.
    refine ⟨1 - (H : Int), ?_⟩
    rw [Int.ofNat_sub (by simp only [fermat]; lia)]
    simp only [fermat]
    push_cast at hPQ ⊢
    exact rot_val _ _ _ _ _ hPQ
  · rw [e₁]
    simp only [↓reduceIte]
    have hcp : toNat (copyPadded (y.toSlice (n - w) (n + 2)) (n + 1)) = H := by
      rw [toNat_copyPadded, hHs]
    rw [toNat_subModI M _ _ hn (size_copyPadded _ _ (by simp; lia)) (by simp [hAs])
      (by rw [hcp]; simp only [fermat]; lia) (by rw [hA]; simp only [fermat]; lia), hcp, hA,
      hx2, hsplit]
    apply FFT.mod_eq_iff_dvd.2
    -- `(L + Q H) P 2ᴺ - (H + F - P L) = (P L + (2ᴺ - 1) H - 1) F`.
    refine ⟨1 - ((2 ^ (32 * w) : Nat) : Int) * L - (((2 ^ (32 * n) : Nat) : Int) - 1) * H, ?_⟩
    rw [Int.ofNat_sub (by simp only [fermat]; lia)]
    simp only [fermat]
    push_cast at hPQ ⊢
    exact rot_val_neg _ _ _ _ _ hPQ

public theorem toNat_mulPow2I {n : Nat} (M : FermatMod n) (x : UInt32Array) (s : Nat)
    (hn : 1 ≤ n) (hx : x.size = n + 1) (hxF : toNat x < fermat n) :
    toNat (mulPow2I M x s) = (toNat x * 2 ^ s) % fermat n := by
  have hq : (2 ^ s) % fermat n = (2 ^ (s % (64 * n))) % fermat n := by
    have hA : ((2 ^ (64 * n)) ^ (s / (64 * n))) % fermat n = 1 % fermat n := by
      rw [Nat.pow_mod, two_pow_period, ← Nat.pow_mod, Nat.one_pow]
    conv => lhs; rw [← Nat.div_add_mod s (64 * n), Nat.pow_add, Nat.pow_mul]
    rw [Nat.mul_mod, hA, ← Nat.mul_mod, Nat.one_mul]
  have hs : (toNat x * 2 ^ s) % fermat n = (toNat x * 2 ^ (s % (64 * n))) % fermat n := by
    rw [Nat.mul_mod, hq, ← Nat.mul_mod]
  rw [hs]
  have ht : s % (64 * n) < 64 * n := Nat.mod_lt _ (by lia)
  by_cases h0 : s % (64 * n) = 0
  · have e : mulPow2I M x s = x := by simp only [mulPow2I, h0, ↓reduceIte]
    rw [e, h0, Nat.pow_zero, Nat.mul_one, Nat.mod_eq_of_lt hxF]
  by_cases h : s % (64 * n) < 32 * n
  · have e : mulPow2I M x s = mulPow2Core M x (s % (64 * n) / 32) (s % (64 * n) % 32) false := by
      simp only [mulPow2I, h0, h, ↓reduceIte]
    rw [e, toNat_mulPow2Core M _ _ _ _ hn (by lia) (Nat.mod_lt _ (by decide)) hx hxF]
    simp only [Bool.false_eq_true, ↓reduceIte, Nat.mul_one, Nat.div_add_mod]
  · have e : mulPow2I M x s = mulPow2Core M x ((s % (64 * n) - 32 * n) / 32)
        ((s % (64 * n) - 32 * n) % 32) true := by
      simp only [mulPow2I, h0, h, ↓reduceIte]
    rw [e, toNat_mulPow2Core M _ _ _ _ hn (by lia) (Nat.mod_lt _ (by decide)) hx hxF]
    simp only [↓reduceIte, Nat.div_add_mod]
    rw [Nat.mul_assoc, ← Nat.pow_add, show s % (64 * n) - 32 * n + 32 * n = s % (64 * n) by lia]

public theorem toNat_mulPow2I_lt {n : Nat} (M : FermatMod n) (x : UInt32Array) (s : Nat)
    (hn : 1 ≤ n) (hx : x.size = n + 1) (hxF : toNat x < fermat n) :
    toNat (mulPow2I M x s) < fermat n := by
  rw [toNat_mulPow2I M x s hn hx hxF]
  exact Nat.mod_lt _ (by simp [fermat])

end MPN.Fermat
