/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import MPN32.Mul.Limb
public import MPN.Shift
public import MPN.Bitwise
public import MPN32.Basic

/-!
# Shifts and bits

* `shiftLeft a n` is `a * 2ⁿ`: the limbs of `a` shifted left by `n % 32` bits into fresh limbs
  above `n / 32` zero limbs, by `main`'s `WordArray.lshiftW` (or `copyW` for whole limbs), which
  reads `a` where it is.
* `shiftRight a n` is `a / 2ⁿ`: the limbs of `a` from `n / 32` on shifted right by `n % 32` bits
  into fresh limbs, by `WordArray.rshiftW` (or `copyW`).
* `shrLimbs`, a right shift in place from the top limb down, divides the interpolation values of
  the Toom methods by powers of 2 and is the exact division by 2, 4 and 8.
* `land`, `lor` and `xor` of arrays, limb by limb, by `main`'s `WordArray.bitW`.

Both results are trimmed.
-/

open ScalarArray

namespace MPN.W32

/-! ## Moving limbs -/

/-- The limbs of `a` from `k` on hold `⌊a / βᵏ⌋`. -/
public theorem toNat_slice_from (a : UInt32Array.Slice) (k : Nat) (hk : k ≤ a.size) :
    toNat (a.slice k a.size) = toNat a / 2 ^ (32 * k) := by
  have h := toNat_slice_add_toNat_slice a k hk
  have hlt := toNat_lt (a.slice 0 k)
  simp only [UInt32Array.Slice.size_slice] at hlt
  rw [show min k a.size - 0 = k by lia] at hlt
  rw [← h, Nat.mul_comm (2 ^ _), Nat.add_mul_div_right _ _ (Nat.two_pow_pos _),
    Nat.div_eq_of_lt hlt, Nat.zero_add]

public theorem toNat_pow_limb (s : Nat) (hs : s < 32) :
    ((1 : UInt32) <<< s.toUInt32).toNat = 2 ^ s := by
  rw [UInt32.toNat_shiftLeft]
  simp only [UInt32.toNat_one, Nat.toUInt32, UInt32.toNat_ofNat', Nat.one_shiftLeft]
  rw [Nat.mod_eq_of_lt (show s < 2 ^ 32 by lia), Nat.mod_eq_of_lt hs,
    Nat.mod_eq_of_lt (Nat.pow_lt_pow_right (by decide) hs)]

/-! ## Shifts -/

/--
Limb `v` shifted left by `s < 32` bits, plus the carry `c < 2^s`; the bits above go up. The carry
out depends on `v` only, not on `c`, which keeps the loop free of a dependency chain: `c` lands in
the `s` low bits, which the shift leaves zero, so the sum doesn't wrap.
-/
@[inline] public def shlStep (s : UInt64) (v c : UInt32) : UInt32 × UInt32 :=
  let w := v.toUInt64 <<< s
  (w.toUInt32 + c, (w >>> 32).toUInt32)

public theorem shlStep_spec (s : Nat) (hs : s < 32) (v c : UInt32) (hc : c.toNat < 2 ^ s) :
    (shlStep s.toUInt64 v c).1.toNat + 2 ^ 32 * (shlStep s.toUInt64 v c).2.toNat =
      v.toNat * 2 ^ s + c.toNat ∧ (shlStep s.toUInt64 v c).2.toNat < 2 ^ s := by
  have hv := v.toNat_lt
  have hs' : s.toUInt64.toNat = s := by
    simp only [Nat.toUInt64, UInt64.toNat_ofNat']
    exact Nat.mod_eq_of_lt (by lia)
  have hQ : (2 : Nat) ^ 32 = 2 ^ s * 2 ^ (32 - s) := by
    rw [← Nat.pow_add]; congr 1; lia
  have hlt : v.toNat * 2 ^ s < 2 ^ 32 * 2 ^ s := Nat.mul_lt_mul_of_pos_right hv (Nat.two_pow_pos _)
  have h64 : 2 ^ 32 * 2 ^ s ≤ 2 ^ 64 := by
    rw [← Nat.pow_add]; exact Nat.pow_le_pow_right (by decide) (by lia)
  have hw : (v.toUInt64 <<< s.toUInt64).toNat = v.toNat * 2 ^ s := by
    rw [UInt64.toNat_shiftLeft, hs', Nat.mod_eq_of_lt (show s < 64 by lia),
      UInt32.toNat_toUInt64, Nat.shiftLeft_eq, Nat.mod_eq_of_lt (by lia)]
  -- The low limb of `v 2^s` is a multiple of `2^s`, so adding `c < 2^s` stays below `β`.
  have hlow : v.toNat * 2 ^ s % 2 ^ 32 + c.toNat < 2 ^ 32 := by
    rw [hQ, Nat.mul_comm v.toNat, Nat.mul_mod_mul_left]
    have hm := Nat.mod_lt v.toNat (Nat.two_pow_pos (32 - s))
    have := Nat.mul_le_mul_left (2 ^ s) (show v.toNat % 2 ^ (32 - s) + 1 ≤ 2 ^ (32 - s) by lia)
    rw [Nat.mul_succ] at this
    lia
  have hq : v.toNat * 2 ^ s / 2 ^ 32 < 2 ^ s := by
    rw [Nat.div_lt_iff_lt_mul (by decide)]; exact Nat.lt_of_lt_of_eq hlt (Nat.mul_comm _ _)
  simp only [shlStep, UInt32.toNat_add, UInt64.toNat_toUInt32, UInt64.toNat_shiftRight, hw,
    UInt64.reduceToNat, Nat.shiftRight_eq_div_pow, Nat.reduceMod]
  rw [Nat.mod_eq_of_lt (show v.toNat * 2 ^ s / 2 ^ 32 < 2 ^ 32 by lia), Nat.mod_eq_of_lt hlow]
  refine ⟨?_, hq⟩
  have := Nat.mod_add_div (v.toNat * 2 ^ s) (2 ^ 32)
  lia

/-- Limb `v` shifted right by `s < 32` bits, with the `s` low bits of the limb `c` above it. -/
@[inline] def shrStep (s : UInt64) (v c : UInt32) : UInt32 × UInt32 :=
  (((c.toUInt64 * 4294967296 + v.toUInt64) >>> s).toUInt32, v)

private theorem toNat_shrStep (s : Nat) (hs : s < 32) (v c : UInt32) :
    (shrStep s.toUInt64 v c).1.toNat = (c.toNat * 2 ^ 32 + v.toNat) / 2 ^ s % 2 ^ 32 := by
  have hv := v.toNat_lt
  have hc := c.toNat_lt
  have ht : (c.toUInt64 * 4294967296 + v.toUInt64).toNat = c.toNat * 2 ^ 32 + v.toNat := by
    simp only [UInt64.toNat_add, UInt64.toNat_mul, UInt32.toNat_toUInt64, UInt64.reduceToNat]
    lia
  have hs' : s.toUInt64.toNat = s := by
    simp only [Nat.toUInt64, UInt64.toNat_ofNat']
    exact Nat.mod_eq_of_lt (by lia)
  simp only [shrStep, UInt64.toNat_toUInt32, UInt64.toNat_shiftRight, ht, hs',
    Nat.shiftRight_eq_div_pow, Nat.mod_eq_of_lt (show s < 64 by lia)]

/--
One limb of a right shift: `(D % β · β + v) / P % β` and `β ⌊D / P⌋` make `⌊(v + β D) / P⌋` when
`P` divides `β`.
-/
private theorem shr_arith (v D P Q : Nat) (hP : 0 < P) (hv : v < P * Q) :
    ((D % (P * Q)) * (P * Q) + v) / P % (P * Q) + (P * Q) * (D / P) = (v + (P * Q) * D) / P := by
  have hB0 : 0 < P * Q := by lia
  have h1 : (v + P * Q * D) / (P * Q) = D := by
    rw [Nat.add_mul_div_left _ _ hB0, Nat.div_eq_of_lt hv, Nat.zero_add]
  have h2 : (v + P * Q * D) / P / (P * Q) = D / P := by
    rw [Nat.div_div_eq_div_mul, Nat.mul_comm P (P * Q), ← Nat.div_div_eq_div_mul, h1]
  have h3 : (v + P * Q * D) / P % (P * Q) = ((D % (P * Q)) * (P * Q) + v) / P % (P * Q) := by
    have hD := Nat.div_add_mod D (P * Q)
    have e : v + P * Q * D = ((D % (P * Q)) * (P * Q) + v) + P * (Q * (P * Q) * (D / (P * Q))) := by
      conv => lhs; rw [← hD]
      grind
    rw [e, Nat.add_mul_div_left _ _ hP,
      show Q * (P * Q) * (D / (P * Q)) = (P * Q) * (Q * (D / (P * Q))) by grind,
      Nat.add_mul_mod_self_left]
  rw [← h3, ← h2, Nat.mod_add_div]

/--
The loop of `foldrInPlace` with `shrStep`: below index `k` the limbs of `x` are untouched, from `k`
on they hold `⌊x' / 2^s⌋` for the limbs `x'` of `x` from `k` on, and the carry is limb `k`.
-/
private theorem shr_loop (sh : Nat) (hsh : sh < 32) (x : UInt32Array) (n : Nat)
    (r : UInt32Array.Slice) (hs : r.size = n) (k : Nat) (hk : k ≤ n) (c : UInt32)
    (h0 : r.start = 0) (hlow : ∀ i, i < k → r.array[i]! = x[i]!)
    (hW : r.array.valAt k (n - k) = x.valAt k (n - k) / 2 ^ sh)
    (hc : c.toNat = x.valAt k (n - k) % 2 ^ 32) :
    (UInt32Array.Slice.foldrInPlace.loop n (fun _ _ v c => shrStep sh.toUInt64 v c) r hs
      k hk c).1.array.valAt 0 n = x.valAt 0 n / 2 ^ sh := by
  induction k generalizing r c with
  | zero =>
    rw [UInt32Array.Slice.foldrInPlace.loop]
    simpa using hW
  | succ k ih =>
    rw [UInt32Array.Slice.foldrInPlace.loop]
    have hrk : r[k]'(by lia) = x[k]! := by
      rw [UInt32Array.Slice.getElem_eq_getElem!, h0, Nat.zero_add, hlow k (by lia)]
    have hX := UInt32Array.valAt_succ x k (n - (k + 1))
    have e : n - k = n - (k + 1) + 1 := by lia
    refine ih _ _ _ _ ?_ ?_ ?_ ?_
    · rw [UInt32Array.Slice.start_set, h0]
    · intro i hi
      rw [UInt32Array.Slice.array_set, UInt32Array.getElem!_set, ite_eq_right (by lia),
        hlow i (by lia)]
    · rw [UInt32Array.Slice.array_set, e, UInt32Array.valAt_succ, UInt32Array.getElem!_set,
        ite_eq_left (by lia), hX]
      rw [UInt32Array.valAt_congr (b := r.array) _ fun i hi _ => by
        rw [UInt32Array.getElem!_set, ite_eq_right (by lia)]]
      rw [hW, toNat_shrStep sh hsh, hc, hrk]
      have hP : (2 : Nat) ^ 32 = 2 ^ sh * 2 ^ (32 - sh) := by
        rw [← Nat.pow_add]; congr 1; lia
      rw [hP]
      exact shr_arith _ _ _ _ (Nat.two_pow_pos _) (by rw [← hP]; exact x[k]!.toNat_lt)
    · show (r[k]'(by lia)).toNat = _
      rw [hrk, e, hX, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt x[k]!.toNat_lt]

/--
Shifts the limbs of `x` right by `s < 32` bits in place, from the top limb down, with the low bits
of each limb carried into the one below, and trims. The shift is an argument so that the loop
doesn't recompute it.
-/
public def shrLimbs (x : UInt32Array) (s : UInt64) : UInt32Array :=
  x.toSlice.foldrInPlaceThen (0 : UInt32) (fun _ _ v c => shrStep s v c) (fun r _ => trim r.array)

public theorem size_shrLimbs_le (x : UInt32Array) (s : UInt64) : (shrLimbs x s).size ≤ x.size := by
  rw [shrLimbs, UInt32Array.Slice.foldrInPlaceThen_eq]
  exact Nat.le_trans (size_trim_le _) (by simp)

@[simp] public theorem toNat_shrLimbs (x : UInt32Array) (s : Nat) (hs : s < 32) :
    toNat (shrLimbs x s.toUInt64) = toNat x / 2 ^ s := by
  rw [shrLimbs]
  simp only [UInt32Array.Slice.foldrInPlaceThen_eq]
  rw [toNat_trim, toNat_array_eq_valAt, toNat_array_eq_valAt,
    UInt32Array.Slice.size_array_foldrInPlace, show x.toSlice.array.size = x.toSlice.size by simp]
  conv => rhs; rw [show x.size = x.toSlice.size by simp]
  exact shr_loop s hs x _ _ rfl _ (Nat.le_refl _) 0 (by simp) (fun _ _ => by simp) (by simp)
    (by simp)

/-! ## Shifts of slices

`main`'s `WordArray.lshiftW`, `rshiftW` and `copyW` from the limbs of a slice into fresh limbs,
which read the slice where it is instead of copying it first.
-/

private theorem get_zeros (n i : Nat) : LimbArray.get (UInt32Array.replicate n 0) i = 0 := by
  show (UInt32Array.replicate n 0)[i]! = 0
  by_cases h : i < n
  · rw [getElem!_pos _ _ (by simpa using h)]; simp
  · rw [getElem!_neg _ _ (by simpa using h)]; rfl

private theorem valAt_zeros (n lo k : Nat) :
    LimbArray.valAt (UInt32Array.replicate n 0) lo k = 0 :=
  LimbArray.valAt_eq_zero _ fun i _ _ => by rw [get_zeros]; rfl

private theorem shl_bound (a : UInt32Array.Slice) (q : Nat)
    (h : q + a.size + 1 < USize.size ∧ a.start + a.size < USize.size) :
    WordArray.LoopBound (UInt32Array.replicate (q + a.size + 1) 0) q.toUSize a.size.toUSize ∧
      WordArray.LoopBound a.array a.start.toUSize a.size.toUSize := by
  have := a.stop_le_array_size
  have := a.size_eq
  have := a.start_le_stop
  simp only [WordArray.LoopBound, toNat_toUSize (show q < USize.size by lia),
    toNat_toUSize (show a.size < USize.size by lia), toNat_toUSize (show a.start < USize.size by lia)]
  exact ⟨⟨by show _ ≤ (UInt32Array.replicate _ 0).size; simp, by lia⟩, ⟨by
    show _ ≤ a.array.size; lia, by lia⟩⟩

private theorem top_bound (a : UInt32Array.Slice) (q : Nat) (x : UInt32Array)
    (hx : x.size = q + a.size + 1) (h : q + a.size + 1 < USize.size) :
    (q + a.size).toUSize.toNat < x.size := by
  rw [toNat_toUSize (by lia), hx]; lia

/--
`a 2ⁿ`, untrimmed, in `n / 32 + a.size + 1` limbs: the limbs of `a` shifted left by `n % 32` bits
above `n / 32` zero limbs (`WordArray.lshiftW`, or `copyW` for whole limbs), with the bits out on
top; on `Nat` were the sizes not `USize`s, which never happens.
-/
def shlRaw (a : UInt32Array.Slice) (n : Nat) : UInt32Array :=
  let q := n / 32
  if h' : q + a.size + 1 < 4294967295 ∧ a.start + a.size < 4294967295 then
    have h : q + a.size + 1 < USize.size ∧ a.start + a.size < USize.size :=
      ⟨lt_usizeSize h'.1, lt_usizeSize h'.2⟩
    let r := UInt32Array.replicate (q + a.size + 1) 0
    if n % 32 = 0 then
      WordArray.copyW r q.toUSize a.array a.start.toUSize a.size.toUSize (shl_bound a q h).1
        (shl_bound a q h).2
    else
      let p := WordArray.lshiftW r q.toUSize a.array a.start.toUSize a.size.toUSize
        (n % 32).toUInt32 (shl_bound a q h).1 (shl_bound a q h).2
      p.1.uset (q + a.size).toUSize p.2 (top_bound a q p.1 (by
        rw [show p.1.size = LimbArray.size p.1 from rfl, WordArray.size_lshiftW]
        exact UInt32Array.size_replicate ..) h.1)
  else ofNat (toNat a * 2 ^ n)

/-- `a 2ⁿ`, trimmed (`shlRaw`). -/
public def shiftLeft (a : UInt32Array.Slice) (n : Nat) : UInt32Array := trim (shlRaw a n)

private theorem valAt_shlSplit (x : UInt32Array) (q m : Nat)
    (hz : ∀ i, i < q → LimbArray.get x i = 0) :
    LimbArray.valAt x 0 (q + m + 1) =
      2 ^ (32 * q) * (LimbArray.valAt x q m + 2 ^ (32 * m) * (LimbArray.get x (q + m)).toNat) := by
  rw [LimbArray.valAt_add x 0 (q + m) 1, LimbArray.valAt_add x 0 q m, LimbArray.valAt_one,
    LimbArray.valAt_eq_zero q (fun i _ hi => by rw [hz i (by lia)]; rfl)]
  simp only [Nat.zero_add, show LimbArray.w UInt32Array = 32 from rfl]
  rw [Nat.mul_add 32 q m, Nat.pow_add, Nat.mul_add, Nat.mul_assoc]
  rfl

/-- The limbs of a left shift with the bits out stored on top. -/
private theorem shl_fin (q m s : Nat) (p : UInt32Array × UInt32) (A : Nat)
    (hsz : LimbArray.size p.1 = q + m + 1)
    (e₂ : ∀ i, (i < q ∨ q + m ≤ i) → LimbArray.get p.1 i = 0)
    (e₃ : LimbArray.valAt p.1 q m + 2 ^ (32 * m) * p.2.toNat = A * 2 ^ s)
    (hti : (q + m).toUSize.toNat = q + m) (hb : (q + m).toUSize.toNat < p.1.size) :
    LimbArray.size (p.1.uset (q + m).toUSize p.2 hb) = q + m + 1 ∧
      LimbArray.valAt (p.1.uset (q + m).toUSize p.2 hb) 0 (q + m + 1) = 2 ^ (32 * q) * (A * 2 ^ s) := by
  refine ⟨by show (UInt32Array.uset _ _ _ _).size = _; rw [UInt32Array.size_uset]; exact hsz, ?_⟩
  have hg : ∀ i, LimbArray.get (p.1.uset (q + m).toUSize p.2 hb) i =
      if q + m = i then p.2 else LimbArray.get p.1 i := fun i => by
    show (UInt32Array.uset _ _ _ _)[i]! = _
    rw [UInt32Array.getElem!_uset, hti]
    rfl
  have hz : ∀ i, i < q → LimbArray.get (p.1.uset (q + m).toUSize p.2 hb) i = 0 := fun i hi => by
    rw [hg]
    simp only [show ¬(q + m = i) by lia, ↓reduceIte]
    exact e₂ i (by lia)
  have hv : LimbArray.valAt (p.1.uset (q + m).toUSize p.2 hb) q m = LimbArray.valAt p.1 q m :=
    LimbArray.valAt_congr m fun i _ hi => by
      rw [hg]; simp only [show ¬(q + m = i) by lia, ↓reduceIte]
  rw [valAt_shlSplit _ q m hz, hv]
  have ht : LimbArray.get (p.1.uset (q + m).toUSize p.2 hb) (q + m) = p.2 := by
    rw [hg]; simp
  rw [ht, e₃]

private theorem valAt_shlRaw (a : UInt32Array.Slice) (n : Nat)
    (h' : n / 32 + a.size + 1 < 4294967295 ∧ a.start + a.size < 4294967295) :
    LimbArray.size (shlRaw a n) = n / 32 + a.size + 1 ∧
      LimbArray.valAt (shlRaw a n) 0 (n / 32 + a.size + 1) = toNat a * 2 ^ n := by
  have h : n / 32 + a.size + 1 < USize.size ∧ a.start + a.size < USize.size :=
    ⟨lt_usizeSize h'.1, lt_usizeSize h'.2⟩
  have hn : 2 ^ n = 2 ^ (32 * (n / 32)) * 2 ^ (n % 32) := by
    rw [← Nat.pow_add]; congr 1; lia
  have hA : toNat a = LimbArray.valAt a.array a.start a.size := toNat_eq_valAt a
  have hq := toNat_toUSize (show n / 32 < USize.size by lia)
  have hm := toNat_toUSize (show a.size < USize.size by lia)
  have hst := toNat_toUSize (show a.start < USize.size by lia)
  have hzs : LimbArray.size (UInt32Array.replicate (n / 32 + a.size + 1) 0) =
      n / 32 + a.size + 1 := UInt32Array.size_replicate ..
  by_cases h0 : n % 32 = 0
  · have e : shlRaw a n = WordArray.copyW (UInt32Array.replicate (n / 32 + a.size + 1) 0)
        (n / 32).toUSize a.array a.start.toUSize a.size.toUSize (shl_bound a _ h).1
        (shl_bound a _ h).2 := by
      simp only [shlRaw, h', h0, and_self, ↓reduceDIte, ↓reduceIte]
    rw [e]
    obtain ⟨e₁, e₂, e₃⟩ := WordArray.copyW_spec (UInt32Array.replicate (n / 32 + a.size + 1) 0)
      (n / 32).toUSize a.array a.start.toUSize a.size.toUSize (shl_bound a _ h).1
      (shl_bound a _ h).2
    simp only [hq, hm, hst] at e₂ e₃
    refine ⟨by rw [e₁, hzs], ?_⟩
    rw [valAt_shlSplit _ (n / 32) a.size (fun i hi => by rw [e₂ i (by lia), get_zeros]), e₃,
      e₂ _ (by lia), get_zeros, ← hA, hn, h0]
    simp [Nat.mul_comm]
  · have hs32 : (n % 32).toUInt32.toNat = n % 32 := by
      simp only [Nat.toUInt32, UInt32.toNat_ofNat']
      exact Nat.mod_eq_of_lt (by have := Nat.mod_lt n (show 32 > 0 by decide); lia)
    have hti := toNat_toUSize (show n / 32 + a.size < USize.size by lia)
    obtain ⟨e₁, e₂, e₃⟩ := WordArray.lshiftW_spec (UInt32Array.replicate (n / 32 + a.size + 1) 0)
      (n / 32).toUSize a.array a.start.toUSize a.size.toUSize (n % 32).toUInt32
      (shl_bound a _ h).1 (shl_bound a _ h).2 (by show 0 < (n % 32).toUInt32.toNat; lia)
      (by show (n % 32).toUInt32.toNat < 32; rw [hs32]; exact Nat.mod_lt _ (by decide))
    simp only [hq, hm, hst] at e₂ e₃
    change LimbArray.valAt _ (n / 32) a.size + 2 ^ (32 * a.size) * UInt32.toNat _ =
      LimbArray.valAt a.array a.start a.size * 2 ^ (n % 32).toUInt32.toNat at e₃
    rw [hs32, ← hA] at e₃
    have hb : (n / 32 + a.size).toUSize.toNat < (WordArray.lshiftW
        (UInt32Array.replicate (n / 32 + a.size + 1) 0) (n / 32).toUSize a.array a.start.toUSize
        a.size.toUSize (n % 32).toUInt32 (shl_bound a _ h).1 (shl_bound a _ h).2).1.size := by
      rw [hti]
      change _ < LimbArray.size (A := UInt32Array) _
      rw [e₁, hzs]
      lia
    have e : shlRaw a n = (WordArray.lshiftW (UInt32Array.replicate (n / 32 + a.size + 1) 0)
        (n / 32).toUSize a.array a.start.toUSize a.size.toUSize (n % 32).toUInt32
        (shl_bound a _ h).1 (shl_bound a _ h).2).1.uset (n / 32 + a.size).toUSize
        (WordArray.lshiftW (UInt32Array.replicate (n / 32 + a.size + 1) 0)
        (n / 32).toUSize a.array a.start.toUSize a.size.toUSize (n % 32).toUInt32
        (shl_bound a _ h).1 (shl_bound a _ h).2).2 hb := by
      simp only [shlRaw, h', h0, and_self, ↓reduceDIte, ↓reduceIte]
    rw [e]
    have := shl_fin (n / 32) a.size (n % 32) _ (toNat a) (e₁.trans hzs)
      (fun i hi => (e₂ i hi).trans (get_zeros _ _)) e₃ hti hb
    rw [hn, ← Nat.mul_assoc, Nat.mul_comm (toNat a), Nat.mul_assoc]
    exact this

@[simp] public theorem toNat_shiftLeft (a : UInt32Array.Slice) (n : Nat) :
    toNat (shiftLeft a n) = toNat a * 2 ^ n := by
  rw [shiftLeft, toNat_trim]
  by_cases h : n / 32 + a.size + 1 < 4294967295 ∧ a.start + a.size < 4294967295
  · obtain ⟨e₁, e₂⟩ := valAt_shlRaw a n h
    rw [toNat_array_eq_valAt, show (shlRaw a n).size = LimbArray.size (shlRaw a n) from rfl, e₁]
    exact e₂
  · have e : shlRaw a n = ofNat (toNat a * 2 ^ n) := by simp only [shlRaw, h, ↓reduceDIte]
    rw [e, toNat_ofNat]

public theorem isTrimmed_shiftLeft (a : UInt32Array.Slice) (n : Nat) :
    isTrimmed (shiftLeft a n) = true := isTrimmed_trim _

/-- The value of the limbs of a slice from `q` on: its value over `2^(32 q)`. -/
private theorem valAt_from_div (a : UInt32Array.Slice) (q : Nat) (hq : q ≤ a.size) :
    LimbArray.valAt a.array (a.start + q) (a.size - q) = toNat a / 2 ^ (32 * q) := by
  rw [toNat_eq_valAt]
  show _ = LimbArray.valAt a.array a.start a.size / _
  rw [show a.size = q + (a.size - q) by lia, LimbArray.valAt_add,
    show LimbArray.w UInt32Array = 32 from rfl, Nat.add_mul_div_left _ _ (Nat.two_pow_pos _),
    Nat.div_eq_of_lt (by
      have := LimbArray.valAt_lt a.array a.start q
      rwa [show LimbArray.w UInt32Array = 32 from rfl] at this),
    Nat.zero_add, show q + (a.size - q) - q = a.size - q by lia]

private theorem shr_bound (a : UInt32Array.Slice) (q : Nat) (hq : q < a.size)
    (h : a.start + a.size < USize.size) :
    WordArray.LoopBound (UInt32Array.replicate (a.size - q) 0) 0 (a.size - q).toUSize ∧
      WordArray.LoopBound a.array (a.start + q).toUSize (a.size - q).toUSize ∧
      (0 : USize) < (a.size - q).toUSize := by
  have := a.stop_le_array_size
  have := a.size_eq
  have := a.start_le_stop
  have e₁ := toNat_toUSize (show a.size - q < USize.size by lia)
  have e₂ := toNat_toUSize (show a.start + q < USize.size by lia)
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ?_⟩
  · show (0 : USize).toNat + _ ≤ (UInt32Array.replicate _ 0).size; simp [e₁]
  · simp [e₁]; lia
  · show _ ≤ a.array.size; rw [e₁, e₂]; lia
  · rw [e₁, e₂]; lia
  · rw [USize.lt_iff_toNat_lt, e₁]; simp; lia

/--
`a / 2ⁿ`, trimmed: the limbs of `a` from `n / 32` on shifted right by `n % 32` bits into fresh limbs
(`WordArray.rshiftW`, or `copyW` for whole limbs); on `Nat` were the sizes not `USize`s, which
never happens.
-/
public def shiftRight (a : UInt32Array.Slice) (n : Nat) : UInt32Array :=
  if hq : n / 32 < a.size then
    if h' : a.start + a.size < 4294967295 then
      let r := UInt32Array.replicate (a.size - n / 32) 0
      let b := shr_bound a (n / 32) hq (lt_usizeSize h')
      if n % 32 = 0 then
        trim (WordArray.copyW r 0 a.array (a.start + n / 32).toUSize (a.size - n / 32).toUSize b.1
          b.2.1)
      else
        trim (WordArray.rshiftW r 0 a.array (a.start + n / 32).toUSize (a.size - n / 32).toUSize
          (n % 32).toUInt32 b.1 b.2.1 b.2.2).1
    else trim (ofNat (toNat a / 2 ^ n))
  else .empty

@[simp] public theorem toNat_shiftRight (a : UInt32Array.Slice) (n : Nat) :
    toNat (shiftRight a n) = toNat a / 2 ^ n := by
  have hA := toNat_lt a
  have hn : 2 ^ n = 2 ^ (32 * (n / 32)) * 2 ^ (n % 32) := by
    rw [← Nat.pow_add]; congr 1; lia
  by_cases hq : n / 32 < a.size
  · by_cases h' : a.start + a.size < 4294967295
    · have h := lt_usizeSize h'
      have e₁ := toNat_toUSize (show a.size - n / 32 < USize.size by lia)
      have e₂ := toNat_toUSize (show a.start + n / 32 < USize.size by lia)
      have hv := valAt_from_div a (n / 32) (by lia)
      have hzs : LimbArray.size (UInt32Array.replicate (a.size - n / 32) 0) = a.size - n / 32 :=
        UInt32Array.size_replicate ..
      by_cases h0 : n % 32 = 0
      · have e : shiftRight a n = trim (WordArray.copyW (UInt32Array.replicate (a.size - n / 32) 0)
            0 a.array (a.start + n / 32).toUSize (a.size - n / 32).toUSize (shr_bound a _ hq h).1
            (shr_bound a _ hq h).2.1) := by
          simp only [shiftRight, hq, h', h0, ↓reduceDIte, ↓reduceIte]
        rw [e]
        obtain ⟨f₁, -, f₃⟩ := WordArray.copyW_spec (UInt32Array.replicate (a.size - n / 32) 0) 0
          a.array (a.start + n / 32).toUSize (a.size - n / 32).toUSize
          (shr_bound a _ hq h).1 (shr_bound a _ hq h).2.1
        rw [e₁, e₂, USize.toNat_zero] at f₃
        generalize WordArray.copyW (UInt32Array.replicate (a.size - n / 32) 0) 0 a.array
          (a.start + n / 32).toUSize (a.size - n / 32).toUSize (shr_bound a _ hq h).1
          (shr_bound a _ hq h).2.1 = c at f₁ f₃ ⊢
        rw [toNat_trim, toNat_array_eq_valAt, show c.size = LimbArray.size c from rfl, f₁, hzs]
        show LimbArray.valAt c 0 _ = _
        rw [f₃, hv, hn, h0]
        simp
      · have e : shiftRight a n = trim (WordArray.rshiftW
            (UInt32Array.replicate (a.size - n / 32) 0) 0 a.array (a.start + n / 32).toUSize
            (a.size - n / 32).toUSize (n % 32).toUInt32 (shr_bound a _ hq h).1
            (shr_bound a _ hq h).2.1 (shr_bound a _ hq h).2.2).1 := by
          simp only [shiftRight, hq, h', h0, ↓reduceDIte, ↓reduceIte]
        rw [e]
        have hs32 : (n % 32).toUInt32.toNat = n % 32 := by
          simp only [Nat.toUInt32, UInt32.toNat_ofNat']
          exact Nat.mod_eq_of_lt (by have := Nat.mod_lt n (show 32 > 0 by decide); lia)
        obtain ⟨f₁, -, f₃, f₄⟩ := WordArray.rshiftW_spec (UInt32Array.replicate (a.size - n / 32) 0)
          0 a.array (a.start + n / 32).toUSize (a.size - n / 32).toUSize (n % 32).toUInt32
          (shr_bound a _ hq h).1 (shr_bound a _ hq h).2.1 (shr_bound a _ hq h).2.2
          (by show 0 < (n % 32).toUInt32.toNat; lia)
          (by show (n % 32).toUInt32.toNat < 32; rw [hs32]; exact Nat.mod_lt _ (by decide))
        rw [e₁, e₂, USize.toNat_zero] at f₃
        generalize WordArray.rshiftW (UInt32Array.replicate (a.size - n / 32) 0) 0 a.array
          (a.start + n / 32).toUSize (a.size - n / 32).toUSize (n % 32).toUInt32
          (shr_bound a _ hq h).1 (shr_bound a _ hq h).2.1 (shr_bound a _ hq h).2.2 = p at *
        change 2 ^ (n % 32).toUInt32.toNat * _ + p.2.toNat = _ at f₃
        change p.2.toNat < 2 ^ (n % 32).toUInt32.toNat at f₄
        rw [hs32] at f₃ f₄
        rw [toNat_trim, toNat_array_eq_valAt, show p.1.size = LimbArray.size p.1 from rfl, f₁, hzs]
        show LimbArray.valAt p.1 0 _ = _
        rw [hn, ← Nat.div_div_eq_div_mul, ← hv, ← f₃, Nat.add_comm,
          Nat.add_mul_div_left _ _ (Nat.two_pow_pos _), Nat.div_eq_of_lt f₄, Nat.zero_add]
    · have e : shiftRight a n = trim (ofNat (toNat a / 2 ^ n)) := by
        simp only [shiftRight, hq, h', ↓reduceDIte]
      rw [e, toNat_trim, toNat_ofNat]
  · have e : shiftRight a n = .empty := by simp only [shiftRight, hq, ↓reduceDIte]
    rw [e, toNat_array_eq_valAt]
    simp only [UInt32Array.size_empty, UInt32Array.valAt_zero]
    have : 2 ^ (32 * a.size) ≤ 2 ^ n := Nat.pow_le_pow_right (by decide) (by lia)
    exact (Nat.div_eq_of_lt (by simpa using Nat.lt_of_lt_of_le hA this)).symm

public theorem isTrimmed_shiftRight (a : UInt32Array.Slice) (n : Nat) :
    isTrimmed (shiftRight a n) = true := by
  by_cases hq : n / 32 < a.size
  · by_cases h' : a.start + a.size < 4294967295
    · by_cases h0 : n % 32 = 0
      · simp only [shiftRight, hq, h', h0, ↓reduceDIte, ↓reduceIte]; exact isTrimmed_trim _
      · simp only [shiftRight, hq, h', h0, ↓reduceDIte, ↓reduceIte]; exact isTrimmed_trim _
    · simp only [shiftRight, hq, h', ↓reduceDIte]; exact isTrimmed_trim _
  · simp only [shiftRight, hq, ↓reduceDIte]; exact isTrimmed_empty

/-! ## Bitwise operations

`main`'s `WordArray.bitW` into fresh zeros, by the instance's `land`, `lor` and `xor`.
-/

private theorem hz32 : ∀ (a : UInt32Array) (i : Nat), LimbArray.size a ≤ i →
    LimbArray.val UInt32Array (LimbArray.get a i) = 0 := fun a i h => by
  show a[i]!.toNat = 0
  rw [getElem!_neg a i (Nat.not_lt.2 h)]; rfl

/-- The value of an array over `n ≥ a.size` limbs. -/
private theorem valAt_ge (a : UInt32Array) (n : Nat) (h : a.size ≤ n) :
    LimbArray.valAt a 0 n = toNat a := by
  rw [toNat_array_eq_valAt, show n = a.size + (n - a.size) by lia]
  show _ = LimbArray.valAt a 0 a.size
  rw [LimbArray.valAt_add, LimbArray.valAt_eq_zero (n - a.size) (fun i h₁ _ => hz32 a i (by
    show a.size ≤ i; lia)), Nat.mul_zero, Nat.add_zero]

/--
Limb-wise `f` of `a` and `b`, zero past their ends, trimmed, for an `f` whose value is the
bitwise `op`; on `Nat` were the sizes not `USize`s, which never happens.
-/
@[inline] def bitA (f : UInt32 → UInt32 → UInt32) (op : Nat → Nat → Nat) (a b : UInt32Array) :
    UInt32Array :=
  let n := max a.size b.size
  if h : n < 4294967295 then
    trim (WordArray.bitW f a b (UInt32Array.replicate n 0) n.toUSize (by
      have e := toNat_toUSize (lt_usizeSize h)
      exact ⟨by show _ ≤ (UInt32Array.replicate n 0).size; simp [e],
        by simp [e]; exact lt_usizeSize h⟩))
  else trim (ofNat (op (toNat a) (toNat b)))

private theorem toNat_bitA (f : UInt32 → UInt32 → UInt32) (op : Nat → Nat → Nat)
    (hw : ∀ (a b r : UInt32Array) (n : USize) (hr : WordArray.LoopBound r 0 n),
      LimbArray.size a < USize.size → LimbArray.size b < USize.size →
      LimbArray.valAt (WordArray.bitW f a b r n hr) 0 n.toNat =
        op (LimbArray.valAt a 0 n.toNat) (LimbArray.valAt b 0 n.toNat))
    (a b : UInt32Array) : toNat (bitA f op a b) = op (toNat a) (toNat b) := by
  by_cases h : max a.size b.size < 4294967295
  · have e := toNat_toUSize (lt_usizeSize h)
    have hr : WordArray.LoopBound (UInt32Array.replicate (max a.size b.size) 0) 0
        (max a.size b.size).toUSize :=
      ⟨by show _ ≤ (UInt32Array.replicate _ 0).size; simp [e], by simp [e]; exact lt_usizeSize h⟩
    have eq : bitA f op a b = trim (WordArray.bitW f a b
        (UInt32Array.replicate (max a.size b.size) 0) (max a.size b.size).toUSize hr) := by
      simp only [bitA, h, ↓reduceDIte]
    have h' := hw a b _ _ hr (by show a.size < _; have := lt_usizeSize h; lia)
      (by show b.size < _; have := lt_usizeSize h; lia)
    have hs := WordArray.size_bitW f a b _ _ hr
    rw [e] at h'
    rw [eq]
    generalize WordArray.bitW f a b (UInt32Array.replicate (max a.size b.size) 0)
      (max a.size b.size).toUSize hr = c at h' hs ⊢
    rw [toNat_trim, toNat_array_eq_valAt, show c.size = LimbArray.size c from rfl, hs,
      show LimbArray.size (UInt32Array.replicate (max a.size b.size) 0) = max a.size b.size by
        show (UInt32Array.replicate _ 0).size = _; simp]
    show LimbArray.valAt c 0 _ = _
    rw [h', valAt_ge a _ (by lia), valAt_ge b _ (by lia)]
  · have eq : bitA f op a b = trim (ofNat (op (toNat a) (toNat b))) := by
      simp only [bitA, h, ↓reduceDIte]
    rw [eq, toNat_trim, toNat_ofNat]

private theorem isTrimmed_bitA (f : UInt32 → UInt32 → UInt32) (op : Nat → Nat → Nat)
    (a b : UInt32Array) : isTrimmed (bitA f op a b) = true := by
  unfold bitA; dsimp only; split <;> exact isTrimmed_trim _

/-- Whether `a < b`, by `main`'s `WordArray.ltW` from the top limb down; on `Nat` were the sizes not
`USize`s, which never happens. -/
public def ltA (a b : UInt32Array) : Bool :=
  if max a.size b.size < 4294967295 then WordArray.ltW a b (max a.size b.size).toUSize
  else decide (toNat a < toNat b)

public theorem ltA_iff (a b : UInt32Array) : ltA a b = true ↔ toNat a < toNat b := by
  unfold ltA
  split
  · rename_i h
    have e := toNat_toUSize (lt_usizeSize h)
    rw [WordArray.ltW_iff hz32 a b _ (by show a.size < _; have := lt_usizeSize h; lia)
      (by show b.size < _; have := lt_usizeSize h; lia), e, valAt_ge a _ (by lia),
      valAt_ge b _ (by lia)]
  · exact decide_eq_true_iff

/-- `a &&& b`, trimmed. -/
public def land (a b : UInt32Array) : UInt32Array := bitA (· &&& ·) (· &&& ·) a b

/-- `a ||| b`, trimmed. -/
public def lor (a b : UInt32Array) : UInt32Array := bitA (· ||| ·) (· ||| ·) a b

/-- `a ^^^ b`, trimmed. -/
public def xor (a b : UInt32Array) : UInt32Array := bitA (· ^^^ ·) (· ^^^ ·) a b

@[simp] public theorem toNat_land (a b : UInt32Array) : toNat (land a b) = toNat a &&& toNat b :=
  toNat_bitA _ _ (fun a b r n hr ha hb => WordArray.valAt_bitW_land hz32 a b r n hr ha hb) a b

@[simp] public theorem toNat_lor (a b : UInt32Array) : toNat (lor a b) = toNat a ||| toNat b :=
  toNat_bitA _ _ (fun a b r n hr ha hb => WordArray.valAt_bitW_lor hz32 a b r n hr ha hb) a b

@[simp] public theorem toNat_xor (a b : UInt32Array) : toNat (xor a b) = toNat a ^^^ toNat b :=
  toNat_bitA _ _ (fun a b r n hr ha hb => WordArray.valAt_bitW_xor hz32 a b r n hr ha hb) a b

public theorem isTrimmed_land (a b : UInt32Array) : isTrimmed (land a b) = true :=
  isTrimmed_bitA _ _ a b
public theorem isTrimmed_lor (a b : UInt32Array) : isTrimmed (lor a b) = true :=
  isTrimmed_bitA _ _ a b
public theorem isTrimmed_xor (a b : UInt32Array) : isTrimmed (xor a b) = true :=
  isTrimmed_bitA _ _ a b

end MPN.W32
