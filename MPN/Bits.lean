/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import MPN.Mul.Limb

/-!
# Shifts and bits

* `shiftLeft a n` is `a * 2ⁿ`: `a` copied above `n / 32` zero limbs and shifted left by `n % 32`
  bits in place with `foldlInPlaceThen`, from the bottom limb up.
* `shiftRight a n` is `a / 2ⁿ`: the limbs of `a` from `n / 32` on, copied and shifted right by
  `n % 32` bits in place with `foldrInPlaceThen`, from the top limb down. `shrLimbs`, the shift
  in place, also divides Toom-3's interpolation values by 2.

Both results are trimmed.
-/

open ScalarArray

namespace MPN

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

/--
The loop of `foldlInPlace` with `shlStep`, on a window that starts at `q`: below the window there
are `q` zeros, the first `k` limbs of the window hold `W`, and the rest still hold `O` from `k` on,
with `W + β^k c = (the first k limbs of O) 2^s`.
-/
private theorem shl_loop (sh : Nat) (hsh : sh < 32) (O : List UInt32) (q n : Nat)
    (hn : n = O.length) (r : UInt32Array.Slice) (hs : r.size = n) (k : Nat) (c : UInt32)
    (W : List UInt32) (h0 : r.start = q) (hl : r.array.toList = List.replicate q 0 ++ W ++ O.drop k)
    (hW : W.length = k) (hkn : k ≤ n)
    (hv : ofLimbs W + 2 ^ (32 * k) * c.toNat = ofLimbs (O.take k) * 2 ^ sh)
    (hc : c.toNat < 2 ^ sh) :
    ∃ W', (UInt32Array.Slice.foldlInPlace.loop n (fun _ _ v c => shlStep sh.toUInt64 v c) r hs k
        c).1.array.toList = List.replicate q 0 ++ W' ∧ W'.length = n ∧
      ofLimbs W' + 2 ^ (32 * n) * (UInt32Array.Slice.foldlInPlace.loop n
        (fun _ _ v c => shlStep sh.toUInt64 v c) r hs k c).2.toNat = ofLimbs O * 2 ^ sh := by
  induction hd : n - k generalizing k r c W with
  | zero =>
    have hk : k = n := by lia
    subst hk
    rw [UInt32Array.Slice.foldlInPlace.loop, dite_eq_right (by lia)]
    refine ⟨W, ?_, hW, ?_⟩
    · rw [hl, List.drop_of_length_le (by lia), List.append_nil]
    · rw [hv, List.take_of_length_le (by lia)]
  | succ d ih =>
    have hk : k < n := by lia
    have hkO : k < O.length := by lia
    rw [UInt32Array.Slice.foldlInPlace.loop, dite_eq_left hk]
    have hsa : q + k < r.array.size := by
      have := r.stop_le_array_size; have := r.size_eq; have := r.start_le_stop; lia
    have hdrop := List.drop_eq_getElem_cons hkO
    have hl' := hl
    rw [hdrop] at hl'
    have hrk : r[k]'(by lia) = O[k] := by
      have h := List.getElem_of_eq hl' (i := q + k) (by simpa using hsa)
      rw [List.getElem_append_right (by simp; lia)] at h
      simp only [List.length_append, List.length_replicate, hW, Nat.sub_self,
        List.getElem_cons_zero, UInt32Array.getElem_toList] at h
      rw [UInt32Array.Slice.getElem_eq]
      simpa [h0] using h
    obtain ⟨h₁, h₂⟩ := shlStep_spec sh hsh (r[k]'(by lia)) c hc
    refine ih _ _ (k + 1) _ (W ++ [(shlStep sh.toUInt64 (r[k]'(by lia)) c).1]) ?_ ?_ ?_ (by lia)
      ?_ h₂ (by lia)
    · rw [UInt32Array.Slice.start_set, h0]
    · rw [UInt32Array.Slice.array_set, UInt32Array.toList_set, hl', h0,
        List.set_append_right _ _ (by simp; lia)]
      simp [hW]
      rw [hdrop]
      rfl
    · simp [hW]
    · rw [ofLimbs_concat, hW, List.take_succ_eq_append_getElem hkO, ofLimbs_append, ofLimbs_cons,
        ofLimbs_nil, Nat.mul_zero, Nat.add_zero, List.length_take,
        Nat.min_eq_left (Nat.le_of_lt hkO), ← hrk, Nat.add_mul, ← hv, Nat.mul_succ, Nat.pow_add]
      generalize (shlStep sh.toUInt64 (r[k]'(by lia)) c).1.toNat = o at *
      generalize (shlStep sh.toUInt64 (r[k]'(by lia)) c).2.toNat = c' at *
      generalize (r[k]'(by lia)).toNat = v at *
      generalize ofLimbs W = A at *
      generalize ofLimbs (O.take k) = T at *
      generalize 2 ^ (32 * k) = P at *
      generalize 2 ^ sh = S at *
      generalize (2 : Nat) ^ 32 = B at *
      simp only [Nat.add_zero]
      calc A + P * o + P * B * c' = A + P * (o + B * c') := by
            rw [Nat.mul_add, Nat.mul_assoc, Nat.add_assoc]
        _ = A + P * (v * S + c.toNat) := by rw [h₁]
        _ = (A + P * c.toNat) + P * v * S := by rw [Nat.mul_add, ← Nat.mul_assoc]; lia

/--
Shifts the window of `x` from `q` on left by `s < 32` bits in place, from the bottom limb up, with
the high bits of each limb carried into the one above, and trims.
-/
def shlLimbs (x : UInt32Array) (q : Nat) (s : UInt64) : UInt32Array :=
  (x.toSlice q x.size).foldlInPlaceThen (0 : UInt32) (fun _ _ v c => shlStep s v c)
    (fun r _ => trim r.array)

/--
`a * 2ⁿ`, trimmed: `a` copied with one `memcpy` above `n / 32` zero limbs and below one more, then
`shlLimbs` by `n % 32`.
-/
public def shiftLeft (a : UInt32Array.Slice) (n : Nat) : UInt32Array :=
  shlLimbs (a.array.copySlice a.start (.replicate (n / 32 + a.size + 1) 0) (n / 32) a.size)
    (n / 32) (n % 32).toUInt64

private theorem toList_copyAt (a : UInt32Array.Slice) (q : Nat) :
    (a.array.copySlice a.start (.replicate (q + a.size + 1) 0) q a.size).toList =
      List.replicate q 0 ++ (a.copy.toList ++ [0]) := by
  have := a.stop_le_array_size
  have := a.start_le_stop
  have hs := a.size_eq
  have hstop : a.start + a.size = a.stop := by lia
  have hmin : min a.size (a.array.size - a.start) = a.size := by lia
  simp only [UInt32Array.toList_copySlice, UInt32Array.toList_replicate,
    UInt32Array.size_replicate, hstop, hmin, List.extract_eq_take_drop, List.drop_replicate,
    Nat.sub_zero, List.take_replicate, UInt32Array.Slice.copy, UInt32Array.toList_extract]
  rw [Nat.min_eq_left (by lia), Nat.min_eq_left (by lia),
    show q + a.size + 1 - (q + a.size) = 1 by lia, List.append_assoc]
  rfl

@[simp] public theorem toNat_shiftLeft (a : UInt32Array.Slice) (n : Nat) :
    toNat (shiftLeft a n) = toNat a * 2 ^ n := by
  have hA := toNat_lt a
  rw [shiftLeft, shlLimbs, UInt32Array.Slice.foldlInPlaceThen_eq, toNat_trim, toNat_toSlice]
  generalize hx : a.array.copySlice a.start (.replicate (n / 32 + a.size + 1) 0) (n / 32) a.size
    = x
  have hxl : x.toList = List.replicate (n / 32) 0 ++ (a.copy.toList ++ [0]) := by
    rw [← hx, toList_copyAt]
  have hxs : x.size = n / 32 + a.size + 1 := by
    rw [← UInt32Array.length_toList, hxl]; simp; lia
  obtain ⟨W, hl, hW, hv⟩ := shl_loop (n % 32) (Nat.mod_lt _ (by decide)) (a.copy.toList ++ [0])
    (n / 32) (x.toSlice (n / 32) x.size).size (by simp; lia) (x.toSlice (n / 32) x.size) rfl
    0 0 []
    (by simp; lia) (by simpa using hxl) rfl (Nat.zero_le _) (by simp) (Nat.two_pow_pos _)
  simp only [UInt32Array.Slice.foldlInPlace]
  rw [hl, ofLimbs_append, ofLimbs_replicate_zero, Nat.zero_add, List.length_replicate]
  -- The carry out of the top limb is zero: `a 2^s < β^(m + 1)`.
  have hO : ofLimbs (a.copy.toList ++ [0]) = toNat a := by
    rw [show ([0] : List UInt32) = List.replicate 1 0 from rfl, ofLimbs_append_replicate_zero]
    rfl
  rw [hO] at hv
  have hsz : (x.toSlice (n / 32) x.size).size = a.size + 1 := by simp; lia
  generalize (UInt32Array.Slice.foldlInPlace.loop _ (fun _ _ v (c : UInt32) =>
    shlStep (n % 32).toUInt64 v c) _ _ 0 (0 : UInt32)).2 = cc at hv
  generalize cc.toNat = c at hv
  rw [hsz] at hv
  have hlt : toNat a * 2 ^ (n % 32) < 2 ^ (32 * (a.size + 1)) := by
    rw [Nat.mul_succ, Nat.pow_add]
    exact Nat.mul_lt_mul_of_lt_of_le (by simpa using hA) (Nat.pow_le_pow_right (by decide)
      (Nat.le_of_lt (Nat.mod_lt _ (by decide)))) (Nat.two_pow_pos _)
  have hc : c = 0 := by
    rcases Nat.eq_zero_or_pos c with h | h
    · exact h
    · have := Nat.mul_le_mul_left (2 ^ (32 * (a.size + 1))) h
      lia
  rw [hc, Nat.mul_zero, Nat.add_zero] at hv
  have hn : 2 ^ n = 2 ^ (32 * (n / 32)) * 2 ^ (n % 32) := by
    rw [← Nat.pow_add]; congr 1; lia
  rw [hv, hn, ← Nat.mul_assoc, Nat.mul_comm (2 ^ (32 * (n / 32))) (toNat a), Nat.mul_assoc]

public theorem isTrimmed_shiftLeft (a : UInt32Array.Slice) (n : Nat) :
    isTrimmed (shiftLeft a n) = true := by
  rw [shiftLeft, shlLimbs, UInt32Array.Slice.foldlInPlaceThen_eq]
  exact isTrimmed_trim _

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
The loop of `foldrInPlace` with `shrStep`: below index `k` the limbs of `O` are untouched, above
it they hold `⌊O' / 2^s⌋` for the limbs `O'` of `O` from `k` on, and the carry is limb `k`.
-/
private theorem shr_loop (sh : Nat) (hsh : sh < 32) (O : List UInt32) (n : Nat) (hn : n = O.length)
    (r : UInt32Array.Slice) (hs : r.size = n) (k : Nat) (hk : k ≤ n) (c : UInt32)
    (W : List UInt32) (h0 : r.start = 0) (hl : r.array.toList = O.take k ++ W)
    (hW : ofLimbs W = ofLimbs (O.drop k) / 2 ^ sh)
    (hc : c.toNat = ofLimbs (O.drop k) % 2 ^ 32) :
    ofLimbs (UInt32Array.Slice.foldrInPlace.loop n (fun _ _ v c => shrStep sh.toUInt64 v c) r hs
      k hk c).1.array.toList = ofLimbs O / 2 ^ sh := by
  induction k generalizing r c W with
  | zero =>
    rw [UInt32Array.Slice.foldrInPlace.loop, hl, List.take_zero, List.nil_append, hW,
      List.drop_zero]
  | succ k ih =>
    rw [UInt32Array.Slice.foldrInPlace.loop]
    have hkO : k < O.length := by lia
    have hra : k < r.array.size := by
      have := r.stop_le_array_size; have := r.size_eq; have := r.start_le_stop; lia
    have hrk : r[k]'(by lia) = O[k] := by
      have h := List.getElem_of_eq hl (i := k) (by simp; lia)
      rw [List.getElem_append_left (by simp; lia), List.getElem_take,
        UInt32Array.getElem_toList] at h
      rw [UInt32Array.Slice.getElem_eq]
      simpa [h0] using h
    have hdrop := List.drop_eq_getElem_cons hkO
    refine ih _ _ _ _ ((shrStep sh.toUInt64 (r[k]'(by lia)) c).1 :: W) ?_ ?_ ?_ ?_
    · rw [UInt32Array.Slice.start_set, h0]
    · rw [UInt32Array.Slice.array_set, UInt32Array.toList_set, hl, h0, Nat.zero_add,
        List.take_succ_eq_append_getElem hkO, List.append_assoc,
        List.set_append_right _ _ (by simp; lia)]
      simp [Nat.min_eq_left (Nat.le_of_lt hkO)]
    · rw [ofLimbs_cons, toNat_shrStep sh hsh, hW, hc, hrk, hdrop, ofLimbs_cons]
      have hP : (2 : Nat) ^ 32 = 2 ^ sh * 2 ^ (32 - sh) := by
        rw [← Nat.pow_add]; congr 1; lia
      rw [hP]
      exact shr_arith _ _ _ _ (Nat.two_pow_pos _) (by rw [← hP]; exact O[k].toNat_lt)
    · show (r[k]'(by lia)).toNat = _
      rw [hrk, hdrop, ofLimbs_cons, Nat.add_mul_mod_self_left,
        Nat.mod_eq_of_lt O[k].toNat_lt]

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
  simp only [UInt32Array.Slice.foldrInPlaceThen_eq, UInt32Array.Slice.foldrInPlace]
  rw [toNat_trim, toNat_toSlice, toNat_toSlice]
  exact shr_loop s hs x.toList _ (by simp) _ _ _ _ 0 [] (by simp)
    (by rw [List.take_of_length_le (by simp)]; simp)
    (by rw [List.drop_of_length_le (by simp)]; simp)
    (by rw [List.drop_of_length_le (by simp)]; simp)

/-- `a / 2ⁿ`, trimmed: the limbs of `a` from `n / 32` on, copied, then `shrLimbs` by `n % 32`. -/
public def shiftRight (a : UInt32Array.Slice) (n : Nat) : UInt32Array :=
  if n / 32 < a.size then shrLimbs (a.slice (n / 32) a.size).copy (n % 32).toUInt64 else .empty

@[simp] public theorem toNat_shiftRight (a : UInt32Array.Slice) (n : Nat) :
    toNat (shiftRight a n) = toNat a / 2 ^ n := by
  have hA := toNat_lt a
  have hn : 2 ^ n = 2 ^ (32 * (n / 32)) * 2 ^ (n % 32) := by
    rw [← Nat.pow_add]; congr 1; lia
  by_cases hq : n / 32 < a.size
  · have hsl := toNat_slice_from a (n / 32) (by lia)
    rw [shiftRight, ite_eq_left hq, toNat_shrLimbs _ _ (Nat.mod_lt _ (by decide)), toNat_copy,
      hsl, hn, Nat.div_div_eq_div_mul]
  · have e : shiftRight a n = .empty := by rw [shiftRight, ite_eq_right hq]
    rw [e, toNat_toSlice]
    simp only [UInt32Array.toList_empty, ofLimbs_nil]
    -- `a < β^a.size ≤ 2ⁿ`.
    have : 2 ^ (32 * a.size) ≤ 2 ^ n := Nat.pow_le_pow_right (by decide) (by lia)
    exact (Nat.div_eq_of_lt (by lia)).symm

public theorem isTrimmed_shiftRight (a : UInt32Array.Slice) (n : Nat) :
    isTrimmed (shiftRight a n) = true := by
  unfold shiftRight
  split
  · rw [shrLimbs, UInt32Array.Slice.foldrInPlaceThen_eq]
    exact isTrimmed_trim _
  · rw [isTrimmed_iff]; simp

/-! ## Bitwise operations -/

/-- Bit `j` of a number is bit `j % 32` of its limb `j / 32`. -/
public theorem testBit_ofLimbs (l : List UInt32) (j : Nat) :
    (ofLimbs l).testBit j = (l.getD (j / 32) 0).toNat.testBit (j % 32) := by
  induction l generalizing j with
  | nil => simp
  | cons x l ih =>
    rw [ofLimbs_cons, Nat.add_comm, Nat.testBit_two_pow_mul_add _ x.toNat_lt]
    by_cases hj : j < 32
    · rw [ite_eq_left hj, Nat.div_eq_of_lt hj, Nat.mod_eq_of_lt hj]
      rfl
    · rw [ite_eq_right hj, ih]
      have h₁ : j / 32 = (j - 32) / 32 + 1 := by lia
      have h₂ : j % 32 = (j - 32) % 32 := by lia
      rw [h₁, h₂, List.getD_cons_succ]

/-- The limbs `f (a i) (b i)`, trimmed, for a limbwise operation `f` with `f 0 0 = 0`. -/
def bitwiseLimbs (f : UInt32 → UInt32 → UInt32) (a b : UInt32Array.Slice) : UInt32Array :=
  trim (UInt32Array.ofFn (n := max a.size b.size) fun i => f (a.getD i 0) (b.getD i 0))

private theorem getD_bitwiseLimbs (f : UInt32 → UInt32 → UInt32) (hf : f 0 0 = 0)
    (a b : UInt32Array.Slice) (k : Nat) :
    (UInt32Array.ofFn (n := max a.size b.size) fun i => f (a.getD i 0) (b.getD i 0)).toList.getD
      k 0 = f (a.getD k 0) (b.getD k 0) := by
  rw [UInt32Array.toList_ofFn, List.getD_eq_getElem?_getD]
  by_cases hk : k < max a.size b.size
  · rw [List.getElem?_ofFn]
    simp [hk]
  · rw [List.getElem?_ofFn]
    simp only [hk, ↓reduceDIte, Option.getD_none]
    rw [UInt32Array.Slice.getD_eq, UInt32Array.Slice.getD_eq]
    simp only [show ¬ k < a.size by lia, show ¬ k < b.size by lia, ↓reduceDIte]
    exact hf.symm

private theorem testBit_bitwiseLimbs (f : UInt32 → UInt32 → UInt32) (hf : f 0 0 = 0)
    (a b : UInt32Array.Slice) (j : Nat) :
    (toNat (bitwiseLimbs f a b)).testBit j =
      (f (a.getD (j / 32) 0) (b.getD (j / 32) 0)).toNat.testBit (j % 32) := by
  rw [bitwiseLimbs, toNat_trim, toNat_toSlice, testBit_ofLimbs, getD_bitwiseLimbs f hf]

private theorem testBit_toNat (a : UInt32Array.Slice) (j : Nat) :
    (toNat a).testBit j = (a.getD (j / 32) 0).toNat.testBit (j % 32) := by
  rw [toNat, testBit_ofLimbs, ← getD_eq_getD_toList_copy]

/-- `a &&& b`, trimmed. -/
public def land (a b : UInt32Array.Slice) : UInt32Array := bitwiseLimbs (· &&& ·) a b

/-- `a ||| b`, trimmed. -/
public def lor (a b : UInt32Array.Slice) : UInt32Array := bitwiseLimbs (· ||| ·) a b

/-- `a ^^^ b`, trimmed. -/
public def xor (a b : UInt32Array.Slice) : UInt32Array := bitwiseLimbs (· ^^^ ·) a b

@[simp] public theorem toNat_land (a b : UInt32Array.Slice) :
    toNat (land a b) = toNat a &&& toNat b := by
  apply Nat.eq_of_testBit_eq
  intro j
  rw [land, testBit_bitwiseLimbs _ (by decide), UInt32.toNat_and, Nat.testBit_and, Nat.testBit_and,
    testBit_toNat, testBit_toNat]

@[simp] public theorem toNat_lor (a b : UInt32Array.Slice) :
    toNat (lor a b) = toNat a ||| toNat b := by
  apply Nat.eq_of_testBit_eq
  intro j
  rw [lor, testBit_bitwiseLimbs _ (by decide), UInt32.toNat_or, Nat.testBit_or, Nat.testBit_or,
    testBit_toNat, testBit_toNat]

@[simp] public theorem toNat_xor (a b : UInt32Array.Slice) :
    toNat (xor a b) = toNat a ^^^ toNat b := by
  apply Nat.eq_of_testBit_eq
  intro j
  rw [xor, testBit_bitwiseLimbs _ (by decide), UInt32.toNat_xor, Nat.testBit_xor, Nat.testBit_xor,
    testBit_toNat, testBit_toNat]

public theorem isTrimmed_land (a b : UInt32Array.Slice) : isTrimmed (land a b) = true :=
  isTrimmed_trim _
public theorem isTrimmed_lor (a b : UInt32Array.Slice) : isTrimmed (lor a b) = true :=
  isTrimmed_trim _
public theorem isTrimmed_xor (a b : UInt32Array.Slice) : isTrimmed (xor a b) = true :=
  isTrimmed_trim _

end MPN
