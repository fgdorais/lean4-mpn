/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import MPN.Mul.Fermat
public import MPN.ListIndex
public import MPN.Poly
public import MPN.Mul.Toom4
public import MPN.Mul.Basecase

/-!
# The transform

The discrete Fourier transform of length `2ᵏ` modulo `F = 2ᴺ + 1` with `ω = 2ᵉ`, on residues
(`n + 1` limbs below `F`), by the recursive radix-2 split: the values at `ωʲ` and `ω^(j + 2ᵏ⁻¹)` of
a polynomial `p` are `p_even(ω²ʲ) ± ωʲ p_odd(ω²ʲ)`, since `ω^(2ᵏ⁻¹) ≡ -1`. The twiddles `ωʲ` are
products by powers of two, `mulPow2`.
-/

open ScalarArray

namespace MPN.FFT

open Fermat

/-- A residue modulo `fermat n`: `n + 1` limbs with a value below `fermat n`. -/
@[expose] public def IsRes (n : Nat) (x : UInt32Array) : Prop := x.size = n + 1 ∧ toNat x < fermat n

/-- The values at `2^(e j)`, `j < 2ᵏ`, of the polynomial with coefficients `xs`, modulo `F`. -/
public def transform {n : Nat} (M : FermatMod n) : Nat → Nat → List UInt32Array → List UInt32Array
  | 0, _, xs => xs
  | k + 1, e, xs =>
    let ev := transform M k (2 * e) (evens xs)
    let od := transform M k (2 * e) (odds xs)
    let tw := List.zipWith (fun o j => mulPow2I M o (e * j)) od (List.range (2 ^ k))
    List.zipWith (fun x (y : UInt32Array) => addModI M x y) ev tw ++ List.zipWith (fun x
      (y : UInt32Array) => subModI M x y) ev tw

/-- The values of a list of arrays. -/
@[expose] public def vals (xs : List UInt32Array) : List Nat :=
  xs.map fun x : UInt32Array => toNat x

/-! ## Congruences -/

/-- The sum of a butterfly. -/
private theorem butterfly_add (A B s F : Nat) :
    (A % F + (B % F * s) % F) % F = (A + s * B) % F := by
  apply mod_eq_iff_dvd.2
  have h₁ := dvd_mod_sub A F
  have h₂ := dvd_mod_sub (B % F * s) F
  have h₃ := dvd_mod_sub B F
  have e : ((A % F + (B % F * s) % F : Nat) : Int) - ((A + s * B : Nat) : Int) =
      (((A % F : Nat) : Int) - A) + ((((B % F * s) % F : Nat) : Int) - ((B % F * s : Nat) : Int)) +
        (s : Int) * (((B % F : Nat) : Int) - B) := by
    push_cast; grind
  rw [e]
  exact Int.dvd_add (Int.dvd_add h₁ h₂) (Int.dvd_trans h₃ (Int.dvd_mul_left _ _))

/-- The difference of a butterfly: `ω^(j + 2ᵏ) = ωʲ u` with `u ≡ -1`. -/
private theorem butterfly_sub (A A' B B' s u F : Nat) (hA : A' % F = A % F)
    (hB : B' % F = B % F) (hu : (u + 1) % F = 0) :
    (A' + s * u * B') % F = (A % F + F - (B % F * s) % F) % F := by
  rcases Nat.eq_zero_or_pos F with hF | hF
  · subst hF; simp at hu
  have hc : (B % F * s) % F < F := Nat.mod_lt _ hF
  apply mod_eq_iff_dvd.2
  have h₁ : (F : Int) ∣ (A' : Int) - ((A % F : Nat) : Int) :=
    mod_eq_iff_dvd.1 (by rw [hA, Nat.mod_mod])
  have h₂ : (F : Int) ∣ (B' : Int) - ((B % F : Nat) : Int) :=
    mod_eq_iff_dvd.1 (by rw [hB, Nat.mod_mod])
  have h₃ : (F : Int) ∣ ((u + 1 : Nat) : Int) - ((0 : Nat) : Int) :=
    mod_eq_iff_dvd.1 (by rw [hu, Nat.zero_mod])
  have h₄ := dvd_mod_sub (B % F * s) F
  have e : ((A' + s * u * B' : Nat) : Int) - ((A % F + F - (B % F * s) % F : Nat) : Int) =
      ((A' : Int) - ((A % F : Nat) : Int)) - F -
        ((((B % F * s) % F : Nat) : Int) - ((B % F * s : Nat) : Int)) * (-1) +
        (s : Int) * B' * (((u + 1 : Nat) : Int) - ((0 : Nat) : Int)) -
        (s : Int) * ((B' : Int) - ((B % F : Nat) : Int)) := by
    rw [Int.ofNat_sub (by lia)]
    push_cast; grind
  rw [e]
  exact Int.dvd_sub (Int.dvd_add (Int.dvd_sub (Int.dvd_sub h₁ (Int.dvd_refl _))
    (Int.dvd_trans h₄ (Int.dvd_mul_right _ _))) (Int.dvd_trans h₃ (Int.dvd_mul_left _ _)))
    (Int.dvd_trans h₂ (Int.dvd_mul_left _ _))

/-! ## The transform -/

/-- `a u + a ≡ 0` when `u ≡ -1`. -/
private theorem mul_neg_one_add {a u F : Nat} (hu : (u + 1) % F = 0) : (a * u + a) % F = 0 := by
  rw [show a * u + a = a * (u + 1) by rw [Nat.mul_add, Nat.mul_one], Nat.mul_mod, hu,
    Nat.mul_zero, Nat.zero_mod]

public theorem transform_spec {n : Nat} (M : FermatMod n) (hn : 1 ≤ n) (k : Nat) :
    ∀ (e : Nat) (xs : List UInt32Array), xs.length = 2 ^ k → (∀ x ∈ xs, IsRes n x) →
    (1 ≤ k → (2 ^ (e * 2 ^ (k - 1)) + 1) % fermat n = 0) →
    (transform M k e xs).length = 2 ^ k ∧
      (∀ j < 2 ^ k, IsRes n ((transform M k e xs).getD j default)) ∧
      ∀ j < 2 ^ k, toNat ((transform M k e xs).getD j default) =
        polyVal (2 ^ (e * j)) (vals xs) % fermat n := by
  have hFpos : 0 < fermat n := by simp [fermat]
  induction k with
  | zero =>
    intro e xs hl hres _
    obtain ⟨x, rfl⟩ : ∃ x, xs = [x] := List.length_eq_one_iff.1 (by simpa using hl)
    have hx := hres x (by simp)
    refine ⟨by simp [transform], fun j hj => ?_, fun j hj => ?_⟩
    · have hj0 : j = 0 := by simp at hj; lia
      subst hj0
      simpa [transform] using hx
    · have hj0 : j = 0 := by simp at hj; lia
      subst hj0
      simp only [transform, List.getD_cons_zero, vals, List.map_cons, List.map_nil, polyVal,
        Nat.mul_zero, Nat.add_zero]
      exact (Nat.mod_eq_of_lt hx.2).symm
  | succ k ih =>
    intro e xs hl hres hw
    have hw' := hw (by lia)
    simp only [Nat.add_sub_cancel] at hw'
    obtain ⟨hle, hlo⟩ := length_evens_odds xs (2 ^ k) (by rw [hl, Nat.pow_succ]; lia)
    have hsub : 1 ≤ k → (2 ^ (2 * e * 2 ^ (k - 1)) + 1) % fermat n = 0 := fun hk => by
      rw [show 2 * e * 2 ^ (k - 1) = e * 2 ^ k by
        rw [Nat.mul_comm 2 e, Nat.mul_assoc, ← Nat.pow_succ']; congr 2; lia]
      exact hw'
    obtain ⟨le, re, ve⟩ := ih (2 * e) (evens xs) hle (fun x h => hres x (mem_evens h)) hsub
    obtain ⟨lo, ro, vo⟩ := ih (2 * e) (odds xs) hlo (fun x h => hres x (mem_odds h)) hsub
    simp only [transform]
    generalize transform M k (2 * e) (evens xs) = E at *
    generalize transform M k (2 * e) (odds xs) = O at *
    -- The twiddled odd values.
    have ltw : (List.zipWith (fun o j => mulPow2I M o (e * j)) O (List.range (2 ^ k))).length =
        2 ^ k := by simp [lo]
    have vtw : ∀ j < 2 ^ k, (List.zipWith (fun o j => mulPow2I M o (e * j)) O
        (List.range (2 ^ k))).getD j default = mulPow2I M (O.getD j default) (e * j) :=
        fun j hj => by
      rw [getD_zipWith _ _ _ _ _ default 0 (by rw [lo]; exact hj) (by simpa using hj),
        getD_range _ _ _ hj]
    generalize List.zipWith (fun o j => mulPow2I M o (e * j)) O (List.range (2 ^ k)) = T at *
    have rO := ro
    have rE := re
    have rT : ∀ j < 2 ^ k, IsRes n (T.getD j default) := fun j hj => by
      rw [vtw j hj]
      exact ⟨size_mulPow2I M _ _ hn (rO j hj).1, toNat_mulPow2I_lt M _ _ hn (rO j hj).1 (rO j hj).2⟩
    have l1 : (List.zipWith (fun x
      (y : UInt32Array) => addModI M x y) E T).length = 2 ^ k := by simp [le, ltw]
    have g1 : ∀ j < 2 ^ k, (List.zipWith (fun x
      (y : UInt32Array) => addModI M x y) E T ++ List.zipWith (fun x
          (y : UInt32Array) => subModI M x y) E T).getD j
        default = addModI M (E.getD j default) (T.getD j default) := fun j hj => by
      rw [getD_append_left _ _ _ _ (by rw [l1]; exact hj),
        getD_zipWith _ _ _ _ _ default default (by rw [le]; exact hj) (by rw [ltw]; exact hj)]
    have g2 : ∀ j < 2 ^ k, (List.zipWith (fun x
      (y : UInt32Array) => addModI M x y) E T ++ List.zipWith (fun x
          (y : UInt32Array) => subModI M x y) E T).getD
        (j + 2 ^ k) default = subModI M (E.getD j default) (T.getD j default) := fun j hj => by
      rw [getD_append_right _ _ _ _ (by rw [l1]; lia), l1, Nat.add_sub_cancel,
        getD_zipWith _ _ _ _ _ default default (by rw [le]; exact hj) (by rw [ltw]; exact hj)]
    -- The values of the halves.
    have hEv : ∀ j < 2 ^ k, toNat (E.getD j default) =
        polyVal (2 ^ (2 * e * j)) (evens (vals xs)) % fermat n := fun j hj => by
      rw [ve j hj, vals, vals, map_evens]
    have hTv : ∀ j < 2 ^ k, toNat (T.getD j default) =
        (polyVal (2 ^ (2 * e * j)) (odds (vals xs)) % fermat n * 2 ^ (e * j)) % fermat n :=
      fun j hj => by
        rw [vtw j hj, toNat_mulPow2I M _ _ hn (rO j hj).1 (rO j hj).2, vo j hj, vals, vals,
          map_odds]
    have hTs : ∀ j < 2 ^ k, (T.getD j default).toSlice.size ≤ n + 1 := fun j hj => by
      simp only [UInt32Array.size_toSlice, (rT j hj).1]; lia
    have hsq : ∀ j, 2 ^ (e * j) * 2 ^ (e * j) = 2 ^ (2 * e * j) := fun j => by
      rw [← Nat.pow_add, Nat.mul_assoc, Nat.two_mul]
    refine ⟨by simp [le, ltw, Nat.pow_succ]; lia, fun j hj => ?_, fun j hj => ?_⟩
    · rcases Nat.lt_or_ge j (2 ^ k) with h | h
      · rw [g1 j h]
        exact ⟨size_addModI M _ _ (rE j h).1 (hTs j h), by
          rw [toNat_addModI M _ _ hn (rE j h).1 (hTs j h) (rE j h).2 (rT j h).2]
          exact Nat.mod_lt _ hFpos⟩
      · obtain ⟨j', rfl⟩ : ∃ j', j = j' + 2 ^ k := ⟨j - 2 ^ k, by lia⟩
        have h' : j' < 2 ^ k := by rw [Nat.pow_succ] at hj; lia
        rw [g2 j' h']
        exact ⟨size_subModI M _ _ (rE j' h').1 (hTs j' h'), by
          rw [toNat_subModI M _ _ hn (rE j' h').1 (hTs j' h') (rE j' h').2
            (rT j' h').2]
          exact Nat.mod_lt _ hFpos⟩
    · rcases Nat.lt_or_ge j (2 ^ k) with h | h
      · rw [g1 j h, toNat_addModI M _ _ hn (rE j h).1 (hTs j h) (rE j h).2 (rT j h).2,
          hEv j h,
          hTv j h, butterfly_add]
        conv => rhs; rw [polyVal_evens_odds, hsq]
      · obtain ⟨j', rfl⟩ : ∃ j', j = j' + 2 ^ k := ⟨j - 2 ^ k, by lia⟩
        have h' : j' < 2 ^ k := by rw [Nat.pow_succ] at hj; lia
        rw [g2 j' h', toNat_subModI M _ _ hn (rE j' h').1 (hTs j' h') (rE j' h').2
          (rT j' h').2, hEv j' h', hTv j' h']
        conv => rhs; rw [polyVal_evens_odds,
          show 2 ^ (e * (j' + 2 ^ k)) = 2 ^ (e * j') * 2 ^ (e * 2 ^ k) by
            rw [Nat.mul_add, Nat.pow_add]]
        -- `(ωʲ u)² ≡ ω²ʲ`, since `u = ω^(2ᵏ) ≡ -1`.
        have hu2 := sq_of_neg_one hw'
        have ht : (2 ^ (e * j') * 2 ^ (e * 2 ^ k) * (2 ^ (e * j') * 2 ^ (e * 2 ^ k))) %
            fermat n = 2 ^ (2 * e * j') % fermat n := by
          rw [show 2 ^ (e * j') * 2 ^ (e * 2 ^ k) * (2 ^ (e * j') * 2 ^ (e * 2 ^ k)) =
              (2 ^ (e * j') * 2 ^ (e * j')) * (2 ^ (e * 2 ^ k) * 2 ^ (e * 2 ^ k)) by
              rw [Nat.mul_assoc, Nat.mul_left_comm (2 ^ (e * 2 ^ k)), ← Nat.mul_assoc],
            Nat.mul_mod, hu2, ← Nat.mul_mod, Nat.mul_one, hsq]
        exact (butterfly_sub _ _ _ _ _ _ _ (polyVal_mod ht _) (polyVal_mod ht _) hw').symm

/-! ## Pieces -/

/-- The values of the `L` pieces of `m` limbs of `s` from limb `i`. -/
@[expose] public def pieceList (s : UInt32Array.Slice) (m : Nat) : Nat → Nat → List Nat
  | _, 0 => []
  | i, L + 1 => toNat (s.slice i (i + m)) :: pieceList s m (i + m) L

public theorem length_pieceList (s : UInt32Array.Slice) (m i L : Nat) :
    (pieceList s m i L).length = L := by
  induction L generalizing i with
  | zero => rfl
  | succ L ih => simp [pieceList, ih]

/-- The pieces of `s` from limb `i` cover the rest of `s` when `i + L m ≥ s.size`. -/
public theorem toNat_eq_polyVal_pieceList (s : UInt32Array.Slice) (m i L : Nat)
    (h : s.size ≤ i + L * m) :
    toNat (s.slice i s.size) = polyVal (2 ^ (32 * m)) (pieceList s m i L) := by
  induction L generalizing i with
  | zero =>
    simp only [pieceList, polyVal]
    exact toNat_of_size_eq_zero (by simp only [UInt32Array.Slice.size_slice]; lia)
  | succ L ih =>
    rw [toNat_slice_split s i m, ih (i + m) (by rw [Nat.add_mul, Nat.one_mul] at h; lia)]
    rfl

/-- Pieces at or past the end of `s` are zero. -/
public theorem pieceList_zero (s : UInt32Array.Slice) (m i L : Nat) (h : s.size ≤ i) :
    ∀ c ∈ pieceList s m i L, c = 0 := by
  induction L generalizing i with
  | zero => simp [pieceList]
  | succ L ih =>
    intro c hc
    simp only [pieceList, List.mem_cons] at hc
    rcases hc with rfl | hc
    · exact toNat_of_size_eq_zero (by simp only [UInt32Array.Slice.size_slice]; lia)
    · exact ih (i + m) (by lia) c hc

public theorem pieceList_append (s : UInt32Array.Slice) (m i L L' : Nat) :
    pieceList s m i (L + L') = pieceList s m i L ++ pieceList s m (i + L * m) L' := by
  induction L generalizing i with
  | zero => simp [pieceList]
  | succ L ih =>
    rw [Nat.add_right_comm, pieceList, ih, pieceList, List.cons_append]
    congr 2
    rw [Nat.add_mul, Nat.one_mul]; lia

public theorem pieceList_lt (s : UInt32Array.Slice) (m i L : Nat) :
    ∀ c ∈ pieceList s m i L, c < 2 ^ (32 * m) := by
  induction L generalizing i with
  | zero => simp [pieceList]
  | succ L ih =>
    intro c hc
    simp only [pieceList, List.mem_cons] at hc
    rcases hc with rfl | hc
    · have := toNat_lt (s.slice i (i + m))
      simp only [UInt32Array.Slice.size_slice] at this
      exact Nat.lt_of_lt_of_le this (Nat.pow_le_pow_right (by decide) (by lia))
    · exact ih (i + m) c hc

/-! ## Multiplication -/

/-- The `L` pieces of `m` limbs of `s` from limb `i`, as residues of `n + 1` limbs. -/
public def pieceArrays (s : UInt32Array.Slice) (m n : Nat) : Nat → Nat → List UInt32Array
  | _, 0 => []
  | i, L + 1 => copyPadded (s.slice i (i + m)) (n + 1) :: pieceArrays s m n (i + m) L

public theorem vals_pieceArrays (s : UInt32Array.Slice) (m n i L : Nat) :
    vals (pieceArrays s m n i L) = pieceList s m i L := by
  induction L generalizing i with
  | zero => rfl
  | succ L ih =>
    simp only [pieceArrays, pieceList, vals, List.map_cons, toNat_copyPadded]
    rw [← vals, ih]

public theorem length_pieceArrays (s : UInt32Array.Slice) (m n i L : Nat) :
    (pieceArrays s m n i L).length = L := by
  induction L generalizing i with
  | zero => rfl
  | succ L ih => simp [pieceArrays, ih]

public theorem isRes_pieceArrays (s : UInt32Array.Slice) (m n i L : Nat) (hmn : m ≤ n) :
    ∀ x ∈ pieceArrays s m n i L, IsRes n x := by
  induction L generalizing i with
  | zero => simp [pieceArrays]
  | succ L ih =>
    intro x hx
    simp only [pieceArrays, List.mem_cons] at hx
    rcases hx with rfl | hx
    · refine ⟨size_copyPadded _ _ (by simp only [UInt32Array.Slice.size_slice]; lia), ?_⟩
      rw [toNat_copyPadded]
      have := toNat_lt (s.slice i (i + m))
      simp only [UInt32Array.Slice.size_slice] at this
      have h₁ : 2 ^ (32 * (min (i + m) s.size - i)) ≤ 2 ^ (32 * n) :=
        Nat.pow_le_pow_right (by decide) (by lia)
      simp only [fermat]; lia
    · exact ih (i + m) x hx

/--
The product `a * b` by the FFT: `a` and `b` in pieces of `m` limbs, `2ᵏ` of them, transformed
modulo `F = 2^(32 n) + 1` with `ω = 2^(64 n / 2ᵏ)`, multiplied pointwise by `mulRec`, transformed
back with `ω⁻¹ = 2^(64 n - 64 n / 2ᵏ)`, divided by `2ᵏ` (a product by `2^(64 n - k)`) and
assembled.
-/
public def fftMulAt (a b : UInt32Array.Slice) (k m n : Nat)
    (mulRec : (x y : UInt32Array.Slice) → x.size + y.size < a.size + b.size → UInt32Array) :
    UInt32Array :=
  let M := fermatMod n
  let e := 64 * n / 2 ^ k
  let fa := transform M k e (pieceArrays a m n 0 (2 ^ k))
  let fb := transform M k e (pieceArrays b m n 0 (2 ^ k))
  let fc := (List.range (2 ^ k)).map fun j =>
    let x := fa.getD j default
    let y := fb.getD j default
    if h : x.toSlice.size + y.toSlice.size < a.size + b.size then normProd M (mulRec x y h)
    else x
  let c := (transform M k (64 * n - e) fc).map fun z => mulPow2I M z (64 * n - k)
  assembleFrom (.replicate (a.size + b.size) 0) 0 m (c.take ((a.size + b.size + m - 1) / m))

/-- `⌈a / m⌉ + ⌈b / m⌉ ≤ ⌈(a + b) / m⌉ + 1`. -/
private theorem ceil_add_ceil (a b m : Nat) (hm : 1 ≤ m) :
    (a + m - 1) / m + (b + m - 1) / m ≤ (a + b + m - 1) / m + 1 := by
  have h₁ := Nat.div_mul_le_self (a + m - 1) m
  have h₂ := Nat.div_mul_le_self (b + m - 1) m
  generalize (a + m - 1) / m = p at *
  generalize (b + m - 1) / m = q at *
  rcases Nat.eq_zero_or_pos (p + q) with h | h
  · lia
  · have : p + q - 1 ≤ (a + b + m - 1) / m := by
      rw [Nat.le_div_iff_mul_le (by lia), Nat.sub_mul, Nat.add_mul, Nat.one_mul]
      lia
    lia

/--
The inverse transform of the values of `Z` gives `2ᵏ Z`: when `C j ≡ Z(ωʲ)` for `j < 2ᵏ`, with
`ω = 2ᵉ` and `ω' = 2^e'` inverses modulo `F`, then `C(ω'ˡ) ≡ 2ᵏ Z_l`.
-/
private theorem inverse_values (F k e e' : Nat) (hk : 1 ≤ k)
    (hw : (2 ^ (e * 2 ^ (k - 1)) + 1) % F = 0) (hww : (2 ^ e * 2 ^ e') % F = 1 % F)
    (Z C : List Nat) (hZ : Z.length ≤ 2 ^ k) (hC : C.length = 2 ^ k)
    (hCv : ∀ j < 2 ^ k, C.getD j 0 % F = polyVal (2 ^ (e * j)) Z % F) (l : Nat) (hl : l < 2 ^ k) :
    polyVal (2 ^ (e' * l)) C % F = (2 ^ k * Z.getD l 0) % F := by
  rw [polyVal_eq_sumRange _ C (2 ^ k) (by lia)]
  rw [sumRange_mod (g := fun j => sumRange (fun i => Z.getD i 0 * (2 ^ e) ^ (i * j)) (2 ^ k) *
      (2 ^ e') ^ (j * l)) (fun j hj => by
    rw [Nat.mul_mod, hCv j hj, ← Nat.mul_mod, polyVal_eq_sumRange _ Z (2 ^ k) hZ]
    congr 2
    · exact sumRange_congr fun i _ => by rw [← Nat.pow_mul, ← Nat.pow_mul, Nat.mul_comm i j,
        Nat.mul_assoc]
    · rw [← Nat.pow_mul, ← Nat.pow_mul, Nat.mul_comm j l, Nat.mul_assoc])]
  exact inverse_mod (2 ^ e) (2 ^ e') F k hk (by rw [← Nat.pow_mul]; exact hw) hww
    (fun i => Z.getD i 0) l hl

public theorem fftMulAt_spec (a b : UInt32Array.Slice) (k m n : Nat) (hk : 1 ≤ k) (hn : 1 ≤ n)
    (hm : 1 ≤ m) (hmn : m ≤ n) (hdiv : 2 ^ k ∣ 64 * n) (ha : 1 ≤ a.size) (hb : 1 ≤ b.size)
    (hpc : (a.size + m - 1) / m + (b.size + m - 1) / m ≤ 2 ^ k + 1)
    (hbits : 2 ^ k * 2 ^ (64 * m) ≤ 2 ^ (32 * n)) (hsmall : 2 * n + 2 < a.size + b.size)
    (mulRec : (x y : UInt32Array.Slice) → x.size + y.size < a.size + b.size → UInt32Array)
    (hrec : ∀ x y h, (mulRec x y h).size = x.size + y.size ∧
      toNat (mulRec x y h) = toNat x * toNat y) :
    (fftMulAt a b k m n mulRec).size = a.size + b.size ∧
      toNat (fftMulAt a b k m n mulRec) = toNat a * toNat b := by
  have hFpos : 0 < fermat n := by simp [fermat]
  simp only [fftMulAt]
  generalize hK : 2 ^ k = K at *
  have hK1 : 2 ≤ K := by
    rw [← hK]; have := Nat.pow_le_pow_right (show 0 < 2 by decide) hk; simpa using this
  generalize hla : (a.size + m - 1) / m = la at hpc
  generalize hlb : (b.size + m - 1) / m = lb at hpc
  have hla1 : 1 ≤ la := by rw [← hla, Nat.le_div_iff_mul_le (by lia)]; lia
  have hlb1 : 1 ≤ lb := by rw [← hlb, Nat.le_div_iff_mul_le (by lia)]; lia
  have hlaK : la ≤ K := by lia
  have hlbK : lb ≤ K := by lia
  -- The pieces cover the numbers.
  have cover : ∀ x l, (x + m - 1) / m = l → x ≤ 0 + l * m := fun x l hl => by
    have h1 := Nat.div_add_mod (x + m - 1) m
    have h2 := Nat.mod_lt (x + m - 1) (show 0 < m by lia)
    rw [hl, Nat.mul_comm] at h1
    lia
  have hacov := cover _ _ hla
  have hbcov := cover _ _ hlb
  -- The values of the pieces.
  have hKk : K = 2 * 2 ^ (k - 1) := by
    have : 2 ^ k = 2 ^ (k - 1) * 2 := by rw [← Nat.pow_succ]; congr 1; lia
    lia
  have hAval : toNat a = polyVal (2 ^ (32 * m)) (pieceList a m 0 la) := by
    rw [← toNat_eq_polyVal_pieceList a m 0 la hacov, toNat_slice_from a 0 (by lia)]; simp
  have hBval : toNat b = polyVal (2 ^ (32 * m)) (pieceList b m 0 lb) := by
    rw [← toNat_eq_polyVal_pieceList b m 0 lb hbcov, toNat_slice_from b 0 (by lia)]; simp
  generalize hA : pieceList a m 0 la = A at hAval
  generalize hB : pieceList b m 0 lb = B at hBval
  have hfull : ∀ (s : UInt32Array.Slice) l (L : List Nat), s.size ≤ 0 + l * m → l ≤ K →
      pieceList s m 0 l = L → ∀ t, polyVal t (vals (pieceArrays s m n 0 K)) = polyVal t L := by
    intro s l L hs hl hL t
    rw [vals_pieceArrays, show K = l + (K - l) by lia, pieceList_append, polyVal_append,
      polyVal_zeros _ _ (pieceList_zero s m _ _ hs), Nat.mul_zero, Nat.add_zero, hL]
  have hfa := hfull a la A hacov hlaK hA
  have hfb := hfull b lb B hbcov hlbK hB
  -- The forward transforms.
  have he : 64 * n / K * 2 ^ (k - 1) = 32 * n := by
    have := Nat.div_mul_cancel hdiv
    generalize 64 * n / K = e at this ⊢
    rw [hKk, Nat.mul_left_comm] at this
    lia
  have hw : (2 ^ (64 * n / K * 2 ^ (k - 1)) + 1) % fermat n = 0 := by
    rw [he]; exact Nat.mod_self _
  obtain ⟨lfa, rfa, vfa⟩ := transform_spec (fermatMod n) hn k (64 * n / K) (pieceArrays a m n 0 K)
    (by rw [length_pieceArrays, hK]) (isRes_pieceArrays a m n 0 K hmn) (fun _ => hw)
  obtain ⟨lfb, rfb, vfb⟩ := transform_spec (fermatMod n) hn k (64 * n / K) (pieceArrays b m n 0 K)
    (by rw [length_pieceArrays, hK]) (isRes_pieceArrays b m n 0 K hmn) (fun _ => hw)
  rw [hK] at lfa lfb rfa rfb vfa vfb
  generalize 64 * n / K = e at *
  generalize transform (fermatMod n) k e (pieceArrays a m n 0 K) = FA at *
  generalize transform (fermatMod n) k e (pieceArrays b m n 0 K) = FB at *
  -- The pointwise products are the values of `Z = A B`.
  generalize hZ : polyMul A B = Z
  have hres : ∀ x : UInt32Array, IsRes n x → toNat x ≤ 2 ^ (32 * n) := fun x hx => by
    have := hx.2; simp only [fermat] at this; lia
  have hcond : ∀ j < K, (FA.getD j default).toSlice.size + (FB.getD j default).toSlice.size <
      a.size + b.size := fun j hj => by
    simp only [UInt32Array.size_toSlice, (rfa j hj).1, (rfb j hj).1]; lia
  have hfc : ∀ j (hj : j < K), ((List.range K).map fun j =>
      if h : (FA.getD j default).toSlice.size + (FB.getD j default).toSlice.size <
        a.size + b.size then normProd (fermatMod n) (mulRec (FA.getD j default)
          (FB.getD j default) h)
      else FA.getD j default).getD j default =
        normProd (fermatMod n) (mulRec (FA.getD j default) (FB.getD j default)
          (hcond j hj)) := fun j hj => by
    rw [getD_of_lt _ _ _ (by simp; lia), List.getElem_map, List.getElem_range,
      dite_eq_left (hcond j hj)]
  have lFC : ((List.range K).map fun j =>
      if h : (FA.getD j default).toSlice.size + (FB.getD j default).toSlice.size <
        a.size + b.size then normProd (fermatMod n) (mulRec (FA.getD j default)
          (FB.getD j default) h)
      else FA.getD j default).length = K := by simp
  generalize ((List.range K).map fun j =>
      if h : (FA.getD j default).toSlice.size + (FB.getD j default).toSlice.size <
        a.size + b.size then normProd (fermatMod n) (mulRec (FA.getD j default)
          (FB.getD j default) h)
      else FA.getD j default) = FC at *
  have vFC : ∀ j < K, IsRes n (FC.getD j default) ∧
      toNat (FC.getD j default) = polyVal (2 ^ (e * j)) Z % fermat n := fun j hj => by
    rw [hfc j hj]
    obtain ⟨hps₀, hpv⟩ := hrec _ _ (hcond j hj)
    have hps : (mulRec (FA.getD j default) (FB.getD j default) (hcond j hj)).size = 2 * n + 2 := by
      rw [hps₀]; simp only [UInt32Array.size_toSlice, (rfa j hj).1, (rfb j hj).1]; lia
    have hval : toNat (mulRec (FA.getD j default) (FB.getD j default) (hcond j hj)) ≤
        2 ^ (32 * n) * 2 ^ (32 * n) := by
      rw [hpv]; exact Nat.mul_le_mul (hres _ (rfa j hj)) (hres _ (rfb j hj))
    refine ⟨⟨size_normProd (fermatMod n) _, toNat_normProd_lt (fermatMod n) _ hn (by lia)
      (by lia) hval⟩, ?_⟩
    rw [toNat_normProd (fermatMod n) _ hn (by lia) (by lia) hval, hpv, vfa j hj, vfb j hj, hfa, hfb,
      ← Nat.mul_mod, ← polyVal_polyMul, hZ]
  -- The inverse transform, with `ω⁻¹ = 2^(64 n - e)`.
  have hP := Nat.two_pow_pos (k - 1)
  have heK : e * K = 64 * n := by rw [hKk, Nat.mul_left_comm, he]; lia
  have hw2 : (2 ^ ((64 * n - e) * 2 ^ (k - 1)) + 1) % fermat n = 0 := by
    have hexp : (64 * n - e) * 2 ^ (k - 1) = 32 * n * (K - 1) := by
      rw [Nat.sub_mul, he, Nat.mul_sub, Nat.mul_one, hKk]
      rw [show 64 * n * 2 ^ (k - 1) = 32 * n * (2 * 2 ^ (k - 1)) by
        rw [← Nat.mul_assoc, Nat.mul_comm (32 * n) 2, ← Nat.mul_assoc]]
    rw [hexp, Nat.pow_mul]
    exact pow_odd_mod (by simp [fermat]) (by rw [hKk]; lia)
  have hFCres : ∀ x ∈ FC, IsRes n x :=
    forall_mem_of_getD FC default (fun j hj => (vFC j (by lia)).1)
  obtain ⟨lG, rG, vG⟩ := transform_spec (fermatMod n) hn k (64 * n - e) FC (by rw [lFC, hK]) hFCres
    (fun _ => hw2)
  rw [hK] at lG rG vG
  generalize transform (fermatMod n) k (64 * n - e) FC = G at *
  -- `Z` has at most `K` coefficients, each below `F`.
  have hlenZ : Z.length ≤ la + lb - 1 := by
    rw [← hZ, ← hA]
    refine Nat.le_trans (length_polyMul _ _ ?_) ?_
    · rw [← hB]; intro h; have := congrArg List.length h; simp [length_pieceList] at this; lia
    · rw [length_pieceList, ← hB, length_pieceList]; exact Nat.le_refl _
  have hZlt : ∀ l, Z.getD l 0 < fermat n := fun l => by
    rw [← hZ]
    have h₁ := getD_polyMul_le A B (2 ^ (32 * m) - 1) (2 ^ (32 * m) - 1)
      (fun c hc => by rw [← hA] at hc; have := pieceList_lt a m 0 la c hc; lia)
      (fun c hc => by rw [← hB] at hc; have := pieceList_lt b m 0 lb c hc; lia) l
    have hAl : A.length = la := by rw [← hA, length_pieceList]
    rw [hAl] at h₁
    have h₂ : (2 ^ (32 * m) - 1) * (2 ^ (32 * m) - 1) < 2 ^ (64 * m) := by
      rw [show 64 * m = 32 * m + 32 * m by lia, Nat.pow_add]
      have := Nat.two_pow_pos (32 * m)
      exact Nat.mul_lt_mul'' (by lia) (by lia)
    have h₃ : la * ((2 ^ (32 * m) - 1) * (2 ^ (32 * m) - 1)) ≤ K * 2 ^ (64 * m) :=
      Nat.mul_le_mul hlaK (Nat.le_of_lt h₂)
    simp only [fermat]; lia
  -- The inverse values are `K Z_l`, and the scaled ones `Z_l`.
  have hww : (2 ^ e * 2 ^ (64 * n - e)) % fermat n = 1 % fermat n := by
    rw [← Nat.pow_add, show e + (64 * n - e) = 64 * n by
      have : e ≤ 64 * n := by rw [← heK]; exact Nat.le_mul_of_pos_right _ (by lia)
      lia]
    exact two_pow_period n
  have hG : ∀ l < K, toNat (G.getD l default) = (K * Z.getD l 0) % fermat n := fun l hl => by
    rw [vG l hl, ← hK]
    exact inverse_values (fermat n) k e (64 * n - e) hk (by rw [he]; exact Nat.mod_self _) hww
      Z (vals FC) (by rw [hK]; lia) (by rw [vals, List.length_map, lFC, hK])
      (fun j hj => by
        rw [vals, List.getD_eq_getElem?_getD, List.getElem?_map,
          List.getElem?_eq_getElem (by rw [lFC, ← hK]; exact hj)]
        simp only [Option.map_some, Option.getD_some]
        rw [← getD_of_lt _ _ default (by rw [lFC, ← hK]; exact hj),
          (vFC j (by rw [← hK]; exact hj)).2, Nat.mod_mod]) l (by rw [hK]; exact hl)
  have hkn : k ≤ 64 * n := by
    have h₁ : k < 2 ^ k := Nat.lt_two_pow_self
    have h₂ : K ≤ 64 * n := Nat.le_of_dvd (by lia) hdiv
    lia
  have hC : ∀ l < K, toNat ((G.map fun z => mulPow2I (fermatMod n) z (64 * n - k)).getD l default) =
      Z.getD l 0 := fun l hl => by
    rw [getD_of_lt _ _ _ (by simp; lia), List.getElem_map, ← getD_of_lt _ _ default (by lia),
      toNat_mulPow2I (fermatMod n) _ _ hn (rG l hl).1 (rG l hl).2, hG l hl, Nat.mod_mul_mod, ← hK,
      Nat.mul_comm (2 ^ k), Nat.mul_assoc, ← Nat.pow_add, show k + (64 * n - k) = 64 * n by lia,
      Nat.mul_mod, two_pow_period, ← Nat.mul_mod, Nat.mul_one, Nat.mod_eq_of_lt (hZlt l)]
  have lC : (G.map fun z => mulPow2I (fermatMod n) z (64 * n - k)).length = K := by simp [lG]
  generalize G.map (fun z => mulPow2I (fermatMod n) z (64 * n - k)) = C at *
  -- The assembly of the first `⌈(a + b) / m⌉` coefficients.
  have hceil := ceil_add_ceil a.size b.size m hm
  rw [hla, hlb] at hceil
  generalize hL : (a.size + b.size + m - 1) / m = L at *
  have hLm : L * m ≤ a.size + b.size + m - 1 := by rw [← hL]; exact Nat.div_mul_le_self _ _
  have lCT : (C.take L).length = min L K := by simp [lC]
  have hZL : Z.length ≤ min L K := by lia
  have hcs : (C.take L).map (fun c : UInt32Array => toNat c) =
      (List.range (min L K)).map fun l => Z.getD l 0 := by
    apply List.ext_getElem (by simp [lC])
    intro i h₁ h₂
    simp only [List.length_map, lCT] at h₁
    rw [List.getElem_map, List.getElem_take, List.getElem_map, List.getElem_range,
      ← getD_of_lt _ _ default (by lia), hC i (by lia)]
  have hpoly : polyVal (2 ^ (32 * m)) ((List.range (min L K)).map fun l => Z.getD l 0) =
      toNat a * toNat b := by
    rw [polyVal_eq_sumRange _ _ (min L K) (by simp), hAval, hBval, ← polyVal_polyMul, hZ,
      polyVal_eq_sumRange _ Z (min L K) hZL]
    exact sumRange_congr fun i hi => by
      rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hi]; rfl
  have hlt : toNat a * toNat b < 2 ^ (32 * (a.size + b.size)) := by
    rw [Nat.mul_add, Nat.pow_add]
    exact Nat.mul_lt_mul'' (toNat_lt a) (toNat_lt b)
  have key := assemble_spec (a.size + b.size) m (C.take L) _
    (by rw [lCT]; have : min L K * m ≤ L * m := Nat.mul_le_mul_right _ (by lia)
        rw [Nat.mul_comm]; lia) hcs (by rw [hpoly]; exact hlt)
  rw [hpoly] at key
  exact key

/--
The parameters of `fftMulAt` for `2ᵏ` pieces and `total` limbs: pieces of
`m = ⌈total / (2ᵏ - 1)⌉` limbs, so that the pieces of `a` and `b` together are at most `2ᵏ + 1`,
and residues of `n ≥ 2 m + 1` limbs, a multiple of `2ᵏ / 64`, so that `2ᵏ` divides `64 n` and every
coefficient of the convolution fits.
-/
public def fftParams (total k : Nat) : Nat × Nat :=
  let m := (total + 2 ^ k - 2) / (2 ^ k - 1)
  let q := max 1 (2 ^ k / 64)
  (m, (2 * m + 1 + q - 1) / q * q)

/--
The product `a * b` by the FFT with `2ᵏ` pieces, the parameters of `fftParams`, and `mulRec` for
the pointwise products; schoolbook when the parameters do not suit the sizes, which the
dispatcher avoids.
-/
public def fftMul (a b : UInt32Array.Slice) (k : Nat)
    (mulRec : (x y : UInt32Array.Slice) → x.size + y.size < a.size + b.size → UInt32Array) :
    UInt32Array :=
  let p := fftParams (a.size + b.size) k
  if 1 ≤ k ∧ k ≤ 32 ∧ 1 ≤ p.2 ∧ 1 ≤ p.1 ∧ p.1 ≤ p.2 ∧ (64 * p.2) % 2 ^ k = 0 ∧ 1 ≤ a.size ∧
      1 ≤ b.size ∧ (a.size + p.1 - 1) / p.1 + (b.size + p.1 - 1) / p.1 ≤ 2 ^ k + 1 ∧
      k + 64 * p.1 ≤ 32 * p.2 ∧ 2 * p.2 + 2 < a.size + b.size then
    fftMulAt a b k p.1 p.2 mulRec
  else
    mulBasecase a b

/-- The number of pieces, `2ᵏ`, for `total` limbs: `k = ⌊log₂ total⌋ / 2 + 1`, measured best. -/
public def fftK (total : Nat) : Nat := min 32 (Nat.log2 total / 2 + 1)

public theorem fftMul_spec (a b : UInt32Array.Slice) (k : Nat)
    (mulRec : (x y : UInt32Array.Slice) → x.size + y.size < a.size + b.size → UInt32Array)
    (hrec : ∀ x y h, (mulRec x y h).size = x.size + y.size ∧
      toNat (mulRec x y h) = toNat x * toNat y) :
    (fftMul a b k mulRec).size = a.size + b.size ∧
      toNat (fftMul a b k mulRec) = toNat a * toNat b := by
  generalize hp : fftParams (a.size + b.size) k = p
  by_cases h : 1 ≤ k ∧ k ≤ 32 ∧ 1 ≤ p.2 ∧ 1 ≤ p.1 ∧ p.1 ≤ p.2 ∧ (64 * p.2) % 2 ^ k = 0 ∧
      1 ≤ a.size ∧ 1 ≤ b.size ∧ (a.size + p.1 - 1) / p.1 + (b.size + p.1 - 1) / p.1 ≤ 2 ^ k + 1 ∧
      k + 64 * p.1 ≤ 32 * p.2 ∧ 2 * p.2 + 2 < a.size + b.size
  · have e : fftMul a b k mulRec = fftMulAt a b k p.1 p.2 mulRec := by
      simp only [fftMul, hp, h, and_self, ↓reduceIte]
    obtain ⟨h₁, -, h₃, h₄, h₅, h₆, h₇, h₈, h₉, h₁₀, h₁₁⟩ := h
    rw [e]
    exact fftMulAt_spec a b k p.1 p.2 h₁ h₃ h₄ h₅ (Nat.dvd_of_mod_eq_zero h₆) h₇ h₈ h₉
      (by rw [← Nat.pow_add]; exact Nat.pow_le_pow_right (by decide) (by lia)) h₁₁ mulRec hrec
  · have e : fftMul a b k mulRec = mulBasecase a b := by
      simp only [fftMul, hp, h, ↓reduceIte]
    rw [e]
    exact ⟨size_mulBasecase a b, toNat_mulBasecase a b⟩

/-! ## Squaring -/

/-- `fftMulAt a a` with one forward transform and squares for the pointwise products. -/
public def fftSqrAt (a : UInt32Array.Slice) (k m n : Nat)
    (sqrRec : (x : UInt32Array.Slice) → x.size < a.size → UInt32Array) : UInt32Array :=
  let M := fermatMod n
  let e := 64 * n / 2 ^ k
  let fa := transform M k e (pieceArrays a m n 0 (2 ^ k))
  let fc := (List.range (2 ^ k)).map fun j =>
    let x := fa.getD j default
    if h : x.toSlice.size + x.toSlice.size < a.size + a.size then
      normProd M (sqrRec x (by lia))
    else x
  let c := (transform M k (64 * n - e) fc).map fun z => mulPow2I M z (64 * n - k)
  assembleFrom (.replicate (a.size + a.size) 0) 0 m (c.take ((a.size + a.size + m - 1) / m))

/-- The products of `fftMulAt a a` that come from `fftSqrAt`: squares of equal arguments. -/
def sqrPair (a : UInt32Array.Slice)
    (sqrRec : (x : UInt32Array.Slice) → x.size < a.size → UInt32Array)
    (x y : UInt32Array.Slice) (h : x.size + y.size < a.size + a.size) : UInt32Array :=
  if hxy : x.copy = y.copy then sqrRec x (by
    have : x.size = y.size := by
      rw [← UInt32Array.Slice.size_copy, hxy, UInt32Array.Slice.size_copy]
    lia) else mulBasecase x y

theorem fftSqrAt_eq (a : UInt32Array.Slice) (k m n : Nat)
    (sqrRec : (x : UInt32Array.Slice) → x.size < a.size → UInt32Array) :
    fftSqrAt a k m n sqrRec = fftMulAt a a k m n (sqrPair a sqrRec) := by
  simp [fftSqrAt, fftMulAt, sqrPair]

public theorem fftSqrAt_spec (a : UInt32Array.Slice) (k m n : Nat) (hk : 1 ≤ k) (hn : 1 ≤ n)
    (hm : 1 ≤ m) (hmn : m ≤ n) (hdiv : 2 ^ k ∣ 64 * n) (ha : 1 ≤ a.size)
    (hpc : (a.size + m - 1) / m + (a.size + m - 1) / m ≤ 2 ^ k + 1)
    (hbits : 2 ^ k * 2 ^ (64 * m) ≤ 2 ^ (32 * n)) (hsmall : 2 * n + 2 < a.size + a.size)
    (sqrRec : (x : UInt32Array.Slice) → x.size < a.size → UInt32Array)
    (hrec : ∀ x h, (sqrRec x h).size = x.size + x.size ∧
      toNat (sqrRec x h) = toNat x * toNat x) :
    (fftSqrAt a k m n sqrRec).size = a.size + a.size ∧
      toNat (fftSqrAt a k m n sqrRec) = toNat a * toNat a := by
  rw [fftSqrAt_eq]
  refine fftMulAt_spec a a k m n hk hn hm hmn hdiv ha ha hpc hbits hsmall _ fun x y h => ?_
  by_cases hxy : x.copy = y.copy
  · have e : sqrPair a sqrRec x y h = sqrRec x (by
        have : x.size = y.size := by
          rw [← UInt32Array.Slice.size_copy, hxy, UInt32Array.Slice.size_copy]
        lia) := by simp only [sqrPair, hxy, ↓reduceDIte]
    have hs : x.size = y.size := by
      rw [← UInt32Array.Slice.size_copy, hxy, UInt32Array.Slice.size_copy]
    have hv : toNat x = toNat y := by simp only [toNat, hxy]
    rw [e]
    obtain ⟨h₁, h₂⟩ := hrec x _
    exact ⟨by rw [h₁, hs], by rw [h₂, hv]⟩
  · have e : sqrPair a sqrRec x y h = mulBasecase x y := by simp only [sqrPair, hxy, ↓reduceDIte]
    rw [e]
    exact ⟨size_mulBasecase x y, toNat_mulBasecase x y⟩

/-- The square `a * a` by the FFT with `2ᵏ` pieces; schoolbook when the parameters do not suit. -/
public def fftSqr (a : UInt32Array.Slice) (k : Nat)
    (sqrRec : (x : UInt32Array.Slice) → x.size < a.size → UInt32Array) : UInt32Array :=
  let p := fftParams (a.size + a.size) k
  if 1 ≤ k ∧ k ≤ 32 ∧ 1 ≤ p.2 ∧ 1 ≤ p.1 ∧ p.1 ≤ p.2 ∧ (64 * p.2) % 2 ^ k = 0 ∧ 1 ≤ a.size ∧
      (a.size + p.1 - 1) / p.1 + (a.size + p.1 - 1) / p.1 ≤ 2 ^ k + 1 ∧
      k + 64 * p.1 ≤ 32 * p.2 ∧ 2 * p.2 + 2 < a.size + a.size then
    fftSqrAt a k p.1 p.2 sqrRec
  else
    mulBasecase a a

public theorem fftSqr_spec (a : UInt32Array.Slice) (k : Nat)
    (sqrRec : (x : UInt32Array.Slice) → x.size < a.size → UInt32Array)
    (hrec : ∀ x h, (sqrRec x h).size = x.size + x.size ∧
      toNat (sqrRec x h) = toNat x * toNat x) :
    (fftSqr a k sqrRec).size = a.size + a.size ∧
      toNat (fftSqr a k sqrRec) = toNat a * toNat a := by
  generalize hp : fftParams (a.size + a.size) k = p
  by_cases h : 1 ≤ k ∧ k ≤ 32 ∧ 1 ≤ p.2 ∧ 1 ≤ p.1 ∧ p.1 ≤ p.2 ∧ (64 * p.2) % 2 ^ k = 0 ∧
      1 ≤ a.size ∧ (a.size + p.1 - 1) / p.1 + (a.size + p.1 - 1) / p.1 ≤ 2 ^ k + 1 ∧
      k + 64 * p.1 ≤ 32 * p.2 ∧ 2 * p.2 + 2 < a.size + a.size
  · have e : fftSqr a k sqrRec = fftSqrAt a k p.1 p.2 sqrRec := by
      simp only [fftSqr, hp, h, and_self, ↓reduceIte]
    obtain ⟨h₁, -, h₃, h₄, h₅, h₆, h₇, h₉, h₁₀, h₁₁⟩ := h
    rw [e]
    exact fftSqrAt_spec a k p.1 p.2 h₁ h₃ h₄ h₅ (Nat.dvd_of_mod_eq_zero h₆) h₇ h₉
      (by rw [← Nat.pow_add]; exact Nat.pow_le_pow_right (by decide) (by lia)) h₁₁ sqrRec hrec
  · have e : fftSqr a k sqrRec = mulBasecase a a := by
      simp only [fftSqr, hp, h, ↓reduceIte]
    rw [e]
    exact ⟨size_mulBasecase a a, toNat_mulBasecase a a⟩

end MPN.FFT
