/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import MPN.Num

/-!
# Divide-and-conquer division

`Num.divNorm U V n k` divides `U < V βᵏ` by a normalized divisor `V` of `n` limbs, with the top bit
set, by computing the quotient in digits of at most `⌊n / 2⌋` limbs from the top down, like
Algorithm D in base `βˢ`. This is the scheme of Burnikel and Ziegler and of GMP's
`mpn_dcpi1_div_qr`, written recursively: the top digit of `s` limbs is `D = ⌊W / V⌋ < βˢ`, where
`W = ⌊U / βʲ⌋` and `j = k - s`. It is estimated from the top `2 s` limbs `Wₕ` of `W` and the top `s`
limbs `Vₕ` of `V` as `⌊Wₕ / Vₕ⌋`, a recursive division, or `βˢ - 1` when that would not be a
digit; the estimate is never too small, and since `V` is normalized it is at most two too large.
Like GMP, the step keeps the remainder `R₀` of the recursive division: with `W = Wₕ B + W_lo` and
`V = Vₕ B + V_lo` for `B = β^(n-s)`, `W - Q₀ V = (R₀ B + W_lo) - Q₀ V_lo`, so it multiplies `Q₀`
by the low `n - s` limbs of `V` only, and `dcFix` adds `V` back while the difference is negative.
The rest, `U - D V βʲ < V βʲ`, is divided recursively. Division then costs `O(M(n) log n)`.

`Num.divMod a b` normalizes `b` and calls `divNorm` from `dcThreshold` limbs in `b`, and
`divModBase` below.
-/

open ScalarArray UInt64Array

namespace MPN.Num

/-- The number of limbs of the divisor from which `divMod` divides by divide and conquer. -/
public def dcThreshold : Nat := 512

/-- The value `1`. -/
public def one : UInt64Array := UInt64Array.replicate 1 1

private theorem toNat_one : one.toNat = 1 := by simp [one, toNat_eq_valAt]

private theorem size_one : one.size = 1 := by simp [one]

/-- `βˢ - 1`, in `s` limbs. -/
public def allOnes (s : Nat) : UInt64Array := UInt64Array.replicate s 0xFFFFFFFFFFFFFFFF

private theorem valAt_allOnes (s lo m : Nat) (h : lo + m ≤ s) :
    (allOnes s).valAt lo m = 2 ^ (64 * m) - 1 := by
  induction m generalizing lo with
  | zero => simp
  | succ m ih =>
    have hx : (allOnes s)[lo]!.toNat = 2 ^ 64 - 1 := by
      rw [allOnes, getElem!_eq_getElem!_data, data_replicate]
      simp [show lo < s by lia]
    rw [valAt_succ, ih (lo + 1) (by lia), hx]
    have := Nat.one_le_two_pow (n := 64 * m)
    rw [Nat.mul_succ, Nat.pow_add, Nat.mul_sub, Nat.mul_one]
    lia

private theorem toNat_allOnes (s : Nat) : (allOnes s).toNat = 2 ^ (64 * s) - 1 := by
  rw [toNat_eq_valAt, show (allOnes s).size = s by simp [allOnes]]
  exact valAt_allOnes s 0 s (by lia)

private theorem size_allOnes (s : Nat) : (allOnes s).size = s := by simp [allOnes]

/-! ## The correction -/

/--
Adds `V` to `T` and decreases `Q` while `T < P`, keeping `n + 1` limbs of `T`: with the invariant
`T + Q V = W + P`, it ends with `Q = ⌊W / V⌋` and `T = W mod V + P`.
-/
public def dcFix (V P Q T : UInt64Array) (n : Nat) : UInt64Array × UInt64Array :=
  if _h : Q.size + P.size + T.size + V.size + n + 4 < USize.size ∧ lt T P = true ∧
      lt Q one = false then
    dcFix V P (sub Q one) (low (add T V) (n + 1)) n
  else (Q, T)
termination_by Q.toNat
decreasing_by
  obtain ⟨h₁, -, h₃⟩ := _h
  have : ¬Q.toNat < 1 := by
    rw [← toNat_one, ← lt_iff _ _ (by rw [size_one]; lia)]; simp [h₃]
  rw [toNat_sub _ _ (by rw [toNat_one]; lia) (by lia) (by rw [size_one]; lia), toNat_one]
  lia

private theorem dcFix_spec (V P Q T : UInt64Array) (n W : Nat) (hV : 0 < V.toNat)
    (hVn : V.toNat < 2 ^ (64 * n)) (hPn : P.toNat ≤ 2 ^ (64 * n)) (hTs : T.size ≤ n + 1)
    (hS : Q.size + P.size + (n + 1) + V.size + n + 4 < USize.size)
    (hinv : T.toNat + Q.toNat * V.toNat = W + P.toNat) (hQ : W / V.toNat ≤ Q.toNat) :
    (dcFix V P Q T n).1.size = Q.size ∧ (dcFix V P Q T n).2.size ≤ n + 1 ∧
      (dcFix V P Q T n).1.toNat = W / V.toNat ∧
      (dcFix V P Q T n).2.toNat = W % V.toNat + P.toNat := by
  induction Q, T using dcFix.induct V P n with
  | case1 Q T h ih =>
    rw [dcFix, dite_eq_left_of_eq_true (eq_true h)]
    obtain ⟨-, h₂, h₃⟩ := h
    rw [lt_iff _ _ (by lia)] at h₂
    have hq1 : ¬Q.toNat < 1 := by
      rw [← toNat_one, ← lt_iff _ _ (by rw [size_one]; lia)]; simp [h₃]
    have hlt : W / V.toNat < Q.toNat := by
      refine Nat.lt_of_not_le fun hle => ?_
      have := Nat.div_mul_le_self W V.toNat
      have := Nat.mul_le_mul_right V.toNat hle
      have := Nat.lt_mul_div_succ W hV
      have := Nat.mul_le_mul_left V.toNat hle
      lia
    have hQ' : (sub Q one).toNat = Q.toNat - 1 := by
      rw [toNat_sub _ _ (by rw [toNat_one]; lia) (by lia) (by rw [size_one]; lia), toNat_one]
    have hT' : (low (add T V) (n + 1)).toNat = T.toNat + V.toNat := by
      rw [toNat_low _ _ (by rw [size_add]; lia), toNat_add _ _ (by lia), Nat.mod_eq_of_lt]
      rw [show 64 * (n + 1) = 64 * n + 64 by lia, Nat.pow_add]
      have := Nat.two_pow_pos (64 * n)
      lia
    obtain ⟨i₁, i₂, i₃, i₄⟩ := ih (by rw [size_low _ _ (by rw [size_add]; lia)]; lia)
      (by rw [size_sub]; lia) (by
        rw [hQ', hT', Nat.sub_mul, Nat.one_mul]
        have : V.toNat ≤ Q.toNat * V.toNat := Nat.le_mul_of_pos_left _ (by lia)
        lia) (by rw [hQ']; lia)
    rw [size_sub] at i₁
    exact ⟨i₁, i₂, i₃, i₄⟩
  | case2 Q T h =>
    rw [dcFix, dite_eq_right_of_eq_false (eq_false h)]
    -- The loop stopped with `T ≥ P`, so `Q V ≤ W` and `Q = ⌊W / V⌋`.
    have hle : ¬T.toNat < P.toNat := by
      intro hlt
      apply h
      refine ⟨by lia, (lt_iff _ _ (by lia)).2 hlt, ?_⟩
      cases hc : lt Q one
      · rfl
      · rw [lt_iff _ _ (by rw [size_one]; lia), toNat_one] at hc
        have : Q.toNat = 0 := by lia
        rw [this, Nat.zero_mul] at hinv
        lia
    have hQV : Q.toNat * V.toNat ≤ W := by lia
    have : Q.toNat ≤ W / V.toNat := (Nat.le_div_iff_mul_le hV).2 hQV
    have hQe : Q.toNat = W / V.toNat := by lia
    refine ⟨rfl, hTs, hQe, ?_⟩
    have := Nat.div_add_mod W V.toNat
    rw [hQe] at hinv
    rw [Nat.mul_comm] at this
    lia

/-! ## The recursion -/

/-- The size of the top digit: `k mod m`, or `m` when `m` divides `k`. -/
@[inline] public def topDigit (k m : Nat) : Nat := if k % m = 0 then m else k % m

private theorem topDigit_spec (k m : Nat) (hm : 1 ≤ m) (hk : 1 ≤ k) :
    1 ≤ topDigit k m ∧ topDigit k m ≤ m ∧ topDigit k m ≤ k := by
  have := Nat.mod_lt k (show 0 < m by lia)
  have := Nat.mod_le k m
  unfold topDigit
  split
  · refine ⟨hm, Nat.le_refl _, ?_⟩
    rename_i h
    have := Nat.div_add_mod k m
    rw [h, Nat.add_zero] at this
    have : 1 ≤ k / m := by
      rcases Nat.eq_zero_or_pos (k / m) with h0 | h0
      · rw [h0] at this; lia
      · exact h0
    have := Nat.mul_le_mul_left m this
    lia
  · lia

/--
`(U / V, U % V)` in `k` and `n` limbs, for `V` of `n` limbs with its top bit set and `U < V βᵏ`:
one digit of `s ≤ ⌊n / 2⌋` limbs from the top, estimated by a recursive division and corrected
by `dcFix`, then the rest recursively; `divModBase` below `dcThreshold` limbs.
-/
public def divNorm (U V : UInt64Array) (n k : Nat) : UInt64Array × UInt64Array :=
  if h : n < dcThreshold ∨ k = 0 then
    let d := divModBase U V
    (low d.1 k, low d.2 n)
  else
    let s := topDigit k (n / 2)
    let j := k - s
    let W := low (shr U (64 * j)) (n + s)
    let Wh := shr W (64 * (n - s))
    let Vh := shr V (64 * (n - s))
    let e := if lt (shr Wh (64 * s)) Vh then divNorm Wh Vh s s
      else (allOnes s, add (sub Wh (shl Vh (64 * s))) Vh)
    let P := mul e.1 (low V (n - s))
    let f := dcFix V P e.1 (low (add (shl e.2 (64 * (n - s))) (low W (n - s))) (n + 1)) n
    let U' := add (low U j) (shl (sub f.2 P) (64 * j))
    let r := divNorm (low U' (n + j)) V n j
    (low (add (shl f.1 (64 * j)) r.1) k, r.2)
termination_by (n, k)
decreasing_by
  all_goals
    have ht := topDigit_spec k (n / 2) (by unfold dcThreshold at h; lia) (by lia)
  · exact Prod.Lex.left _ _ (by unfold dcThreshold at h; lia)
  · exact Prod.Lex.right _ (by lia)

/-- The top limbs bound the digit: `D V ≤ W` gives `D Vₕ ≤ Wₕ` for the parts above `P`. -/
private theorem dc_est {D V W P : Nat} (hP : 0 < P) (hD : D * V ≤ W) :
    D * (V / P) ≤ W / P := by
  have h₁ : P * (D * (V / P)) ≤ D * V := by
    rw [Nat.mul_left_comm]
    exact Nat.mul_le_mul_left D (Nat.mul_div_le V P)
  have h₂ := Nat.lt_mul_div_succ W hP
  have : P * (D * (V / P)) < P * (W / P + 1) := by lia
  have := Nat.lt_of_mul_lt_mul_left this
  lia

set_option maxHeartbeats 2000000 in
private theorem divNorm_spec (n : Nat) : ∀ (k : Nat) (U V : UInt64Array), 1 ≤ n →
    V.size = n → 2 ^ (64 * n - 1) ≤ V.toNat → U.size ≤ n + k →
    U.toNat < V.toNat * 2 ^ (64 * k) → 8 * (n + k) + 32 < USize.size →
    (divNorm U V n k).1.size ≤ k ∧ (divNorm U V n k).2.size ≤ n ∧
      (divNorm U V n k).1.toNat = U.toNat / V.toNat ∧
      (divNorm U V n k).2.toNat = U.toNat % V.toNat := by
  induction n using Nat.strongRecOn with
  | ind n ihn =>
  intro k
  induction k using Nat.strongRecOn with
  | ind k ihk =>
  intro U V hn hVs hV hUs hUV hS
  have hV0 : 0 < V.toNat := Nat.lt_of_lt_of_le (Nat.two_pow_pos _) hV
  have hVlt : V.toNat < 2 ^ (64 * n) := by
    rw [toNat_eq_valAt, hVs]; exact valAt_lt ..
  have hq : U.toNat / V.toNat < 2 ^ (64 * k) :=
    (Nat.div_lt_iff_lt_mul hV0).2 (by rw [Nat.mul_comm]; exact hUV)
  rw [divNorm]
  split
  · dsimp only
    clear ihn ihk
    obtain ⟨d₁, d₂⟩ := toNat_divModBase U V hV0 (by lia)
    obtain ⟨e₁, e₂⟩ := size_divModBase U V (by lia)
    refine ⟨by rw [size_low _ _ (by lia)]; lia, by rw [size_low _ _ (by lia)]; lia, ?_, ?_⟩
    · rw [toNat_low _ _ (by lia), d₁, Nat.mod_eq_of_lt hq]
    · rw [toNat_low _ _ (by lia), d₂,
        Nat.mod_eq_of_lt (Nat.lt_trans (Nat.mod_lt _ hV0) hVlt)]
  · rename_i h
    dsimp only
    have hm : 1 ≤ n / 2 := by unfold dcThreshold at h; lia
    obtain ⟨hs1, hsm, hsk⟩ := topDigit_spec k (n / 2) hm (by lia)
    generalize topDigit k (n / 2) = s at hs1 hsm hsk ⊢
    have hsn : s < n := by lia
    generalize hj : k - s = j
    have hkj : k = j + s := by lia
    subst hkj
    have hjk : j < j + s := by lia
    -- The window `W = U / βʲ` of `n + s` limbs.
    have hPk : 2 ^ (64 * (j + s)) = 2 ^ (64 * s) * 2 ^ (64 * j) := by
      rw [← Nat.pow_add]; congr 1; lia
    have hWlt : U.toNat / 2 ^ (64 * j) < V.toNat * 2 ^ (64 * s) :=
      (Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _)).2 (by rw [Nat.mul_assoc, ← hPk]; exact hUV)
    have hWs : (low (shr U (64 * j)) (n + s)).size ≤ n + s := by
      rw [size_low _ _ (by rw [size_shr]; lia)]; lia
    have hWv : (low (shr U (64 * j)) (n + s)).toNat = U.toNat / 2 ^ (64 * j) := by
      rw [toNat_low _ _ (by rw [size_shr]; lia), toNat_shr _ _ (by lia), Nat.mod_eq_of_lt]
      calc U.toNat / 2 ^ (64 * j) < V.toNat * 2 ^ (64 * s) := hWlt
        _ ≤ 2 ^ (64 * n) * 2 ^ (64 * s) := Nat.mul_le_mul_right _ (Nat.le_of_lt hVlt)
        _ = 2 ^ (64 * (n + s)) := by rw [← Nat.pow_add]; congr 1; lia
    generalize low (shr U (64 * j)) (n + s) = W at hWs hWv ⊢
    rw [← hWv] at hWlt
    -- The top limbs `Wₕ` and `Vₕ`.
    have hPn : 0 < 2 ^ (64 * (n - s)) := Nat.two_pow_pos _
    have hWhs : (shr W (64 * (n - s))).size ≤ s + s := by rw [size_shr]; lia
    have hWhv : (shr W (64 * (n - s))).toNat = W.toNat / 2 ^ (64 * (n - s)) :=
      toNat_shr _ _ (by lia)
    have hVhs : (shr V (64 * (n - s))).size = s := by rw [size_shr]; lia
    have hVhv : (shr V (64 * (n - s))).toNat = V.toNat / 2 ^ (64 * (n - s)) :=
      toNat_shr _ _ (by lia)
    have hVh : 2 ^ (64 * s - 1) ≤ V.toNat / 2 ^ (64 * (n - s)) := by
      apply (Nat.le_div_iff_mul_le hPn).2
      rw [← Nat.pow_add, show 64 * s - 1 + 64 * (n - s) = 64 * n - 1 by lia]
      exact hV
    have hD : W.toNat / V.toNat * (V.toNat / 2 ^ (64 * (n - s))) ≤
        W.toNat / 2 ^ (64 * (n - s)) := dc_est hPn (Nat.div_mul_le_self _ _)
    have hDs : W.toNat / V.toNat < 2 ^ (64 * s) :=
      (Nat.div_lt_iff_lt_mul hV0).2 (by rw [Nat.mul_comm]; exact hWlt)
    -- The estimate `Q₀` and the remainder `R₀ = Wₕ - Q₀ Vₕ`; `Q₀` is never too small.
    have hVhlt : V.toNat / 2 ^ (64 * (n - s)) < 2 ^ (64 * s) := by
      apply (Nat.div_lt_iff_lt_mul hPn).2
      rw [← Nat.pow_add, show 64 * s + 64 * (n - s) = 64 * n by lia]; exact hVlt
    have hWh : W.toNat / 2 ^ (64 * (n - s)) <
        (V.toNat / 2 ^ (64 * (n - s)) + 1) * 2 ^ (64 * s) := by
      apply (Nat.div_lt_iff_lt_mul hPn).2
      have := Nat.lt_mul_div_succ V.toNat hPn
      calc W.toNat < V.toNat * 2 ^ (64 * s) := hWlt
        _ ≤ 2 ^ (64 * (n - s)) * (V.toNat / 2 ^ (64 * (n - s)) + 1) * 2 ^ (64 * s) :=
            Nat.mul_le_mul_right _ (Nat.le_of_lt this)
        _ = _ := by rw [Nat.mul_comm (2 ^ (64 * (n - s))), Nat.mul_assoc, Nat.mul_assoc,
              Nat.mul_comm (2 ^ (64 * (n - s)))]
    have he : ∃ Q₀ R₀ : UInt64Array, (if lt (shr (shr W (64 * (n - s))) (64 * s))
        (shr V (64 * (n - s))) = true then divNorm (shr W (64 * (n - s))) (shr V (64 * (n - s))) s s
        else (allOnes s, add (sub (shr W (64 * (n - s))) (shl (shr V (64 * (n - s))) (64 * s)))
          (shr V (64 * (n - s))))) = (Q₀, R₀) ∧
        Q₀.size ≤ s ∧ R₀.size ≤ 2 * s + 1 ∧ W.toNat / V.toNat ≤ Q₀.toNat ∧
        Q₀.toNat < 2 ^ (64 * s) ∧ R₀.toNat < 2 * 2 ^ (64 * s) ∧
        Q₀.toNat * (V.toNat / 2 ^ (64 * (n - s))) + R₀.toNat = W.toNat / 2 ^ (64 * (n - s)) := by
      split
      · rename_i hc
        rw [lt_iff _ _ (by rw [size_shr]; lia), toNat_shr _ _ (by lia), hWhv, hVhv,
          Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _)] at hc
        obtain ⟨r₁, r₂, r₃, r₄⟩ := ihn s hsn s _ _ (by lia) hVhs (by rw [hVhv]; exact hVh)
          hWhs (by rw [hWhv, hVhv]; exact hc) (by lia)
        rw [hWhv, hVhv] at r₃ r₄
        have hVh0 : 0 < V.toNat / 2 ^ (64 * (n - s)) :=
          Nat.lt_of_lt_of_le (Nat.two_pow_pos _) hVh
        refine ⟨_, _, rfl, r₁, by lia, ?_, ?_, ?_, ?_⟩
        · rw [r₃]; exact (Nat.le_div_iff_mul_le hVh0).2 hD
        · rw [r₃]; exact (Nat.div_lt_iff_lt_mul hVh0).2 (Nat.lt_of_lt_of_eq hc (Nat.mul_comm _ _))
        · rw [r₄]; have := Nat.mod_lt (W.toNat / 2 ^ (64 * (n - s))) hVh0; lia
        · rw [r₃, r₄, Nat.mul_comm]; exact Nat.div_add_mod _ _
      · rename_i hc
        rw [lt_iff _ _ (by rw [size_shr]; lia), toNat_shr _ _ (by lia), hWhv, hVhv,
          Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _)] at hc
        have hsh := toNat_shl (shr V (64 * (n - s))) (64 * s) (by lia)
        rw [hVhv] at hsh
        have hsub := toNat_sub (shr W (64 * (n - s))) (shl (shr V (64 * (n - s))) (64 * s))
          (by rw [hsh, hWhv]; lia) (by lia) (by rw [size_shl]; lia)
        rw [hsh, hWhv] at hsub
        have hadd := toNat_add (sub (shr W (64 * (n - s))) (shl (shr V (64 * (n - s))) (64 * s)))
          (shr V (64 * (n - s))) (by rw [size_sub]; lia)
        rw [hsub, hVhv] at hadd
        have hB := Nat.one_le_two_pow (n := 64 * s)
        refine ⟨_, _, rfl, by rw [size_allOnes]; exact Nat.le_refl _,
          by rw [size_add, size_sub]; lia, ?_, ?_, ?_, ?_⟩
        · rw [toNat_allOnes]; lia
        · rw [toNat_allOnes]; lia
        · rw [hadd, Nat.add_mul, Nat.one_mul] at *
          lia
        · rw [toNat_allOnes, hadd, Nat.sub_mul, Nat.one_mul, Nat.mul_comm (2 ^ (64 * s))]
          have := Nat.le_mul_of_pos_left (V.toNat / 2 ^ (64 * (n - s)))
            (show 0 < 2 ^ (64 * s) by lia)
          lia
    obtain ⟨Q₀, R₀, hedef, hQ₀s, hR₀s, hQ₀v, hQ₀lt, hR₀lt, hQR⟩ := he
    rw [hedef]
    clear hedef ihn
    dsimp only
    -- `P = Q₀ V_lo` and `T₀ = R₀ β^(n-s) + W_lo`, with `T₀ + Q₀ V = W + P`.
    have hVlo : (low V (n - s)).toNat = V.toNat % 2 ^ (64 * (n - s)) := toNat_low _ _ (by lia)
    have hVlos : (low V (n - s)).size ≤ n - s := by rw [size_low _ _ (by lia)]; lia
    have hPv : (mul Q₀ (low V (n - s))).toNat = Q₀.toNat * (V.toNat % 2 ^ (64 * (n - s))) := by
      rw [toNat_mul _ _ (by lia), hVlo]
    have hPs := size_mul_le Q₀ (low V (n - s))
    have hPlt : (mul Q₀ (low V (n - s))).toNat ≤ 2 ^ (64 * n) := by
      rw [hPv]
      have := Nat.mod_lt V.toNat hPn
      calc Q₀.toNat * (V.toNat % 2 ^ (64 * (n - s))) ≤ 2 ^ (64 * s) * 2 ^ (64 * (n - s)) :=
            Nat.mul_le_mul (by lia) (by lia)
        _ = 2 ^ (64 * n) := by rw [← Nat.pow_add]; congr 1; lia
    have hWlo : (low W (n - s)).toNat = W.toNat % 2 ^ (64 * (n - s)) := toNat_low _ _ (by lia)
    have hWlos : (low W (n - s)).size ≤ n - s := by rw [size_low _ _ (by lia)]; lia
    have hT₀ : (low (add (shl R₀ (64 * (n - s))) (low W (n - s))) (n + 1)).toNat =
        R₀.toNat * 2 ^ (64 * (n - s)) + W.toNat % 2 ^ (64 * (n - s)) := by
      rw [toNat_low _ _ (by rw [size_add, size_shl]; lia), toNat_add _ _ (by rw [size_shl]; lia),
        toNat_shl _ _ (by lia), hWlo, Nat.mod_eq_of_lt]
      have := Nat.mod_lt W.toNat hPn
      have := Nat.mul_le_mul_right (2 ^ (64 * (n - s)))
        (show R₀.toNat + 1 ≤ 2 * 2 ^ (64 * s) by lia)
      have e : 2 * 2 ^ (64 * s) * 2 ^ (64 * (n - s)) ≤ 2 ^ (64 * (n + 1)) := by
        rw [Nat.mul_assoc, ← Nat.pow_add, show 64 * (n + 1) = 64 * s + 64 * (n - s) + 64 by lia,
          Nat.pow_add 2 (64 * s + 64 * (n - s)) 64, Nat.mul_comm]
        exact Nat.mul_le_mul_left _ (by decide)
      rw [Nat.add_mul, Nat.one_mul] at this
      lia
    have hT₀s : (low (add (shl R₀ (64 * (n - s))) (low W (n - s))) (n + 1)).size ≤ n + 1 := by
      rw [size_low _ _ (by rw [size_add, size_shl]; lia)]; lia
    have hinv : (low (add (shl R₀ (64 * (n - s))) (low W (n - s))) (n + 1)).toNat +
        Q₀.toNat * V.toNat = W.toNat + (mul Q₀ (low V (n - s))).toNat := by
      rw [hT₀, hPv]
      have h₁ := Nat.div_add_mod V.toNat (2 ^ (64 * (n - s)))
      have h₂ := Nat.div_add_mod W.toNat (2 ^ (64 * (n - s)))
      rw [← hQR] at h₂
      generalize V.toNat / 2 ^ (64 * (n - s)) = vh at *
      generalize V.toNat % 2 ^ (64 * (n - s)) = vl at *
      generalize W.toNat % 2 ^ (64 * (n - s)) = wl at *
      generalize 2 ^ (64 * (n - s)) = P' at *
      rw [← h₁, ← h₂]
      grind
    obtain ⟨f₁, f₂, f₃, f₄⟩ := dcFix_spec V (mul Q₀ (low V (n - s))) Q₀ _ n W.toNat hV0 hVlt hPlt
      hT₀s (by lia) hinv hQ₀v
    generalize dcFix V (mul Q₀ (low V (n - s))) Q₀
      (low (add (shl R₀ (64 * (n - s))) (low W (n - s))) (n + 1)) n = f at f₁ f₂ f₃ f₄ ⊢
    have hdm := Nat.div_add_mod W.toNat V.toNat
    have hWr : (sub f.2 (mul Q₀ (low V (n - s)))).toNat = W.toNat % V.toNat := by
      rw [toNat_sub _ _ (by rw [f₄]; lia) (by lia) (by lia), f₄]
      lia
    have hWrs : (sub f.2 (mul Q₀ (low V (n - s)))).size ≤ n + 1 := by rw [size_sub]; exact f₂
    generalize sub f.2 (mul Q₀ (low V (n - s))) = Wr at hWr hWrs ⊢
    -- The rest `U' = U mod βʲ + (W mod V) βʲ < V βʲ`.
    have hB := Nat.two_pow_pos (64 * j)
    have hUlo := Nat.mod_lt U.toNat hB
    have hWm := Nat.mod_lt W.toNat hV0
    have hU's : (add (low U j) (shl Wr (64 * j))).size ≤ n + s + j + 3 := by
      rw [size_add, size_low _ _ (by lia), size_shl]; lia
    have hU'v : (add (low U j) (shl Wr (64 * j))).toNat =
        U.toNat % 2 ^ (64 * j) + W.toNat % V.toNat * 2 ^ (64 * j) := by
      rw [toNat_add _ _ (by rw [size_low _ _ (by lia), size_shl]; lia), toNat_low _ _ (by lia),
        toNat_shl _ _ (by lia), hWr]
    have hU'lt : U.toNat % 2 ^ (64 * j) + W.toNat % V.toNat * 2 ^ (64 * j) <
        V.toNat * 2 ^ (64 * j) := by
      have := Nat.mul_le_mul_right (2 ^ (64 * j)) (show W.toNat % V.toNat + 1 ≤ V.toNat by lia)
      rw [Nat.add_mul, Nat.one_mul] at this
      lia
    have hU'n : V.toNat * 2 ^ (64 * j) ≤ 2 ^ (64 * (n + j)) := by
      rw [show 64 * (n + j) = 64 * n + 64 * j by lia, Nat.pow_add]
      exact Nat.mul_le_mul_right _ (Nat.le_of_lt hVlt)
    have hLs : (low (add (low U j) (shl Wr (64 * j))) (n + j)).size ≤ n + j := by
      rw [size_low _ _ (by lia)]; lia
    have hLv : (low (add (low U j) (shl Wr (64 * j))) (n + j)).toNat =
        U.toNat % 2 ^ (64 * j) + W.toNat % V.toNat * 2 ^ (64 * j) := by
      rw [toNat_low _ _ (by lia), hU'v, Nat.mod_eq_of_lt (by lia)]
    obtain ⟨r₁, r₂, r₃, r₄⟩ := ihk j hjk _ V hn hVs hV hLs (by rw [hLv]; exact hU'lt) (by lia)
    clear ihk
    generalize divNorm (low (add (low U j) (shl Wr (64 * j))) (n + j)) V n j = r at r₁ r₂ r₃ r₄
    rw [hLv] at r₃ r₄
    -- `U = U' + D V βʲ`.
    have hUsplit : U.toNat = U.toNat % 2 ^ (64 * j) + W.toNat % V.toNat * 2 ^ (64 * j) +
        V.toNat * (W.toNat / V.toNat * 2 ^ (64 * j)) := by
      have h₁ := Nat.mod_add_div U.toNat (2 ^ (64 * j))
      rw [← hWv] at h₁
      clear r₁ r₂ r₃ r₄ hLv hU'v hQ₀v f₃ f₄ hWr hD hWhv hVhv
      generalize W.toNat / V.toNat = d at *
      generalize W.toNat % V.toNat = m at *
      generalize W.toNat = w at *
      generalize U.toNat % 2 ^ (64 * j) = a at *
      generalize 2 ^ (64 * j) = B at *
      subst hdm
      rw [← h₁]
      grind
    have hQ : U.toNat / V.toNat = W.toNat / V.toNat * 2 ^ (64 * j) +
        (U.toNat % 2 ^ (64 * j) + W.toNat % V.toNat * 2 ^ (64 * j)) / V.toNat := by
      conv => lhs; rw [hUsplit]
      rw [Nat.add_mul_div_left _ _ hV0]; lia
    have hR : U.toNat % V.toNat =
        (U.toNat % 2 ^ (64 * j) + W.toNat % V.toNat * 2 ^ (64 * j)) % V.toNat := by
      conv => lhs; rw [hUsplit]
      rw [Nat.add_mul_mod_self_left]
    refine ⟨by rw [size_low _ _ (by rw [size_add, size_shl]; lia)]; lia, r₂, ?_, by rw [r₄, hR]⟩
    rw [toNat_low _ _ (by rw [size_add, size_shl]; lia), toNat_add _ _ (by rw [size_shl]; lia),
      toNat_shl _ _ (by lia), f₃, r₃, ← hQ, Nat.mod_eq_of_lt hq]

/-! ## Division -/

/--
`(a / b, a % b)`, for `0 < b`: when `b` has at least `dcThreshold` limbs, `a` and `b` are shifted
left by the `c` bits that set the top bit of `b`, divided by `divNorm`, and the remainder is shifted
back; otherwise `divModBase`.
-/
public def divMod (a b : UInt64Array) : UInt64Array × UInt64Array :=
  let L := MPN.log2 b.toUSlice
  let nb := L / 64 + 1
  if dcThreshold ≤ nb ∧ nb ≤ a.size ∧ 8 * a.size + 48 < USize.size then
    let c := 63 - L % 64
    let r := divNorm (low (shl a c) (a.size + 1)) (low (shl b c) nb) nb (a.size + 1 - nb)
    (r.1, shr r.2 c)
  else divModBase a b

private theorem divMod_dc (a b : UInt64Array) (hb : 0 < b.toNat)
    (hU : a.size + b.size + 1 < USize.size) :
    (divMod a b).1.toNat = a.toNat / b.toNat ∧ (divMod a b).2.toNat = a.toNat % b.toNat ∧
      (divMod a b).1.size ≤ a.size + 1 ∧ (divMod a b).2.size ≤ max a.size b.size := by
  have hL : MPN.log2 b.toUSlice = _root_.Nat.log2 b.toNat := by
    rw [log2_eq, toUSlice_toNat b (by lia)]
  unfold divMod
  dsimp only
  rw [hL]
  split
  · rename_i h
    generalize hl : _root_.Nat.log2 b.toNat = L at h ⊢
    have hb₀ : b.toNat ≠ 0 := by lia
    have hlo : 2 ^ L ≤ b.toNat := by rw [← hl]; exact Nat.log2_self_le hb₀
    have hhi : b.toNat < 2 ^ (L + 1) := by rw [← hl]; exact Nat.lt_log2_self
    have hB : b.toNat < 2 ^ (64 * b.size) := by rw [toNat_eq_valAt]; exact valAt_lt ..
    have hA : a.toNat < 2 ^ (64 * a.size) := by rw [toNat_eq_valAt]; exact valAt_lt ..
    have hnb : L / 64 + 1 ≤ b.size := by
      refine Nat.le_of_not_lt fun h' => ?_
      have := Nat.pow_le_pow_right (show 0 < 2 by decide) (show 64 * b.size ≤ L by lia)
      lia
    generalize hnb' : L / 64 + 1 = nb at h hnb ⊢
    generalize hc : 63 - L % 64 = c
    have hLc : L + c + 1 = 64 * nb := by lia
    have hc64 : c < 64 := by lia
    -- The normalized divisor.
    have hVv : (low (shl b c) nb).toNat = b.toNat * 2 ^ c := by
      rw [toNat_low _ _ (by rw [size_shl]; lia), toNat_shl _ _ (by lia), Nat.mod_eq_of_lt]
      calc b.toNat * 2 ^ c < 2 ^ (L + 1) * 2 ^ c :=
            Nat.mul_lt_mul_of_pos_right hhi (Nat.two_pow_pos _)
        _ = 2 ^ (64 * nb) := by rw [← Nat.pow_add, ← hLc]; congr 1; lia
    have hVs : (low (shl b c) nb).size = nb := by
      rw [size_low _ _ (by rw [size_shl]; lia), size_shl]; lia
    have hVn : 2 ^ (64 * nb - 1) ≤ (low (shl b c) nb).toNat := by
      rw [hVv, show 64 * nb - 1 = L + c by lia, Nat.pow_add]
      exact Nat.mul_le_mul_right _ hlo
    -- The normalized dividend.
    have hUv : (low (shl a c) (a.size + 1)).toNat = a.toNat * 2 ^ c := by
      rw [toNat_low _ _ (by rw [size_shl]; lia), toNat_shl _ _ (by lia), Nat.mod_eq_of_lt]
      calc a.toNat * 2 ^ c < 2 ^ (64 * a.size) * 2 ^ 64 :=
            Nat.mul_lt_mul_of_lt_of_le hA (Nat.pow_le_pow_right (by decide) (by lia))
              (Nat.two_pow_pos _)
        _ = 2 ^ (64 * (a.size + 1)) := by rw [← Nat.pow_add]; congr 1
    have hUs : (low (shl a c) (a.size + 1)).size ≤ nb + (a.size + 1 - nb) := by
      rw [size_low _ _ (by rw [size_shl]; lia)]; lia
    have hUV : (low (shl a c) (a.size + 1)).toNat <
        (low (shl b c) nb).toNat * 2 ^ (64 * (a.size + 1 - nb)) := by
      rw [hUv, hVv, Nat.mul_right_comm]
      apply Nat.mul_lt_mul_of_pos_right _ (Nat.two_pow_pos _)
      calc a.toNat < 2 ^ (64 * a.size) := hA
        _ = 2 ^ (64 * (nb - 1)) * 2 ^ (64 * (a.size + 1 - nb)) := by
            rw [← Nat.pow_add]; congr 1; lia
        _ ≤ b.toNat * 2 ^ (64 * (a.size + 1 - nb)) := by
            apply Nat.mul_le_mul_right
            exact Nat.le_trans (Nat.pow_le_pow_right (by decide) (by lia)) hlo
    obtain ⟨r₁, r₂, r₃, r₄⟩ := divNorm_spec nb (a.size + 1 - nb) _ _ (by lia) hVs hVn hUs hUV
      (by lia)
    rw [hUv, hVv, Nat.mul_div_mul_right _ _ (Nat.two_pow_pos _)] at r₃
    rw [hUv, hVv, Nat.mul_mod_mul_right] at r₄
    refine ⟨r₃, ?_, by lia, by rw [size_shr]; lia⟩
    rw [toNat_shr _ _ (by lia), r₄, Nat.mul_div_cancel _ (Nat.two_pow_pos _)]
  · obtain ⟨d₁, d₂⟩ := toNat_divModBase a b hb hU
    obtain ⟨e₁, e₂⟩ := size_divModBase a b (by lia)
    exact ⟨d₁, d₂, e₁, e₂⟩

public theorem toNat_divMod (a b : UInt64Array) (hb : 0 < b.toNat)
    (hU : a.size + b.size + 1 < USize.size) :
    (divMod a b).1.toNat = a.toNat / b.toNat ∧ (divMod a b).2.toNat = a.toNat % b.toNat :=
  ⟨(divMod_dc a b hb hU).1, (divMod_dc a b hb hU).2.1⟩

public theorem size_divMod (a b : UInt64Array) (hb : 0 < b.toNat)
    (hU : a.size + b.size + 1 < USize.size) :
    (divMod a b).1.size ≤ a.size + 1 ∧ (divMod a b).2.size ≤ max a.size b.size :=
  (divMod_dc a b hb hU).2.2

end MPN.Num
