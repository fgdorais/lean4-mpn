/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import MPN.Generic.Ops

/-!
# Divide-and-conquer division, at any base

`NatOps.divNorm base T U V n k` divides `U < V Bᵏ` by a divisor `V < Bⁿ` by computing the quotient in
digits of at most `⌊n / 2⌋` limbs from the top down, like Algorithm D in base `Bˢ`: the scheme of
Burnikel and Ziegler and of GMP's `mpn_dcpi1_div_qr`, written recursively. The top digit of `s`
limbs is `D = ⌊W / V⌋ < Bˢ`, where `W = ⌊U / Bʲ⌋` and `j = k - s`. It is estimated from the top
`2 s` limbs `Wₕ` of `W` and the top `s` limbs `Vₕ` of `V` as `⌊Wₕ / Vₕ⌋`, a recursive division,
or `Bˢ - 1` when that would not be a digit; the estimate is never too small. Like GMP, the step
keeps the remainder `R₀` of the recursive division: with `W = Wₕ P + W_lo` and `V = Vₕ P + V_lo`
for `P = B^(n-s)`, `W - Q₀ V = (R₀ P + W_lo) - Q₀ V_lo`, so it multiplies `Q₀` by the low `n - s`
limbs of `V` only, and `dcFix` adds `V` back while the difference is negative. The rest,
`U - D V Bʲ < V Bʲ`, is divided recursively, and below `T` limbs in `V` the instance's `base`
division takes over. Division then costs `O(M(n) log n)`.

The result is exact for any `V > 0`. When `V` is normalized, with its top limb at least `B / 2`, the
estimate is at most two too large and `dcFix` takes at most two steps; the instance normalizes
before calling, with its own shifts. From `main64`'s `Num.divNorm`.
-/

namespace MPN

namespace NatOps

variable {α : Type} (o : NatOps α)

/-- `Bˢ - 1`. -/
public def allOnes (s : Nat) : α := o.sub (o.pow s) o.one

public theorem val_allOnes (s : Nat) : o.val (o.allOnes s) = o.B ^ s - 1 := by
  have := Nat.one_le_two_pow (n := s)
  have hB : 1 ≤ o.B ^ s := Nat.one_le_pow _ _ (by have := o.one_lt_B; lia)
  rw [allOnes, o.val_sub _ _ (by rw [o.val_pow, o.val_one]; exact hB), o.val_pow, o.val_one]

/-! ## The correction -/

/--
Adds `V` to `T` and decreases `Q` while `T < P`: with the invariant `T + Q V = W + P`, it ends
with `Q = ⌊W / V⌋` and `T = W mod V + P`.
-/
public def dcFix (V P Q T : α) : α × α :=
  if _h : o.le P T = false ∧ o.le o.one Q = true then
    dcFix V P (o.sub Q o.one) (o.add T V)
  else (Q, T)
termination_by o.val Q
decreasing_by
  have := (o.le_iff _ _).1 _h.2
  rw [o.val_one] at this
  rw [o.val_sub _ _ (by rw [o.val_one]; exact this), o.val_one]
  lia

private theorem dcFix_spec (V P : α) (W : Nat) (hV : 0 < o.val V) :
    ∀ Q T : α, o.val T + o.val Q * o.val V = W + o.val P → W / o.val V ≤ o.val Q →
      o.val (o.dcFix V P Q T).1 = W / o.val V ∧
        o.val (o.dcFix V P Q T).2 = W % o.val V + o.val P := by
  intro Q T
  induction Q, T using NatOps.dcFix.induct o V P with
  | case1 Q T h ih =>
    intro hinv hQ
    rw [dcFix, dite_eq_left_of_eq_true (eq_true h)]
    obtain ⟨h₂, h₃⟩ := h
    have hlt₂ : o.val T < o.val P := Nat.lt_of_not_le fun hle => by
      rw [(o.le_iff P T).2 hle] at h₂; exact absurd h₂ (by simp)
    have hq1 := (o.le_iff _ _).1 h₃
    rw [o.val_one] at hq1
    have hlt : W / o.val V < o.val Q := by
      refine Nat.lt_of_not_le fun hle => ?_
      have h₁ := Nat.mul_le_mul_right (o.val V) hle
      have h₂ := Nat.div_mul_le_self W (o.val V)
      generalize o.val Q * o.val V = QV at *
      generalize W / o.val V * o.val V = DV at *
      lia
    have hQ' : o.val (o.sub Q o.one) = o.val Q - 1 := by
      rw [o.val_sub _ _ (by rw [o.val_one]; exact hq1), o.val_one]
    have hT' : o.val (o.add T (V)) = o.val T + o.val V := o.val_add _ _
    exact ih (by
      rw [hQ', hT', Nat.sub_mul, Nat.one_mul]
      have : o.val V ≤ o.val Q * o.val V := Nat.le_mul_of_pos_left _ (by lia)
      lia) (by rw [hQ']; lia)
  | case2 Q T h =>
    intro hinv hQ
    rw [dcFix, dite_eq_right h]
    -- The loop stopped with `T ≥ P`, or with `Q = 0`; either way `Q V ≤ W`.
    have hQV : o.val Q * o.val V ≤ W := by
      by_cases hPT : o.le P T = true
      · have := (o.le_iff _ _).1 hPT; lia
      · have hq : ¬o.le o.one Q = true := fun hq => h ⟨by simpa using hPT, hq⟩
        rw [o.le_iff, o.val_one] at hq
        rw [show o.val Q = 0 by lia, Nat.zero_mul]; exact Nat.zero_le _
    have : o.val Q ≤ W / o.val V := (Nat.le_div_iff_mul_le hV).2 hQV
    have hQe : o.val Q = W / o.val V := by lia
    refine ⟨hQe, ?_⟩
    have := Nat.div_add_mod W (o.val V)
    rw [hQe] at hinv
    rw [Nat.mul_comm] at this
    lia

/-! ## The recursion -/

/-- The size of the top digit: `k mod m`, or `m` when `m` divides `k`. -/
@[inline] public def dcDigit (k m : Nat) : Nat := if k % m = 0 then m else k % m

private theorem dcDigit_spec (k m : Nat) (hm : 1 ≤ m) (hk : 1 ≤ k) :
    1 ≤ dcDigit k m ∧ dcDigit k m ≤ m ∧ dcDigit k m ≤ k := by
  have := Nat.mod_lt k (show 0 < m by lia)
  have := Nat.mod_le k m
  unfold dcDigit
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
`(U / V, U % V)` for `0 < V < Bⁿ` and `U < V Bᵏ`: one digit of `s ≤ ⌊n / 2⌋` limbs from the top,
estimated by a recursive division and corrected by `dcFix`, then the rest recursively; `base`
below `T` limbs.
-/
public def divNorm (base : α → α → α × α) (T : Nat) (U V : α) (n k : Nat) : α × α :=
  if _h : n < T ∨ n < 2 ∨ k = 0 then base U V
  else
    let s := dcDigit k (n / 2)
    let j := k - s
    let W := o.hi j U
    let Wh := o.hi (n - s) W
    let Vh := o.hi (n - s) V
    let e := if o.le Vh (o.hi s Wh) then (o.allOnes s, o.add (o.sub Wh (o.shl s Vh)) Vh)
      else divNorm base T Wh Vh s s
    let P := o.mul e.1 (o.lo (n - s) V)
    let f := o.dcFix V P e.1 (o.add (o.shl (n - s) e.2) (o.lo (n - s) W))
    let U' := o.add (o.lo j U) (o.shl j (o.sub f.2 P))
    let r := divNorm base T U' V n j
    (o.add (o.shl j f.1) r.1, r.2)
termination_by (n, k)
decreasing_by
  all_goals have ht := dcDigit_spec k (n / 2) (by lia) (by lia)
  · exact Prod.Lex.left _ _ (by lia)
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

public theorem divNorm_spec (base : α → α → α × α)
    (hbase : ∀ U V, 0 < o.val V →
      o.val (base U V).1 = o.val U / o.val V ∧ o.val (base U V).2 = o.val U % o.val V)
    (T n : Nat) : ∀ (k : Nat) (U V : α), 0 < o.val V → o.val V < o.B ^ n →
      o.val U < o.val V * o.B ^ k →
      o.val (o.divNorm base T U V n k).1 = o.val U / o.val V ∧
        o.val (o.divNorm base T U V n k).2 = o.val U % o.val V := by
  have hBpos : ∀ m, 0 < o.B ^ m := fun _ => Nat.pow_pos (by have := o.one_lt_B; lia)
  induction n using Nat.strongRecOn with
  | ind n ihn =>
  intro k
  induction k using Nat.strongRecOn with
  | ind k ihk =>
  intro U V hV0 hVlt hUV
  have hq : o.val U / o.val V < o.B ^ k :=
    (Nat.div_lt_iff_lt_mul hV0).2 (by rw [Nat.mul_comm]; exact hUV)
  rw [divNorm]
  split
  · exact hbase U V hV0
  · rename_i h
    dsimp only
    have hm : 1 ≤ n / 2 := by lia
    obtain ⟨hs1, hsm, hsk⟩ := dcDigit_spec k (n / 2) hm (by lia)
    generalize dcDigit k (n / 2) = s at hs1 hsm hsk ⊢
    have hsn : s < n := by lia
    generalize hj : k - s = j
    have hkj : k = j + s := by lia
    subst hkj
    have hjk : j < j + s := by lia
    -- The window `W = U / Bʲ`.
    have hPk : o.B ^ (j + s) = o.B ^ s * o.B ^ j := by rw [Nat.pow_add, Nat.mul_comm]
    have hWlt : o.val U / o.B ^ j < o.val V * o.B ^ s :=
      (Nat.div_lt_iff_lt_mul (hBpos _)).2 (by rw [Nat.mul_assoc, ← hPk]; exact hUV)
    have hWv : o.val (o.hi j U) = o.val U / o.B ^ j := o.val_hi _ _
    generalize o.hi j U = W at hWv ⊢
    rw [← hWv] at hWlt
    -- The top limbs `Wₕ` and `Vₕ`.
    have hPn := hBpos (n - s)
    have hPns : o.B ^ n = o.B ^ s * o.B ^ (n - s) := by
      rw [← Nat.pow_add]; congr 1; lia
    have hWhv : o.val (o.hi (n - s) W) = o.val W / o.B ^ (n - s) := o.val_hi _ _
    have hVhv : o.val (o.hi (n - s) V) = o.val V / o.B ^ (n - s) := o.val_hi _ _
    have hD : o.val W / o.val V * (o.val V / o.B ^ (n - s)) ≤ o.val W / o.B ^ (n - s) :=
      dc_est hPn (Nat.div_mul_le_self _ _)
    have hDs : o.val W / o.val V < o.B ^ s :=
      (Nat.div_lt_iff_lt_mul hV0).2 (by rw [Nat.mul_comm]; exact hWlt)
    have hVhlt : o.val V / o.B ^ (n - s) < o.B ^ s := by
      apply (Nat.div_lt_iff_lt_mul hPn).2
      rw [← hPns]; exact hVlt
    have hWh : o.val W / o.B ^ (n - s) < (o.val V / o.B ^ (n - s) + 1) * o.B ^ s := by
      apply (Nat.div_lt_iff_lt_mul hPn).2
      have := Nat.lt_mul_div_succ (o.val V) hPn
      calc o.val W < o.val V * o.B ^ s := hWlt
        _ ≤ o.B ^ (n - s) * (o.val V / o.B ^ (n - s) + 1) * o.B ^ s :=
            Nat.mul_le_mul_right _ (Nat.le_of_lt this)
        _ = _ := by rw [Nat.mul_comm (o.B ^ (n - s)), Nat.mul_assoc, Nat.mul_assoc,
              Nat.mul_comm (o.B ^ (n - s))]
    -- The estimate `Q₀` and the remainder `R₀ = Wₕ - Q₀ Vₕ`; `Q₀` is never too small.
    have he : ∃ Q₀ R₀ : α, (if o.le (o.hi (n - s) V) (o.hi s (o.hi (n - s) W)) = true then
        (o.allOnes s, o.add (o.sub (o.hi (n - s) W) (o.shl s (o.hi (n - s) V))) (o.hi (n - s) V))
        else o.divNorm base T (o.hi (n - s) W) (o.hi (n - s) V) s s) = (Q₀, R₀) ∧
        o.val W / o.val V ≤ o.val Q₀ ∧ o.val Q₀ < o.B ^ s ∧ o.val R₀ < 2 * o.B ^ s ∧
        o.val Q₀ * (o.val V / o.B ^ (n - s)) + o.val R₀ = o.val W / o.B ^ (n - s) := by
      split
      · rename_i hc
        rw [o.le_iff, hVhv, o.val_hi, hWhv, Nat.le_div_iff_mul_le (hBpos _)] at hc
        have hsh : o.val (o.shl s (o.hi (n - s) V)) = o.val V / o.B ^ (n - s) * o.B ^ s := by
          rw [o.val_shl, hVhv]
        have hsub := o.val_sub (o.hi (n - s) W) (o.shl s (o.hi (n - s) V))
          (by rw [hsh, hWhv]; exact hc)
        rw [hsh, hWhv] at hsub
        have hadd := o.val_add (o.sub (o.hi (n - s) W) (o.shl s (o.hi (n - s) V)))
          (o.hi (n - s) V)
        rw [hsub, hVhv] at hadd
        have hB := hBpos s
        refine ⟨_, _, rfl, ?_, ?_, ?_, ?_⟩
        · rw [o.val_allOnes]; lia
        · rw [o.val_allOnes]; lia
        · rw [hadd]
          rw [Nat.add_mul, Nat.one_mul] at hWh
          lia
        · rw [o.val_allOnes, hadd, Nat.sub_mul, Nat.one_mul, Nat.mul_comm (o.B ^ s)]
          have := Nat.le_mul_of_pos_left (o.val V / o.B ^ (n - s)) hB
          lia
      · rename_i hc
        rw [o.le_iff, hVhv, o.val_hi, hWhv, Nat.le_div_iff_mul_le (hBpos _)] at hc
        have hc' : o.val W / o.B ^ (n - s) < o.val V / o.B ^ (n - s) * o.B ^ s := by lia
        have hVh0 : 0 < o.val V / o.B ^ (n - s) := by
          rcases Nat.eq_zero_or_pos (o.val V / o.B ^ (n - s)) with e | e
          · rw [e, Nat.zero_mul] at hc'; lia
          · exact e
        obtain ⟨r₃, r₄⟩ := ihn s hsn s _ _ (by rw [hVhv]; exact hVh0) (by rw [hVhv]; exact hVhlt)
          (by rw [hWhv, hVhv]; exact hc')
        rw [hWhv, hVhv] at r₃ r₄
        refine ⟨_, _, rfl, ?_, ?_, ?_, ?_⟩
        · rw [r₃]; exact (Nat.le_div_iff_mul_le hVh0).2 hD
        · rw [r₃]; exact (Nat.div_lt_iff_lt_mul hVh0).2 (Nat.lt_of_lt_of_eq hc' (Nat.mul_comm _ _))
        · rw [r₄]; have := Nat.mod_lt (o.val W / o.B ^ (n - s)) hVh0; lia
        · rw [r₃, r₄, Nat.mul_comm]; exact Nat.div_add_mod _ _
    obtain ⟨Q₀, R₀, hedef, hQ₀v, hQ₀lt, hR₀lt, hQR⟩ := he
    rw [hedef]
    clear hedef ihn
    dsimp only
    -- `P = Q₀ V_lo` and `T₀ = R₀ B^(n-s) + W_lo`, with `T₀ + Q₀ V = W + P`.
    have hPv : o.val (o.mul Q₀ (o.lo (n - s) V)) =
        o.val Q₀ * (o.val V % o.B ^ (n - s)) := by rw [o.val_mul, o.val_lo]
    have hT₀ : o.val (o.add (o.shl (n - s) R₀) (o.lo (n - s) W)) =
        o.val R₀ * o.B ^ (n - s) + o.val W % o.B ^ (n - s) := by
      rw [o.val_add, o.val_shl, o.val_lo]
    have hinv : o.val (o.add (o.shl (n - s) R₀) (o.lo (n - s) W)) + o.val Q₀ * o.val V =
        o.val W + o.val (o.mul Q₀ (o.lo (n - s) V)) := by
      rw [hT₀, hPv]
      have h₁ := Nat.div_add_mod (o.val V) (o.B ^ (n - s))
      have h₂ := Nat.div_add_mod (o.val W) (o.B ^ (n - s))
      rw [← hQR] at h₂
      generalize o.val V / o.B ^ (n - s) = vh at *
      generalize o.val V % o.B ^ (n - s) = vl at *
      generalize o.val W % o.B ^ (n - s) = wl at *
      generalize o.B ^ (n - s) = P' at *
      rw [← h₁, ← h₂]
      grind
    obtain ⟨f₃, f₄⟩ := o.dcFix_spec V (o.mul Q₀ (o.lo (n - s) V)) (o.val W) hV0 Q₀ _ hinv hQ₀v
    generalize o.dcFix V (o.mul Q₀ (o.lo (n - s) V)) Q₀
      (o.add (o.shl (n - s) R₀) (o.lo (n - s) W)) = f at f₃ f₄ ⊢
    have hdm := Nat.div_add_mod (o.val W) (o.val V)
    have hWr : o.val (o.sub f.2 (o.mul Q₀ (o.lo (n - s) V))) = o.val W % o.val V := by
      rw [o.val_sub _ _ (by rw [f₄]; lia), f₄]
      lia
    generalize o.sub f.2 (o.mul Q₀ (o.lo (n - s) V)) = Wr at hWr ⊢
    -- The rest `U' = U mod Bʲ + (W mod V) Bʲ < V Bʲ`.
    have hB := hBpos j
    have hUlo := Nat.mod_lt (o.val U) hB
    have hWm := Nat.mod_lt (o.val W) hV0
    have hU'v : o.val (o.add (o.lo j U) (o.shl j Wr)) =
        o.val U % o.B ^ j + o.val W % o.val V * o.B ^ j := by
      rw [o.val_add, o.val_lo, o.val_shl, hWr]
    have hU'lt : o.val U % o.B ^ j + o.val W % o.val V * o.B ^ j < o.val V * o.B ^ j := by
      have := Nat.mul_le_mul_right (o.B ^ j) (show o.val W % o.val V + 1 ≤ o.val V by lia)
      rw [Nat.add_mul, Nat.one_mul] at this
      lia
    obtain ⟨r₃, r₄⟩ := ihk j hjk _ V hV0 hVlt (by rw [hU'v]; exact hU'lt)
    clear ihk
    generalize o.divNorm base T (o.add (o.lo j U) (o.shl j Wr)) V n j = r at r₃ r₄
    rw [hU'v] at r₃ r₄
    -- `U = U' + D V Bʲ`.
    have hUsplit : o.val U = o.val U % o.B ^ j + o.val W % o.val V * o.B ^ j +
        o.val V * (o.val W / o.val V * o.B ^ j) := by
      have h₁ := Nat.mod_add_div (o.val U) (o.B ^ j)
      rw [← hWv] at h₁
      clear r₃ r₄ hU'v hQ₀v f₃ f₄ hWr hD hWhv hVhv
      generalize o.val W / o.val V = d at *
      generalize o.val W % o.val V = m at *
      generalize o.val W = w at *
      generalize o.val U % o.B ^ j = a at *
      generalize o.B ^ j = B' at *
      subst hdm
      rw [← h₁]
      grind
    have hQ : o.val U / o.val V = o.val W / o.val V * o.B ^ j +
        (o.val U % o.B ^ j + o.val W % o.val V * o.B ^ j) / o.val V := by
      conv => lhs; rw [hUsplit]
      rw [Nat.add_mul_div_left _ _ hV0]; lia
    have hR : o.val U % o.val V =
        (o.val U % o.B ^ j + o.val W % o.val V * o.B ^ j) % o.val V := by
      conv => lhs; rw [hUsplit]
      rw [Nat.add_mul_mod_self_left]
    refine ⟨?_, by rw [r₄, hR]⟩
    rw [o.val_add, o.val_shl, f₃, r₃, ← hQ]

end NatOps

end MPN
