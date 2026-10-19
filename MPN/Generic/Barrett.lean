/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import MPN.Generic.Ops

/-!
# Division by a reciprocal, at any base

Barrett's division of `x` by an `n`-limb divisor `d` with `μ ≈ B²ⁿ / d`: the quotient estimate
`q = ⌊⌊x / Bⁿ⁻¹⌋ μ / Bⁿ⁺¹⌋` costs one product, the remainder `x - q d` another, and a good `μ`
leaves `q` at most a few units below the quotient. Longer dividends are divided `n` limbs at a
time (`divBlocks`). The reciprocal comes from Newton's iteration on the top half of `d`
(`recip`), at about the cost of a product.

None of the estimates needs a proof: `fixQuot` checks every quotient estimate exactly against
`x = q d + r` with `0 ≤ r < d`, corrects it a few units up or down, and falls back to the slow
division of `NatOps` when it is further off. The specifications therefore hold for any `μ`;
the quality of `μ` only decides how fast they are met.
-/

namespace MPN

namespace NatOps

variable {α : Type} (o : NatOps α)

/-! ## Correcting a quotient -/

/--
The quotient and remainder of `x` by `d` from a quotient `q` and the remainder `r = x - q d`
when `q` may be too small: `q` goes up by one while `r ≥ d`, at most `fuel` times before the
slow division.
-/
def fixUp (x d q r : α) : Nat → α × α
  | 0 => if o.le d r then o.divRem x d else (q, r)
  | fuel + 1 => if o.le d r then fixUp x d (o.add q o.one) (o.sub r d) fuel else (q, r)

/--
The quotient and remainder of `x` by `d` from a quotient `q` that is too large, with
`q d = x + t` and `t > 0`: `q` goes down by one while `t > d`, at most `fuel` times before the
slow division.
-/
def fixDown (x d q t : α) : Nat → α × α
  | 0 => if o.le t d then (o.sub q o.one, o.sub d t) else o.divRem x d
  | fuel + 1 => if o.le t d then (o.sub q o.one, o.sub d t)
      else fixDown x d (o.sub q o.one) (o.sub t d) fuel

/--
The quotient and remainder of `x` by `d`, from an estimate `q` of the quotient: one product
`q d`, then `fixUp` or `fixDown`.
-/
public def fixQuot (x d q : α) (fuel : Nat) : α × α :=
  let p := o.mul q d
  if o.le p x then o.fixUp x d q (o.sub x p) fuel else o.fixDown x d q (o.sub p x) fuel

/-- The specification of a quotient and remainder: `x = q d + r` with `r < d`. -/
@[expose] public def IsDivRem (x d : Nat) (qr : α × α) : Prop :=
  x = o.val qr.1 * d + o.val qr.2 ∧ o.val qr.2 < d

theorem isDivRem_divRem (x d : α) (hd : 0 < o.val d) :
    o.IsDivRem (o.val x) (o.val d) (o.divRem x d) := by
  obtain ⟨h₁, h₂⟩ := o.val_divRem x d (by lia)
  refine ⟨?_, ?_⟩
  · rw [h₁, h₂]; exact (Nat.div_add_mod' _ _).symm
  · rw [h₂]; exact Nat.mod_lt _ hd

theorem fixUp_spec (x d : α) (hd : 0 < o.val d) :
    ∀ fuel (q r : α), o.val x = o.val q * o.val d + o.val r →
      o.IsDivRem (o.val x) (o.val d) (o.fixUp x d q r fuel) := by
  intro fuel
  induction fuel with
  | zero =>
    intro q r h
    simp only [fixUp]
    split
    · exact o.isDivRem_divRem x d hd
    · rename_i hn
      rw [o.le_iff] at hn
      exact ⟨h, by lia⟩
  | succ fuel ih =>
    intro q r h
    simp only [fixUp]
    split
    · rename_i hle
      rw [o.le_iff] at hle
      apply ih
      rw [o.val_add, o.val_one, o.val_sub _ _ hle, Nat.add_mul, Nat.one_mul]
      lia
    · rename_i hn
      rw [o.le_iff] at hn
      exact ⟨h, by lia⟩

theorem fixDown_spec (x d : α) (hd : 0 < o.val d) :
    ∀ fuel (q t : α), o.val q * o.val d = o.val x + o.val t → 0 < o.val t →
      o.IsDivRem (o.val x) (o.val d) (o.fixDown x d q t fuel) := by
  intro fuel
  induction fuel with
  | zero =>
    intro q t h ht
    simp only [fixDown]
    split
    · rename_i hle
      rw [o.le_iff] at hle
      have hq : 1 ≤ o.val q := by
        rcases Nat.eq_zero_or_pos (o.val q) with h0 | h0
        · rw [h0, Nat.zero_mul] at h; lia
        · exact h0
      refine ⟨?_, ?_⟩
      · rw [o.val_sub _ _ (by rw [o.val_one]; exact hq), o.val_one, o.val_sub _ _ hle,
          Nat.sub_mul, Nat.one_mul]
        have : o.val d ≤ o.val q * o.val d := Nat.le_mul_of_pos_left _ hq
        lia
      · rw [o.val_sub _ _ hle]; lia
    · exact o.isDivRem_divRem x d hd
  | succ fuel ih =>
    intro q t h ht
    simp only [fixDown]
    have hq : 1 ≤ o.val q := by
      rcases Nat.eq_zero_or_pos (o.val q) with h0 | h0
      · rw [h0, Nat.zero_mul] at h; lia
      · exact h0
    split
    · rename_i hle
      rw [o.le_iff] at hle
      refine ⟨?_, ?_⟩
      · rw [o.val_sub _ _ (by rw [o.val_one]; exact hq), o.val_one, o.val_sub _ _ hle,
          Nat.sub_mul, Nat.one_mul]
        have : o.val d ≤ o.val q * o.val d := Nat.le_mul_of_pos_left _ hq
        lia
      · rw [o.val_sub _ _ hle]; lia
    · rename_i hn
      rw [o.le_iff] at hn
      apply ih
      · rw [o.val_sub _ _ (by rw [o.val_one]; exact hq), o.val_one, o.val_sub _ _ (by lia),
          Nat.sub_mul, Nat.one_mul]
        have : o.val d ≤ o.val q * o.val d := Nat.le_mul_of_pos_left _ hq
        lia
      · rw [o.val_sub _ _ (by lia)]; lia

public theorem fixQuot_spec (x d q : α) (fuel : Nat) (hd : 0 < o.val d) :
    o.IsDivRem (o.val x) (o.val d) (o.fixQuot x d q fuel) := by
  unfold fixQuot
  dsimp only
  split
  · rename_i hle
    rw [o.le_iff, o.val_mul] at hle
    apply o.fixUp_spec x d hd
    rw [o.val_sub _ _ (by rw [o.val_mul]; exact hle), o.val_mul]
    lia
  · rename_i hn
    rw [o.le_iff, o.val_mul] at hn
    apply o.fixDown_spec x d hd
    · rw [o.val_sub _ _ (by rw [o.val_mul]; lia), o.val_mul]; lia
    · rw [o.val_sub _ _ (by rw [o.val_mul]; lia), o.val_mul]; lia

/-! ## Barrett's division -/

/--
`x` by the `n`-limb `d` with the reciprocal `μ ≈ B²ⁿ / d`, for `x < B²ⁿ`: the estimate
`⌊⌊x / Bⁿ⁻¹⌋ μ / Bⁿ⁺¹⌋`, corrected by `fixQuot`.
-/
public def barrettStep (x d μ : α) (n : Nat) : α × α :=
  o.fixQuot x d (o.hi (n + 1) (o.mul (o.hi (n - 1) x) μ)) 2

public theorem barrettStep_spec (x d μ : α) (n : Nat) (hd : 0 < o.val d) :
    o.IsDivRem (o.val x) (o.val d) (o.barrettStep x d μ n) :=
  o.fixQuot_spec _ _ _ _ hd

/--
`a` by the `n`-limb `d` with the reciprocal `μ`, `n` limbs of quotient at a time from the top:
the quotient of the part above the low `n` limbs, then one `barrettStep` on its remainder
followed by those limbs.
-/
public def divBlocks (d μ : α) (n : Nat) (hn : 0 < n) (a : α) : α × α :=
  if o.size a ≤ 2 * n then o.barrettStep a d μ n
  else
    let t := divBlocks d μ n hn (o.hi n a)
    let s := o.barrettStep (o.add (o.shl n t.2) (o.lo n a)) d μ n
    (o.add (o.shl n t.1) s.1, s.2)
termination_by o.size a
decreasing_by rw [o.size_hi]; lia

public theorem divBlocks_spec (d μ : α) (n : Nat) (hn : 0 < n) (hd : 0 < o.val d) (a : α) :
    o.IsDivRem (o.val a) (o.val d) (o.divBlocks d μ n hn a) := by
  induction a using WellFounded.induction (InvImage.wf o.size Nat.lt_wfRel.wf) with
  | h a ih =>
    unfold divBlocks
    split
    · exact o.barrettStep_spec _ _ _ _ hd
    · rename_i hsz
      dsimp only
      obtain ⟨ht₁, ht₂⟩ := ih (o.hi n a) (by
        show o.size (o.hi n a) < o.size a
        rw [o.size_hi]; lia)
      generalize o.divBlocks d μ n hn (o.hi n a) = t at ht₁ ht₂
      obtain ⟨hs₁, hs₂⟩ := o.barrettStep_spec (o.add (o.shl n t.2) (o.lo n a)) d μ n hd
      generalize o.barrettStep (o.add (o.shl n t.2) (o.lo n a)) d μ n = s at hs₁ hs₂
      refine ⟨?_, hs₂⟩
      rw [o.val_add, o.val_lo] at hs₁
      rw [o.val_shl] at hs₁
      rw [o.val_hi] at ht₁
      show o.val a = o.val (o.add (o.shl n t.1) s.1) * o.val d + o.val s.2
      rw [o.val_add, o.val_shl]
      have hsplit := Nat.div_add_mod (o.val a) (o.B ^ n)
      generalize o.val a / o.B ^ n = A at hsplit ht₁
      generalize o.val a % o.B ^ n = L at hsplit hs₁
      generalize o.B ^ n = P at *
      rw [← hsplit, ht₁]
      generalize o.val t.1 = T₁ at *
      generalize o.val t.2 = T₂ at *
      generalize o.val s.1 = S₁ at *
      generalize o.val s.2 = S₂ at *
      generalize o.val d = D at *
      grind

/-! ## The reciprocal -/

/--
An approximation of `B²ⁿ / d` for the `n`-limb `d`, by Newton's iteration: the reciprocal
`μₕ` of the top `h = ⌈n / 2⌉ + 1` limbs, then one step from `μ₀ = μₕ Bᵏ`, `k = n - h`:
`μ₀ + μ₀ (B²ⁿ - d μ₀) / B²ⁿ = μₕ Bᵏ + μₕ e / B²ⁿ⁻²ᵏ` with `e = B²ⁿ⁻ᵏ - d μₕ`, an `n` by `h`
product. `e` is about `B²ⁿ⁻ᵏ⁻ʰ`, and only its limbs from `t = 2n - 2k - h - 2` on enter the
correction, an `h` by `k` product. The step squares the relative error of `μ₀`, about `B⁻ʰ`, so
the error of the result is about `Bⁿ⁻²ʰ ≤ B⁻²` units: the extra limb of `h` keeps errors from
growing from one level to the next. Four limbs and fewer by the slow division.
-/
public def recip (d : α) : α :=
  let n := o.size d
  if hn : n ≤ 4 then (o.divRem (o.pow (2 * n)) d).1
  else
    let k := n - ((n + 1) / 2 + 1)
    let μₕ := recip (o.hi k d)
    let t := 2 * n - 2 * k - ((n + 1) / 2 + 1) - 2
    let Q := o.pow (2 * n - k)
    let p := o.mul d μₕ
    if o.le p Q then
      o.add (o.shl k μₕ) (o.hi (2 * n - 2 * k - t) (o.mul μₕ (o.hi t (o.sub Q p))))
    else
      o.sub (o.shl k μₕ)
        (o.add (o.hi (2 * n - 2 * k - t) (o.mul μₕ (o.hi t (o.sub p Q)))) o.one)
termination_by o.size d
decreasing_by rw [o.size_hi]; lia

/-- `(a / d, a % d)` by Barrett's division with Newton's reciprocal, for `d ≠ 0`. -/
public def divMu (a d : α) : α × α :=
  if hn : 0 < o.size d then o.divBlocks d (o.recip d) (o.size d) hn a else o.divRem a d

public theorem divMu_spec (a d : α) (hd : 0 < o.val d) :
    o.val (o.divMu a d).1 = o.val a / o.val d ∧ o.val (o.divMu a d).2 = o.val a % o.val d := by
  have h : o.IsDivRem (o.val a) (o.val d) (o.divMu a d) := by
    unfold divMu
    split
    · exact o.divBlocks_spec _ _ _ _ hd a
    · exact o.isDivRem_divRem a d hd
  obtain ⟨h₁, h₂⟩ := h
  have hq : o.val a / o.val d = o.val (o.divMu a d).1 := by
    rw [h₁, Nat.add_comm, Nat.add_mul_div_right _ _ hd, Nat.div_eq_of_lt h₂, Nat.zero_add]
  have hr : o.val a % o.val d = o.val (o.divMu a d).2 := by
    rw [h₁, Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt h₂]
  exact ⟨hq.symm, hr.symm⟩

end NatOps

end MPN
