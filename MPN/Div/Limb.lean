/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import MPN.Basic

/-!
# Division by a limb

`divRem1 a d` divides `a` by the limb `d`, like GMP's `mpn_divrem_1`, from the top limb down: each
step divides the remainder so far, followed by the next limb, by `d`. The remainder stays below
`d`, so this two-limb number is below `d β` and its quotient fits in a limb.
-/

open ScalarArray

namespace MPN

/-- One step of the division: `r β + x = q d + r'` with `r' < d`, computed in `UInt64`. -/
@[inline, expose] public def divStep (r x d : UInt32) : UInt32 × UInt32 :=
  let t : UInt64 := r.toUInt64 * 4294967296 + x.toUInt64
  ((t / d.toUInt64).toUInt32, (t % d.toUInt64).toUInt32)

public theorem divStep_spec (r x d : UInt32) (hr : r.toNat < d.toNat) :
    (divStep r x d).1.toNat = (r.toNat * 2 ^ 32 + x.toNat) / d.toNat ∧
      (divStep r x d).2.toNat = (r.toNat * 2 ^ 32 + x.toNat) % d.toNat := by
  have hx := x.toNat_lt
  have hr' := r.toNat_lt
  have hd' : 0 < d.toNat := by lia
  have ht : (r.toUInt64 * 4294967296 + x.toUInt64).toNat = r.toNat * 2 ^ 32 + x.toNat := by
    simp only [UInt64.toNat_add, UInt64.toNat_mul, UInt32.toNat_toUInt64, UInt64.reduceToNat]
    lia
  have hq : (r.toNat * 2 ^ 32 + x.toNat) / d.toNat < 2 ^ 32 := by
    rw [Nat.div_lt_iff_lt_mul hd']
    have := Nat.mul_le_mul_right (2 ^ 32) (show r.toNat + 1 ≤ d.toNat from hr)
    lia
  constructor
  · simp only [divStep, UInt64.toNat_toUInt32, UInt64.toNat_div, UInt32.toNat_toUInt64, ht]
    exact Nat.mod_eq_of_lt hq
  · simp only [divStep, UInt64.toNat_toUInt32, UInt64.toNat_mod, UInt32.toNat_toUInt64, ht]
    have := Nat.mod_lt (r.toNat * 2 ^ 32 + x.toNat) hd'
    have := d.toNat_lt
    lia

/--
Divides the limbs of `a` below `i` by `d`, from the top down, with remainder `r` so far, writing
the quotient limbs into `q`.
-/
def divRem1Loop (a : UInt32Array.Slice) (d : UInt32) :
    (i : Nat) → (r : UInt32) → (q : UInt32Array) → q.size = a.size → i ≤ a.size →
      UInt32Array × UInt32
  | 0, r, q, _, _ => (q, r)
  | i + 1, r, q, hq, hi =>
    let p := divStep r a[i] d
    divRem1Loop a d i p.2 (q.set i p.1 (by lia)) (by simp [hq]) (by lia)

/--
`a / d` as `a.size` limbs and `a % d`, like GMP's `mpn_divrem_1`. It is exact when `d ≠ 0`.
-/
public def divRem1 (a : UInt32Array.Slice) (d : UInt32) : UInt32Array × UInt32 :=
  divRem1Loop a d a.size 0 (.replicate a.size 0) (by simp) (Nat.le_refl _)

private theorem divRem1Loop_spec (a : UInt32Array.Slice) (d : UInt32) (hd : d ≠ 0) (i : Nat)
    (r : UInt32) (q : UInt32Array) (hq : q.size = a.size) (hi : i ≤ a.size)
    (hr : r.toNat < d.toNat) (hz : ∀ k (hk : k < i), q.toList[k]'(by simp; lia) = 0)
    (hv : ofLimbs q.toList * d.toNat + 2 ^ (32 * i) * r.toNat =
      2 ^ (32 * i) * ofLimbs (a.copy.toList.drop i)) :
    (divRem1Loop a d i r q hq hi).1.size = a.size ∧
      ofLimbs (divRem1Loop a d i r q hq hi).1.toList * d.toNat +
          (divRem1Loop a d i r q hq hi).2.toNat = toNat a ∧
      (divRem1Loop a d i r q hq hi).2.toNat < d.toNat := by
  induction i generalizing r q with
  | zero =>
    simp only [divRem1Loop]
    simp only [Nat.mul_zero, Nat.pow_zero, Nat.one_mul, List.drop_zero] at hv
    exact ⟨hq, hv, hr⟩
  | succ i ih =>
    simp only [divRem1Loop]
    have hd' : 0 < d.toNat := by
      rcases Nat.eq_zero_or_pos d.toNat with h | h
      · exact absurd (UInt32.toNat_inj.1 (by simpa using h)) hd
      · exact h
    obtain ⟨h₁, h₂⟩ := divStep_spec r a[i] d hr
    apply ih
    · rw [h₂]
      exact Nat.mod_lt _ hd'
    · intro k hk
      simp only [UInt32Array.toList_set]
      rw [List.getElem_set_ne (by lia)]
      exact hz k (by lia)
    · -- Writing the quotient limb at `i`, where `q` has a zero, adds it at `βⁱ`.
      have hk : i < q.toList.length := by simp; lia
      have hset := ofLimbs_set q.toList i (divStep r a[i] d).1 hk
      rw [hz i (by lia), UInt32.toNat_zero, Nat.mul_zero, Nat.add_zero] at hset
      have hdrop : ofLimbs (a.copy.toList.drop i) =
          a[i].toNat + 2 ^ 32 * ofLimbs (a.copy.toList.drop (i + 1)) := by
        rw [toList_copy_drop (by lia), ofLimbs_cons]
      have hdiv := Nat.div_add_mod (r.toNat * 2 ^ 32 + a[i].toNat) d.toNat
      rw [UInt32Array.toList_set, hset, h₁, h₂]
      rw [Nat.mul_add 32 i 1, Nat.mul_one, Nat.pow_add] at hv
      generalize ofLimbs q.toList = Q at *
      generalize ofLimbs (a.copy.toList.drop i) = H at *
      generalize ofLimbs (a.copy.toList.drop (i + 1)) = H' at *
      generalize 2 ^ (32 * i) = P at *
      generalize (r.toNat * 2 ^ 32 + a[i].toNat) / d.toNat = qd at *
      generalize (r.toNat * 2 ^ 32 + a[i].toNat) % d.toNat = rd at *
      generalize r.toNat = R at *
      generalize a[i].toNat = x at *
      generalize d.toNat = D at *
      generalize (2 : Nat) ^ 32 = B at *
      clear ih hset h₁ h₂ hz hk
      subst hdrop
      grind

private theorem toNat_pos_of_ne_zero {d : UInt32} (hd : d ≠ 0) : 0 < d.toNat := by
  rcases Nat.eq_zero_or_pos d.toNat with h | h
  · exact absurd (UInt32.toNat_inj.1 (by simpa using h)) hd
  · exact h

private theorem divRem1_spec' (a : UInt32Array.Slice) (d : UInt32) (hd : d ≠ 0) :
    (divRem1 a d).1.size = a.size ∧
      ofLimbs (divRem1 a d).1.toList * d.toNat + (divRem1 a d).2.toNat = toNat a ∧
      (divRem1 a d).2.toNat < d.toNat :=
  divRem1Loop_spec a d hd a.size 0 (.replicate a.size 0) (by simp) (Nat.le_refl _)
    (by rw [UInt32.toNat_zero]; exact toNat_pos_of_ne_zero hd)
    (fun k hk => by simp)
    (by simp [List.drop_of_length_le])

@[simp] public theorem size_divRem1 (a : UInt32Array.Slice) (d : UInt32) (hd : d ≠ 0) :
    (divRem1 a d).1.size = a.size :=
  (divRem1_spec' a d hd).1

/-- `divRem1` divides: `a = q d + r` with `r < d`. -/
public theorem divRem1_spec (a : UInt32Array.Slice) (d : UInt32) (hd : d ≠ 0) :
    toNat (divRem1 a d).1 * d.toNat + (divRem1 a d).2.toNat = toNat a ∧
      (divRem1 a d).2.toNat < d.toNat := by
  rw [toNat_toSlice]
  exact ⟨(divRem1_spec' a d hd).2.1, (divRem1_spec' a d hd).2.2⟩

end MPN
