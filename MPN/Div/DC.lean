/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import MPN.Div.Basecase
public import MPN.Mul
public import MPN.Cmp

/-!
# Divide-and-conquer division

`divRemWith cfg u v` divides by a divisor of `n ≥ cfg.divDC` limbs by computing the quotient in
blocks of `m = ⌊n / 2⌋` limbs, from the top down, like Algorithm D in base `βᵐ`, and below that
threshold with `divRemBasecase`. This is the scheme of Burnikel and Ziegler and of GMP's
`mpn_dcpi1_div_qr`: the block digits are estimated by recursive divisions by the top half of the
divisor and corrected with a multiplication, so that division costs `O(M(n) log n)`.

At the step for block `j`, the remainder `r` is below `v βʲ⁺ᵐ`, so the digit is `⌊W / v⌋ < βᵐ`
where `W = ⌊r / βʲ⌋` is the window of limbs `j` to `j + n + m` of `r`. Its estimate is
`Q̂ = min ⌊Wₕ / vₕ⌋ (βᵐ - 1)`, where `Wₕ` is the top `2 m` limbs of the window and `vₕ` the top
`m` limbs of `v`, which is never too small for the same reason as in `divRemBasecase`; when `v` is
normalized it is at most two too large. The trial product `P = Q̂ v` is computed with
`mulLimbsWith`, and while it exceeds `W`, `Q̂` decreases by one and `v` is subtracted from `P`.
Correctness only needs the estimate not to be too small.
-/

open ScalarArray

namespace MPN

private theorem toNat_oneLimb : toNat (limbArray 1) = 1 := toNat_limbArray 1

/-! ## The estimate of a block digit -/

/-- `m` limbs of `β - 1`, the largest block digit. -/
def allOnes (m : Nat) : UInt32Array := .replicate m 0xFFFFFFFF

private theorem toNat_allOnes (m : Nat) : toNat (allOnes m) = 2 ^ (32 * m) - 1 := by
  rw [toNat_toSlice, allOnes, UInt32Array.toList_replicate]
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [List.replicate_succ, ofLimbs_cons, ih, Nat.mul_add, Nat.mul_one, Nat.pow_add]
    have : 1 ≤ 2 ^ (32 * m) := Nat.one_le_two_pow
    simp only [UInt32.reduceToNat]
    generalize 2 ^ (32 * m) = P at *
    rw [Nat.mul_sub, Nat.mul_one, Nat.mul_comm]
    lia

/--
The estimate of a block digit and the remainder of the top limbs `wh` of the window by the top
limbs `bh` of the divisor, from their division `d`: `(q₁, r₁)` when `q₁` has at most `s` limbs,
and otherwise `βˢ - 1` and `wh - (βˢ - 1) bh`, computed with one product.
-/
def dcEstimate (cfg : Config) (wh bh : UInt32Array.Slice) (s : Nat)
    (d : UInt32Array × UInt32Array) : UInt32Array × UInt32Array :=
  if lt d.1 (allOnes s) then
    (copyPadded (d.1.toSlice 0 s) s, d.2)
  else
    (allOnes s, subInto (copyPadded wh (bh.size + s + 1)) 0 (mulLimbsWith cfg (allOnes s) bh))

private theorem dcEstimate_spec (cfg : Config) (wh bh : UInt32Array.Slice) (s : Nat)
    (d : UInt32Array × UInt32Array) (hwh : wh.size ≤ bh.size + s)
    (hd : toNat d.1 * toNat bh + toNat d.2 = toNat wh) :
    (dcEstimate cfg wh bh s d).1.size = s ∧
      toNat (dcEstimate cfg wh bh s d).1 = min (toNat d.1) (2 ^ (32 * s) - 1) ∧
      toNat (dcEstimate cfg wh bh s d).2 + toNat (dcEstimate cfg wh bh s d).1 * toNat bh =
        toNat wh := by
  have h1 : 1 ≤ 2 ^ (32 * s) := Nat.one_le_two_pow
  by_cases h : lt d.1 (allOnes s) = true
  · have heq : dcEstimate cfg wh bh s d = (copyPadded (d.1.toSlice 0 s) s, d.2) := by
      rw [dcEstimate, ite_eq_left h]
    rw [lt_iff, toNat_allOnes] at h
    rw [heq]
    dsimp only
    have hq : toNat (copyPadded (d.1.toSlice 0 s) s) = toNat d.1 := by
      rw [toNat_copyPadded, toNat_toSlice_of_lt _ _ (by lia)]
    refine ⟨size_copyPadded _ _ (by simp; lia), by rw [hq]; lia, ?_⟩
    rw [hq]
    lia
  · have heq : dcEstimate cfg wh bh s d = (allOnes s, subInto (copyPadded wh (bh.size + s + 1)) 0
        (mulLimbsWith cfg (allOnes s) bh)) := by
      rw [dcEstimate, ite_eq_right h]
    rw [lt_iff, toNat_allOnes] at h
    rw [heq]
    dsimp only
    have hM := isMul_mulLimbsWith cfg
    have hms := hM.size_eq (allOnes s) bh
    have hmv := hM.toNat_eq (allOnes s) bh
    rw [toNat_allOnes] at hmv
    -- `(βˢ - 1) bh ≤ q₁ bh ≤ wh`.
    have h' : 2 ^ (32 * s) - 1 ≤ toNat d.1 := by lia
    have hle : (2 ^ (32 * s) - 1) * toNat bh ≤ toNat wh :=
      Nat.le_trans (Nat.mul_le_mul_right (toNat bh) h') (by lia)
    have hfit : 0 + (mulLimbsWith cfg (allOnes s) bh).toSlice.size ≤
        (copyPadded wh (bh.size + s + 1)).size := by
      rw [UInt32Array.size_toSlice, hms, size_copyPadded _ _ (by lia)]
      simp [allOnes]
      lia
    have hsub := toNat_subInto_of_le _ _ _ hfit (by
      rw [toNat_copyPadded, hmv, Nat.mul_zero, Nat.pow_zero, Nat.one_mul]; exact hle)
    rw [toNat_copyPadded, hmv, Nat.mul_zero, Nat.pow_zero, Nat.one_mul] at hsub
    refine ⟨by simp [allOnes], by rw [toNat_allOnes]; lia, ?_⟩
    rw [hsub, toNat_allOnes]
    lia

/--
The correction of a block digit: while `x < p`, adds `v` to `x` and decreases the estimate `qh`
by one. With `x + qh v = p + W` for the window `W`, it ends with `qh = ⌊W / v⌋` and
`x - p = W mod v`. The guard also checks what the termination needs, which always holds.
-/
def dcFix (v : UInt32Array.Slice) (p : UInt32Array.Slice) (x qh : UInt32Array) :
    UInt32Array × UInt32Array :=
  if _h : lt x p = true ∧ lt qh (limbArray 1) = false ∧ 1 ≤ qh.size then
    dcFix v p (addInto x 0 v) (subInto qh 0 (limbArray 1))
  else
    (x, qh)
termination_by toNat qh
decreasing_by
  obtain ⟨-, h₂, h₃⟩ := _h
  have hle : ¬ toNat qh < toNat (limbArray 1) := fun h' => by
    rw [← lt_iff] at h'
    rw [h'] at h₂
    exact Bool.noConfusion h₂
  rw [toNat_oneLimb] at hle
  rw [toNat_subInto_of_le _ _ _ (by simp [limbArray]; lia)
    (by rw [toNat_oneLimb, Nat.mul_zero, Nat.pow_zero, Nat.one_mul]; lia), toNat_oneLimb,
    Nat.mul_zero, Nat.pow_zero, Nat.one_mul]
  lia

private theorem dcFix_spec (v p : UInt32Array.Slice) (x qh : UInt32Array) (W : Nat)
    (hV : 0 < toNat v) (hq : 1 ≤ qh.size) (hvx : v.size ≤ x.size)
    (hcap : toNat p + toNat v < 2 ^ (32 * x.size))
    (hinv : toNat x + toNat qh * toNat v = toNat p + W) (hge : W / toNat v ≤ toNat qh) :
    (dcFix v p x qh).1.size = x.size ∧ (dcFix v p x qh).2.size = qh.size ∧
      toNat p ≤ toNat (dcFix v p x qh).1 ∧
      toNat (dcFix v p x qh).2 = W / toNat v ∧
      toNat (dcFix v p x qh).1 + W / toNat v * toNat v = toNat p + W := by
  induction x, qh using dcFix.induct v p with
  | case1 x qh h ih =>
    have heq : dcFix v p x qh = dcFix v p (addInto x 0 v) (subInto qh 0 (limbArray 1)) := by
      rw [dcFix, dite_eq_left h]
    rw [heq]
    obtain ⟨h₁, -, -⟩ := h
    rw [lt_iff] at h₁
    -- `x < p` makes `qh v > W`, so `qh > ⌊W / v⌋ ≥ 0`.
    have hgt : W / toNat v < toNat qh := by
      have := Nat.div_mul_le_self W (toNat v)
      exact Nat.lt_of_mul_lt_mul_right (a := toNat v) (by lia)
    have hqpos : 0 < toNat qh := Nat.lt_of_le_of_lt (Nat.zero_le _) hgt
    have hfit₁ : 0 + (limbArray 1).toSlice.size ≤ qh.size := by simp [limbArray]; lia
    have hfit₂ : 0 + v.size ≤ x.size := by lia
    have hq' := toNat_subInto_of_le qh 0 (limbArray 1) hfit₁
      (by rw [toNat_oneLimb, Nat.mul_zero, Nat.pow_zero, Nat.one_mul]; exact hqpos)
    have hx' := toNat_addInto_of_lt x 0 v hfit₂
      (by rw [Nat.mul_zero, Nat.pow_zero, Nat.one_mul]; lia)
    rw [toNat_oneLimb] at hq'
    simp only [Nat.mul_zero, Nat.pow_zero, Nat.one_mul] at hq' hx'
    obtain ⟨i₁, i₂, i₃, i₄, i₅⟩ := ih (by rw [size_subInto _ _ _ hfit₁]; exact hq)
      (by rw [size_addInto _ _ _ hfit₂]; exact hvx) (by rw [size_addInto _ _ _ hfit₂]; exact hcap)
      (by
        rw [hx', hq', Nat.sub_mul, Nat.one_mul]
        have : toNat v ≤ toNat qh * toNat v := Nat.le_mul_of_pos_left _ hqpos
        lia)
      (by rw [hq']; lia)
    rw [size_addInto _ _ _ hfit₂] at i₁
    rw [size_subInto _ _ _ hfit₁] at i₂
    exact ⟨i₁, i₂, i₃, i₄, i₅⟩
  | case2 x qh h =>
    have heq : dcFix v p x qh = (x, qh) := by rw [dcFix, dite_eq_right h]
    rw [heq]
    refine ⟨rfl, rfl, ?_⟩
    -- The guard failed: `x ≥ p`, since `qh = 0` would make `x = p + W ≥ p`.
    have hle : toNat p ≤ toNat x := by
      refine Nat.le_of_not_lt fun hlt => h ⟨(lt_iff _ _).2 hlt, ?_, hq⟩
      cases hc : lt qh (limbArray 1)
      · rfl
      · rw [lt_iff, toNat_oneLimb] at hc
        have : toNat qh = 0 := by lia
        rw [this, Nat.zero_mul] at hinv
        lia
    -- So `qh v ≤ W`, and `qh = ⌊W / v⌋`.
    have hle' : toNat qh ≤ W / toNat v := (Nat.le_div_iff_mul_le hV).2 (by lia)
    have heq : toNat qh = W / toNat v := by lia
    refine ⟨hle, heq, ?_⟩
    rw [← heq]
    exact hinv

/-! ## One block -/

/--
One step of the division at the block of quotient limbs `j` to `j + s`, for `1 ≤ s ≤ m` where
`m = n / 2` and `h = n - m`, as in Burnikel and Ziegler. With the window `W = Wₗ + βʰ Wₕ` and
`v = vₗ + βʰ vₕ`, the digit `Q̂` and the remainder `R₁ = Wₕ - Q̂ vₕ` come from `divRec` on `Wₕ` and
`vₕ`, so that `W - Q̂ v = (Wₗ + βʰ R₁) - Q̂ vₗ` needs only the product `Q̂ vₗ` of `s` by `h` limbs.
`dcFix` corrects the digit. The limbs of `r` above the window are zero, so subtracting
`Q v = W - (W mod v)` at limb `j` replaces the window with `W mod v`, and the block of `q` at limb
`j` is zero, so adding `Q` there writes it: both are copies (`copySlice`), as is `R₁` into the
zero limbs above `Wₗ`. Returns the new remainder and quotient.
-/
def divDCStep (cfg : Config) (v : UInt32Array.Slice) (h4 : 4 ≤ v.size)
    (divRec : (u' v' : UInt32Array.Slice) → v'.size < v.size → 2 ≤ v'.size →
      UInt32Array × UInt32Array)
    (s j : Nat) (r q : UInt32Array) : UInt32Array × UInt32Array :=
  let w := r.toSlice j (j + v.size + s)
  let wh := w.slice (v.size - v.size / 2) w.size
  let bh := v.slice (v.size - v.size / 2) v.size
  let e := dcEstimate cfg wh bh s (divRec wh bh (by simp [bh]; lia) (by simp [bh]; lia))
  let x := e.2.copySlice 0 (copyPadded (w.slice 0 (v.size - v.size / 2)) (v.size + s + 1))
    (v.size - v.size / 2) (v.size / 2 + s)
  let p := mulLimbsWith cfg e.1 (v.slice 0 (v.size - v.size / 2))
  let f := dcFix v p x e.1
  ((subInto f.1 0 p).copySlice 0 r j (v.size + s), f.2.copySlice 0 q j s)

/-- Adding a multiple of `d` below the next multiple keeps a multiple of `d` in range. -/
private theorem add_le_of_dvd {a b d : Nat} (ha : d ∣ a) (hb : d ∣ b) (hab : a < b) :
    a + d ≤ b := by
  obtain ⟨x, rfl⟩ := ha
  obtain ⟨y, rfl⟩ := hb
  have hd : 0 < d := Nat.pos_of_ne_zero fun h => by simp [h] at hab
  have : x < y := Nat.lt_of_mul_lt_mul_left hab
  have : d * (x + 1) ≤ d * y := Nat.mul_le_mul_left _ this
  rw [Nat.mul_add, Nat.mul_one] at this
  exact this

/-- The remainder after subtracting the digit's multiple is below `βʲ v`, as in Algorithm D. -/
private theorem dc_rem_lt {R P V : Nat} (hP : 0 < P) (hV : 0 < V) :
    R - P * (R / P / V * V) < V * P := by
  have h₁ := Nat.div_add_mod R P
  have h₂ := Nat.div_add_mod (R / P) V
  have h₃ := Nat.mod_lt (R / P) hV
  have h₄ := Nat.mod_lt R hP
  generalize R / P / V = qs at *
  generalize R / P = W at *
  generalize (R / P) % V = wm at *
  generalize W % V = wm at *
  generalize R % P = rm at *
  have : P * (wm + 1) ≤ P * V := Nat.mul_le_mul_left _ h₃
  rw [Nat.mul_add, Nat.mul_one] at this
  rw [← h₂, Nat.mul_add] at h₁
  rw [Nat.mul_comm V P, Nat.mul_comm qs V]
  lia

private theorem divDCStep_spec (cfg : Config) (v : UInt32Array.Slice) (h4 : 4 ≤ v.size)
    (divRec : (u' v' : UInt32Array.Slice) → v'.size < v.size → 2 ≤ v'.size →
      UInt32Array × UInt32Array)
    (hrec : ∀ u' v' h h', v'[v'.size - 1]'(by lia) ≠ 0 →
      toNat (divRec u' v' h h').1 * toNat v' + toNat (divRec u' v' h h').2 = toNat u' ∧
        toNat (divRec u' v' h h').2 < toNat v')
    (hvt : v[v.size - 1]'(by lia) ≠ 0) (s j : Nat) (hs : 1 ≤ s) (hsm : s ≤ v.size / 2)
    (r q : UInt32Array) (hr : j + v.size + s ≤ r.size) (hq : j + s ≤ q.size)
    (hbound : toNat r < toNat v * 2 ^ (32 * (j + s)))
    (hdiv : 2 ^ (32 * (j + s)) ∣ toNat q) :
    (divDCStep cfg v h4 divRec s j r q).1.size = r.size ∧
      (divDCStep cfg v h4 divRec s j r q).2.size = q.size ∧
      toNat (divDCStep cfg v h4 divRec s j r q).2 * toNat v +
          toNat (divDCStep cfg v h4 divRec s j r q).1 = toNat q * toNat v + toNat r ∧
      toNat (divDCStep cfg v h4 divRec s j r q).1 < toNat v * 2 ^ (32 * j) ∧
      2 ^ (32 * j) ∣ toNat (divDCStep cfg v h4 divRec s j r q).2 := by
  have hV := toNat_lt v
  have hP : 0 < 2 ^ (32 * j) := Nat.two_pow_pos _
  -- `r` fits in the limbs up to `j + n + s`.
  have hR : toNat r < 2 ^ (32 * (j + v.size + s)) := by
    have : toNat v * 2 ^ (32 * (j + s)) ≤ 2 ^ (32 * v.size) * 2 ^ (32 * (j + s)) :=
      Nat.mul_le_mul_right _ (Nat.le_of_lt hV)
    rw [← Nat.pow_add, show 32 * v.size + 32 * (j + s) = 32 * (j + v.size + s) by lia] at this
    lia
  -- The window `W = ⌊r / βʲ⌋ = Wₗ + βʰ Wₕ` and the divisor `v = vₗ + βʰ vₕ`.
  have hws : (r.toSlice j (j + v.size + s)).size = v.size + s := by simp; lia
  have hW := toNat_window r j (j + v.size + s) (by lia) hR
  have hsplitW := toNat_slice_add_toNat_slice (r.toSlice j (j + v.size + s))
    (v.size - v.size / 2) (by lia)
  have hsplitV := toNat_slice_add_toNat_slice v (v.size - v.size / 2) (by lia)
  have hWl : toNat ((r.toSlice j (j + v.size + s)).slice 0 (v.size - v.size / 2)) <
      2 ^ (32 * (v.size - v.size / 2)) := by
    have := toNat_lt ((r.toSlice j (j + v.size + s)).slice 0 (v.size - v.size / 2))
    simp only [UInt32Array.Slice.size_slice, hws] at this
    rwa [show min (v.size - v.size / 2) (v.size + s) - 0 = v.size - v.size / 2 by lia] at this
  have hWh : toNat ((r.toSlice j (j + v.size + s)).slice (v.size - v.size / 2)
      (r.toSlice j (j + v.size + s)).size) < 2 ^ (32 * (v.size / 2 + s)) := by
    have hsz : ((r.toSlice j (j + v.size + s)).slice (v.size - v.size / 2)
        (r.toSlice j (j + v.size + s)).size).size = v.size / 2 + s := by
      simp only [UInt32Array.Slice.size_slice, hws]; lia
    have := toNat_lt ((r.toSlice j (j + v.size + s)).slice (v.size - v.size / 2)
      (r.toSlice j (j + v.size + s)).size)
    rwa [hsz] at this
  -- The top limb of `vₕ` is that of `v`.
  have hvh : (v.slice (v.size - v.size / 2) v.size)[(v.slice (v.size - v.size / 2)
      v.size).size - 1]'(by simp; lia) ≠ 0 := by
    simp only [UInt32Array.Slice.getElem_slice, UInt32Array.Slice.size_slice]
    have : v.size - v.size / 2 + (min v.size v.size - (v.size - v.size / 2) - 1) = v.size - 1 := by
      lia
    simp only [this]
    exact hvt
  -- The recursive division of `Wₕ` by `vₕ`, and the estimate.
  obtain ⟨hd₁, hd₂⟩ := hrec ((r.toSlice j (j + v.size + s)).slice (v.size - v.size / 2)
    (r.toSlice j (j + v.size + s)).size) (v.slice (v.size - v.size / 2) v.size)
    (by simp; lia) (by simp; lia) hvh
  obtain ⟨he₁, he₂, he₃⟩ := dcEstimate_spec cfg ((r.toSlice j (j + v.size + s)).slice
    (v.size - v.size / 2) (r.toSlice j (j + v.size + s)).size)
    (v.slice (v.size - v.size / 2) v.size) s _ (by simp; lia) hd₁
  simp only [divDCStep]
  generalize divRec ((r.toSlice j (j + v.size + s)).slice (v.size - v.size / 2)
    (r.toSlice j (j + v.size + s)).size) (v.slice (v.size - v.size / 2) v.size) _ _ = d at *
  generalize dcEstimate cfg ((r.toSlice j (j + v.size + s)).slice (v.size - v.size / 2)
    (r.toSlice j (j + v.size + s)).size) (v.slice (v.size - v.size / 2) v.size) s d = e at *
  -- The product `p = Q̂ vₗ`.
  have hM := isMul_mulLimbsWith cfg
  have hps : (mulLimbsWith cfg e.1 (v.slice 0 (v.size - v.size / 2))).size =
      s + (v.size - v.size / 2) := by
    rw [hM.size_eq, UInt32Array.size_toSlice, he₁, UInt32Array.Slice.size_slice]
    lia
  have hpv := hM.toNat_eq e.1 (v.slice 0 (v.size - v.size / 2))
  -- `x = Wₗ + βʰ R₁`, where `R₁ = Wₕ - Q̂ vₕ ≤ Wₕ < β^(m + s)`.
  have hR1 : toNat (e.2.toSlice 0 (v.size / 2 + s)) = toNat e.2 :=
    toNat_toSlice_of_lt _ _ (by lia)
  -- `R₁` goes into zero limbs above `Wₗ`, so copying it adds it.
  have hxs : (copyPadded ((r.toSlice j (j + v.size + s)).slice 0 (v.size - v.size / 2))
      (v.size + s + 1)).size = v.size + s + 1 := size_copyPadded _ _ (by simp; lia)
  obtain ⟨hxsz, hxv⟩ := ofLimbs_copySlice e.2
    (copyPadded ((r.toSlice j (j + v.size + s)).slice 0 (v.size - v.size / 2)) (v.size + s + 1))
    (v.size - v.size / 2) (v.size / 2 + s) (by rw [hxs]; lia)
  rw [hxs] at hxsz
  have hz : ofLimbs (((copyPadded ((r.toSlice j (j + v.size + s)).slice 0
      (v.size - v.size / 2)) (v.size + s + 1)).toList.drop (v.size - v.size / 2)).take
        (min (v.size / 2 + s) e.2.size)) = 0 := by
    rw [toList_copyPadded, List.drop_append_of_le_length (by simp; lia)]
    simp only [UInt32Array.Slice.size_slice, UInt32Array.size_toSlice]
    rw [List.drop_of_length_le (by simp; lia), List.nil_append, List.take_replicate,
      ofLimbs_replicate_zero]
  have hXd : ofLimbs (copyPadded ((r.toSlice j (j + v.size + s)).slice 0 (v.size - v.size / 2))
      (v.size + s + 1)).toList = toNat ((r.toSlice j (j + v.size + s)).slice 0
        (v.size - v.size / 2)) := by
    rw [← toNat_toSlice, toNat_copyPadded]
  have hR1' : ofLimbs (e.2.toList.take (v.size / 2 + s)) = toNat e.2 := by
    rw [← hR1]
    simp only [toNat, UInt32Array.copy_toSlice, UInt32Array.toList_extract,
      List.extract_eq_take_drop, List.drop_zero, Nat.sub_zero]
  rw [hz, Nat.mul_zero, Nat.add_zero, hXd, hR1', ← toNat_toSlice] at hxv
  generalize e.2.copySlice 0 (copyPadded ((r.toSlice j (j + v.size + s)).slice 0
    (v.size - v.size / 2)) (v.size + s + 1)) (v.size - v.size / 2) (v.size / 2 + s) = x at *
  generalize mulLimbsWith cfg e.1 (v.slice 0 (v.size - v.size / 2)) = p at *
  -- The numbers.
  rw [hW] at hsplitW
  generalize hWdef : toNat r / 2 ^ (32 * j) = W at *
  generalize toNat ((r.toSlice j (j + v.size + s)).slice 0 (v.size - v.size / 2)) = Wl at *
  generalize toNat ((r.toSlice j (j + v.size + s)).slice (v.size - v.size / 2)
    (r.toSlice j (j + v.size + s)).size) = Wh at *
  generalize toNat (v.slice 0 (v.size - v.size / 2)) = Bl at *
  generalize toNat (v.slice (v.size - v.size / 2) v.size) = Bh at *
  generalize hβ : 2 ^ (32 * (v.size - v.size / 2)) = β at *
  have hβpos : 0 < β := by rw [← hβ]; exact Nat.two_pow_pos _
  have hBh : 0 < Bh := Nat.lt_of_le_of_lt (Nat.zero_le _) hd₂
  have hVpos : 0 < toNat v := by
    have : Bh ≤ β * Bh := Nat.le_mul_of_pos_left _ hβpos
    lia
  -- The digit `Q = ⌊W / v⌋` is below `βˢ` and at most the estimate.
  have hQlt : W / toNat v < 2 ^ (32 * s) := by
    rw [Nat.div_lt_iff_lt_mul hVpos, ← hWdef, Nat.div_lt_iff_lt_mul hP, Nat.mul_comm (2 ^ _),
      Nat.mul_assoc, ← Nat.pow_add, show 32 * s + 32 * j = 32 * (j + s) by lia]
    exact hbound
  have hq₁ : toNat d.1 = Wh / Bh :=
    (Nat.div_eq_of_lt_le (by lia) (by rw [Nat.add_mul, Nat.one_mul]; lia)).symm
  have hQle : W / toNat v ≤ Wh / Bh :=
    le_div_of_estimate (Nat.div_mul_le_self W (toNat v))
      (by rw [Nat.add_mul, Nat.one_mul, Nat.mul_comm Wh β]; lia)
      (by rw [Nat.mul_comm]; lia) hBh
  have hge : W / toNat v ≤ toNat e.1 := by rw [he₂, hq₁]; lia
  -- The correction.
  have hPlt : toNat p < 2 ^ (32 * (s + (v.size - v.size / 2))) :=
    calc toNat p < 2 ^ (32 * p.size) := Nat.lt_of_lt_of_le (toNat_lt p) (Nat.le_of_eq (by simp))
      _ = 2 ^ (32 * (s + (v.size - v.size / 2))) := by rw [hps]
  have hcap : toNat p + toNat v < 2 ^ (32 * x.size) := by
    rw [hxsz]
    have h₁ : 2 ^ (32 * (s + (v.size - v.size / 2))) ≤ 2 ^ (32 * (v.size + s)) :=
      Nat.pow_le_pow_right (by decide) (by lia)
    have h₂ : 2 ^ (32 * v.size) ≤ 2 ^ (32 * (v.size + s)) :=
      Nat.pow_le_pow_right (by decide) (by lia)
    have h₃ : 2 ^ (32 * (v.size + s + 1)) = 2 ^ (32 * (v.size + s)) * 2 ^ 32 := by
      rw [← Nat.pow_add, show 32 * (v.size + s) + 32 = 32 * (v.size + s + 1) by lia]
    have : 2 ^ (32 * (v.size + s)) * 2 ≤ 2 ^ (32 * (v.size + s)) * 2 ^ 32 :=
      Nat.mul_le_mul_left _ (by decide)
    lia
  have hinv : toNat x + toNat e.1 * toNat v = toNat p + W := by
    rw [hxv, hpv, ← hsplitV, ← hsplitW, ← he₃, Nat.mul_add, Nat.mul_add]
    rw [Nat.mul_comm (toNat e.1) (β * Bh), Nat.mul_assoc, Nat.mul_comm Bh (toNat e.1)]
    lia
  obtain ⟨hf₁, hf₂, hf₃, hf₄, hf₅⟩ := dcFix_spec v p x e.1 W hVpos (by lia) (by lia) hcap hinv
    hge
  generalize dcFix v p x e.1 = f at *
  -- The remainder of the window, `W mod v = f.1 - p`, and `Q v = W - (W mod v)`.
  have hrw : W - W / toNat v * toNat v < toNat v := by
    have := Nat.div_add_mod W (toNat v)
    have := Nat.mod_lt W hVpos
    have : W / toNat v * toNat v = toNat v * (W / toNat v) := Nat.mul_comm _ _
    lia
  have hfit₁ : 0 + p.toSlice.size ≤ f.1.size := by
    rw [UInt32Array.size_toSlice, hps, hf₁, hxsz]; lia
  have hsub₁ := toNat_subInto_of_le f.1 0 p hfit₁
    (by rw [Nat.mul_zero, Nat.pow_zero, Nat.one_mul]; exact hf₃)
  rw [Nat.mul_zero, Nat.pow_zero, Nat.one_mul] at hsub₁
  have hrem : toNat ((subInto f.1 0 p).toSlice 0 (v.size + s)) = W - W / toNat v * toNat v := by
    have : 2 ^ (32 * v.size) ≤ 2 ^ (32 * (v.size + s)) :=
      Nat.pow_le_pow_right (by decide) (by lia)
    rw [toNat_toSlice_of_lt _ _ (by rw [hsub₁]; lia), hsub₁]
    lia
  -- The window of `r` becomes `W mod v`: `r` goes down by `βʲ Q v`.
  have hrs : (subInto f.1 0 p).size = v.size + s + 1 := by
    rw [size_subInto _ _ _ hfit₁, hf₁, hxsz]
  obtain ⟨hr₁, hr₂⟩ := ofLimbs_copySlice (subInto f.1 0 p) r j (v.size + s) (by lia)
  have hwin : ofLimbs ((r.toList.drop j).take (min (v.size + s) (subInto f.1 0 p).size)) = W := by
    rw [hrs, Nat.min_eq_left (by lia), ← hW]
    simp only [toNat, UInt32Array.copy_toSlice, UInt32Array.toList_extract,
      List.extract_eq_take_drop]
    rw [show j + v.size + s - j = v.size + s by lia]
  have hremv : ofLimbs ((subInto f.1 0 p).toList.take (v.size + s)) =
      W - W / toNat v * toNat v := by
    rw [← hrem]
    simp only [toNat, UInt32Array.copy_toSlice, UInt32Array.toList_extract,
      List.extract_eq_take_drop, List.drop_zero, Nat.sub_zero]
  rw [hwin, hremv] at hr₂
  have hPW : W / toNat v * toNat v ≤ W := Nat.div_mul_le_self _ _
  have hrW : 2 ^ (32 * j) * W ≤ toNat r := by
    rw [← hWdef]; exact Nat.mul_div_le _ _
  have hr' : toNat ((subInto f.1 0 p).copySlice 0 r j (v.size + s)) =
      toNat r - 2 ^ (32 * j) * (W / toNat v * toNat v) := by
    rw [toNat_toSlice, toNat_toSlice] at *
    have hm : 2 ^ (32 * j) * (W - W / toNat v * toNat v) =
        2 ^ (32 * j) * W - 2 ^ (32 * j) * (W / toNat v * toNat v) := Nat.mul_sub _ _ _
    have := Nat.mul_le_mul_left (2 ^ (32 * j)) hPW
    lia
  -- The block of `q` is zero, since `βʲ⁺ˢ` divides `q`, so copying `Q` there adds `βʲ Q`.
  obtain ⟨hq₁, hq₂⟩ := ofLimbs_copySlice f.2 q j s (by lia)
  have hfs : f.2.size = s := by rw [hf₂, he₁]
  have hqwin : ofLimbs ((q.toList.drop j).take (min s f.2.size)) = 0 := by
    rw [hfs, Nat.min_self]
    have hsplit := ofLimbs_append (q.toList.take (j + s)) (q.toList.drop (j + s))
    rw [List.take_append_drop, List.length_take, UInt32Array.length_toList,
      Nat.min_eq_left (by lia)] at hsplit
    have hlow : ofLimbs (q.toList.take (j + s)) = 0 := by
      have hd : 2 ^ (32 * (j + s)) ∣ ofLimbs (q.toList.take (j + s)) := by
        have : 2 ^ (32 * (j + s)) ∣ ofLimbs q.toList := by rw [← toNat_toSlice]; exact hdiv
        rw [hsplit] at this
        exact (Nat.dvd_add_left (Nat.dvd_mul_right _ _)).1 this
      exact Nat.eq_zero_of_dvd_of_lt hd (ofLimbs_take_lt _ _)
    have h2 := ofLimbs_append (q.toList.take j) ((q.toList.drop j).take s)
    rw [← List.take_add, List.length_take, UInt32Array.length_toList,
      Nat.min_eq_left (by lia), hlow] at h2
    have hpos : 0 < 2 ^ (32 * j) := Nat.two_pow_pos _
    rcases Nat.eq_zero_or_pos (ofLimbs ((q.toList.drop j).take s)) with h | h
    · exact h
    · have := Nat.mul_pos hpos h
      lia
  rw [hqwin, Nat.mul_zero, Nat.add_zero, List.take_of_length_le (by simp; lia)] at hq₂
  have hq' : toNat (f.2.copySlice 0 q j s) = toNat q + 2 ^ (32 * j) * toNat f.2 := by
    rw [toNat_toSlice, toNat_toSlice, toNat_toSlice]; exact hq₂
  refine ⟨hr₁, hq₁, ?_, ?_, ?_⟩
  · rw [hq', hr', hf₄]
    have := Nat.mul_le_mul_left (2 ^ (32 * j)) hPW
    rw [Nat.add_mul, Nat.mul_assoc]
    lia
  · rw [hr', ← hWdef]
    exact dc_rem_lt hP hVpos
  · rw [hq', hf₄]
    exact Nat.dvd_add (Nat.dvd_trans (Nat.pow_dvd_pow 2 (by lia)) hdiv) (Nat.dvd_mul_right _ _)

/-! ## The blocks -/

/-- Computes the blocks of quotient limbs below `t m`, from the top down, with `divDCStep`. -/
def divDCLoop (cfg : Config) (v : UInt32Array.Slice) (h4 : 4 ≤ v.size)
    (divRec : (u' v' : UInt32Array.Slice) → v'.size < v.size → 2 ≤ v'.size →
      UInt32Array × UInt32Array) :
    Nat → UInt32Array → UInt32Array → UInt32Array × UInt32Array
  | 0, r, q => (q, r)
  | t + 1, r, q =>
    let st := divDCStep cfg v h4 divRec (v.size / 2) (t * (v.size / 2)) r q
    divDCLoop cfg v h4 divRec t st.1 st.2

private theorem divDCLoop_spec (cfg : Config) (v : UInt32Array.Slice) (h4 : 4 ≤ v.size)
    (divRec : (u' v' : UInt32Array.Slice) → v'.size < v.size → 2 ≤ v'.size →
      UInt32Array × UInt32Array)
    (hrec : ∀ u' v' h h', v'[v'.size - 1]'(by lia) ≠ 0 →
      toNat (divRec u' v' h h').1 * toNat v' + toNat (divRec u' v' h h').2 = toNat u' ∧
        toNat (divRec u' v' h h').2 < toNat v')
    (hvt : v[v.size - 1]'(by lia) ≠ 0) (t : Nat) (r q : UInt32Array)
    (hr : t * (v.size / 2) + v.size ≤ r.size) (hq : t * (v.size / 2) ≤ q.size)
    (hbound : toNat r < toNat v * 2 ^ (32 * (t * (v.size / 2))))
    (hdiv : 2 ^ (32 * (t * (v.size / 2))) ∣ toNat q) :
    toNat (divDCLoop cfg v h4 divRec t r q).1 * toNat v +
          toNat (divDCLoop cfg v h4 divRec t r q).2 = toNat q * toNat v + toNat r ∧
      toNat (divDCLoop cfg v h4 divRec t r q).2 < toNat v := by
  induction t generalizing r q with
  | zero =>
    rw [divDCLoop]
    exact ⟨rfl, by simpa using hbound⟩
  | succ t ih =>
    have ht : (t + 1) * (v.size / 2) = t * (v.size / 2) + v.size / 2 := by
      rw [Nat.add_mul, Nat.one_mul]
    rw [ht] at hr hq hbound hdiv
    obtain ⟨s₁, s₂, s₃, s₄, s₅⟩ := divDCStep_spec cfg v h4 divRec hrec hvt (v.size / 2)
      (t * (v.size / 2)) (by lia) (Nat.le_refl _) r q (by lia) hq hbound hdiv
    obtain ⟨i₁, i₂⟩ := ih _ _ (by rw [s₁]; lia) (by rw [s₂]; lia) s₄ s₅
    simp only [divDCLoop]
    exact ⟨by rw [i₁, s₃], i₂⟩

/--
`u / v` and `u % v` by blocks of `m = n / 2` quotient limbs, for a divisor of at least four limbs
with a nonzero top limb, untrimmed. The quotient has the `K` limbs of the quotient of
`divRemBasecase`: a top block of `K % m` limbs, when there is one, then `⌊K / m⌋` blocks of `m`
limbs; the remainder has `K + n` limbs.
-/
public def divRemDC (cfg : Config) (u v : UInt32Array.Slice) (h4 : 4 ≤ v.size)
    (divRec : (u' v' : UInt32Array.Slice) → v'.size < v.size → 2 ≤ v'.size →
      UInt32Array × UInt32Array) : UInt32Array × UInt32Array :=
  let K := max (u.size + 1) v.size - v.size
  let t := K / (v.size / 2)
  let r := copyPadded u (K + v.size)
  let q : UInt32Array := .replicate K 0
  if K % (v.size / 2) = 0 then
    divDCLoop cfg v h4 divRec t r q
  else
    let st := divDCStep cfg v h4 divRec (K % (v.size / 2)) (t * (v.size / 2)) r q
    divDCLoop cfg v h4 divRec t st.1 st.2

public theorem divRemDC_spec (cfg : Config) (u v : UInt32Array.Slice) (h4 : 4 ≤ v.size)
    (divRec : (u' v' : UInt32Array.Slice) → v'.size < v.size → 2 ≤ v'.size →
      UInt32Array × UInt32Array)
    (hrec : ∀ u' v' h h', v'[v'.size - 1]'(by lia) ≠ 0 →
      toNat (divRec u' v' h h').1 * toNat v' + toNat (divRec u' v' h h').2 = toNat u' ∧
        toNat (divRec u' v' h h').2 < toNat v')
    (hvt : v[v.size - 1]'(by lia) ≠ 0) :
    toNat (divRemDC cfg u v h4 divRec).1 * toNat v + toNat (divRemDC cfg u v h4 divRec).2 =
        toNat u ∧
      toNat (divRemDC cfg u v h4 divRec).2 < toNat v := by
  have hvt' : 1 ≤ (v[v.size - 1]'(by lia)).toNat := by
    rcases Nat.eq_zero_or_pos (v[v.size - 1]'(by lia)).toNat with h | h
    · exact absurd (UInt32.toNat_inj.1 (by simpa using h)) hvt
    · exact h
  have hU := toNat_lt u
  unfold divRemDC
  dsimp only
  have hKm := Nat.div_add_mod (max (u.size + 1) v.size - v.size) (v.size / 2)
  have hKu : u.size + 1 ≤ max (u.size + 1) v.size - v.size + v.size := by lia
  generalize max (u.size + 1) v.size - v.size = K at *
  -- `u < β^u.size ≤ β^(n - 1) β^K ≤ v β^K`.
  have hbound : toNat u < toNat v * 2 ^ (32 * K) := by
    have h₁ : 2 ^ (32 * u.size) ≤ 2 ^ (32 * (v.size - 1)) * 2 ^ (32 * K) := by
      rw [← Nat.pow_add]
      exact Nat.pow_le_pow_right (by decide) (by lia)
    have h₂ : 2 ^ (32 * (v.size - 1)) ≤ toNat v := by
      have := top_limb_le v (by lia)
      have := Nat.mul_le_mul_right (2 ^ (32 * (v.size - 1))) hvt'
      lia
    have := Nat.mul_le_mul_right (2 ^ (32 * K)) h₂
    lia
  have h0 := toNat_zeros K
  have hrs : (copyPadded u (K + v.size)).size = K + v.size := size_copyPadded _ _ (by lia)
  have hr0 := toNat_copyPadded u (K + v.size)
  generalize copyPadded u (K + v.size) = r at *
  generalize hqdef : UInt32Array.replicate K 0 = q at *
  have hqs : q.size = K := by rw [← hqdef]; simp
  rw [Nat.mul_comm] at hKm
  by_cases hz : K % (v.size / 2) = 0
  · rw [ite_eq_left hz]
    rw [hz, Nat.add_zero] at hKm
    have h := divDCLoop_spec cfg v h4 divRec hrec hvt (K / (v.size / 2)) r q (by lia) (by lia)
      (by rw [hKm, hr0]; exact hbound) (by rw [h0]; exact Nat.dvd_zero _)
    rw [h0, Nat.zero_mul, Nat.zero_add, hr0] at h
    exact h
  · rw [ite_eq_right hz]
    obtain ⟨s₁, s₂, s₃, s₄, s₅⟩ := divDCStep_spec cfg v h4 divRec hrec hvt
      (K % (v.size / 2)) (K / (v.size / 2) * (v.size / 2)) (by lia)
      (Nat.le_of_lt (Nat.mod_lt _ (by lia))) r q (by lia) (by lia)
      (by rw [hKm, hr0]; exact hbound) (by rw [h0]; exact Nat.dvd_zero _)
    have h := divDCLoop_spec cfg v h4 divRec hrec hvt (K / (v.size / 2)) _ _ (by rw [s₁]; lia)
      (by rw [s₂]; lia) s₄ s₅
    rw [s₃, h0, Nat.zero_mul, Nat.zero_add, hr0] at h
    exact h

/-! ## The dispatch -/

/--
`u / v` and `u % v` for a divisor of at least two limbs with a nonzero top limb, untrimmed: by
blocks with `divRemDC` from `cfg.divDC` limbs, whose digits are estimated with `divRemWith`
again, and with `divRemBasecase` below.
-/
public def divRemWith (cfg : Config) (u v : UInt32Array.Slice) (hn : 2 ≤ v.size) :
    UInt32Array × UInt32Array :=
  if h : cfg.divDC ≤ v.size then
    divRemDC cfg u v (Nat.le_trans cfg.four_le_divDC h) fun u' v' _ hn' => divRemWith cfg u' v' hn'
  else
    divRemBasecase u v hn
termination_by v.size

public theorem divRemWith_spec (cfg : Config) (u v : UInt32Array.Slice) (hn : 2 ≤ v.size)
    (hvt : v[v.size - 1]'(by lia) ≠ 0) :
    toNat (divRemWith cfg u v hn).1 * toNat v + toNat (divRemWith cfg u v hn).2 = toNat u ∧
      toNat (divRemWith cfg u v hn).2 < toNat v := by
  induction u, v, hn using divRemWith.induct cfg with
  | case1 u v hn h ih =>
    have heq : divRemWith cfg u v hn = divRemDC cfg u v (Nat.le_trans cfg.four_le_divDC h)
        fun u' v' _ hn' => divRemWith cfg u' v' hn' := by
      rw [divRemWith, dite_eq_left h]
    rw [heq]
    exact divRemDC_spec cfg u v _ _ (fun u' v' h' hn' hvt' => ih u' v' h' hn' hvt') hvt
  | case2 u v hn h =>
    have heq : divRemWith cfg u v hn = divRemBasecase u v hn := by
      rw [divRemWith, dite_eq_right h]
    rw [heq]
    exact divRemBasecase_spec u v hn hvt

end MPN
