/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import MPN.Div.Limb
public import MPN.Div.Schoolbook
import all Init.Data.UInt.Log2
import all Init.Data.Fin.Log2

/-!
# Schoolbook division

`divRem` divides by a divisor `v` of `n ≥ 2` limbs by Knuth's Algorithm D, like GMP's schoolbook
division, through `main`'s `MPN.Div.Schoolbook` on `UInt64Array` (`divLoopIn`): one quotient limb
per step from the top down, in one array, the multiply-subtract pass by the in-place fold. From
`div32Threshold` limbs in the divisor, the estimates are GMP's 3-by-2 step with the precomputed
reciprocal `recip32`, checked exactly. `divRem` normalizes the divisor, which keeps the corrections
of the estimates rare, and shifts the remainder back.
-/

open ScalarArray UInt64Array

namespace MPN

/-! ## The estimate with a precomputed reciprocal

GMP's schoolbook division estimates each quotient limb without the hardware divider, by Möller
and Granlund's 3-by-2 step (`udiv_qr_3by2`) with the reciprocal `⌊(β³ - 1) / (v₁ β + v₂)⌋ - β`
of the top two limbs of the normalized divisor (`invert_pi1`). `main`'s `qEstR` checks the
quotient and remainder of the step exactly, `q (v₁ β + v₂) + r = w₂ β² + w₁ β + w₀` with
`r < v₁ β + v₂`, by four products off the dependency chain; then `q` is the quotient of the top
three limbs by the top two, which is never too small. Otherwise it takes `qEst`. So neither the
reciprocal nor the error bound of the step needs a proof.
-/

/-- The reciprocal `⌊(β³ - 1) / (d₁ β + d₀)⌋ - β` of a normalized `d₁ β + d₀`, like GMP's
`invert_pi1`. -/
public def recip32 (d₁ d₀ : UInt64) : UInt64 :=
  let v := recip21 d₁
  let p := d₁ * v + d₀
  let vp : UInt64 × UInt64 :=
    if p < d₀ then
      let mask := (0 : UInt64) - (decide (d₁ ≤ p)).toUInt64
      (v - 1 + mask, p - d₁ - (mask &&& d₁))
    else (v, p)
  let v := vp.1
  let t₁ := UInt64.mulh d₀ v
  let p := vp.2 + t₁
  if p < t₁ then
    if d₁ ≤ p && (d₁ < p || d₀ ≤ d₀ * v) then v - 2 else v - 1
  else v

/--
The size of the divisor from which `divRem` estimates the quotient limbs with the reciprocal
(`qEstR`). Below it, computing the reciprocal costs more than the steps save, on Zen 3, where the
hardware divider of `qEst` is fast.
-/
public def div32Threshold : Nat := 48

/-- The reciprocal of the top limbs `v₁ v₂` of a divisor of `n` limbs for `divRem`, or `0`. -/
@[inline] public def divRecip (n : USize) (v₁ v₂ : UInt64) : UInt64 :=
  if div32Threshold ≤ n.toNat then recip32 v₁ v₂ else 0

/-! ## The loop -/

/-- The window of `k` limbs of `w` from limb `i`. -/
private theorem win_spec (w : UInt64Array) (i k : USize) (h : i.toNat + k.toNat ≤ w.size)
    (hU : i.toNat + k.toNat < USize.size) :
    (w.uslice i (i + k)).array = w ∧ (w.uslice i (i + k)).start.toNat = i.toNat ∧
      (w.uslice i (i + k)).size.toNat = k.toNat := by
  have hik : (i + k).toNat = i.toNat + k.toNat := USize.toNat_add_of_lt hU
  have hst := uslice_start w i (i + k) (USize.le_iff_toNat_le.2 (by lia)) (by lia)
  have hsp := uslice_stop w i (i + k) (by lia)
  refine ⟨rfl, by rw [hst], ?_⟩
  rw [USlice.toNat_size, hst, hsp]
  lia


/--
`main`'s `divLoopIn` on `UInt64Array`, with the divisor as a slice: divides limbs `0` to
`i + n - 1` of `w` by `v` of `n` limbs, with the top limbs `v₁` and `v₂`, in place, the quotient in
limbs `n` to `n + i - 1` and the remainder in limbs `0` to `n - 1`.
-/
public def divLoopIn (w : UInt64Array) (v : USlice) (v₁ v₂ dv : UInt64) (n i : USize) :
    UInt64Array :=
  if h : n ≤ v.size then Schoolbook.divLoopIn w v.array v.start n (v.loopBound h) v₁ v₂ dv i else w

private theorem divLoopIn_spec (w : UInt64Array) (v : USlice) (v₁ v₂ dv : UInt64) (n i : USize)
    (hn : v.size = n) (hn₂ : 2 ≤ n.toNat) (hk : i.toNat + n.toNat ≤ w.size)
    (hU : w.size < USize.size) (hv₀ : 0 < v.toNat)
    (hv₁ : v₁ = v.array[v.start.toNat + n.toNat - 1]!)
    (hv₂ : v₂ = v.array[v.start.toNat + n.toNat - 2]!)
    (hR : w.valAt 0 (i.toNat + n.toNat) < v.toNat * 2 ^ (64 * i.toNat)) :
    (divLoopIn w v v₁ v₂ dv n i).size = w.size ∧
      (∀ j, i.toNat + n.toNat ≤ j → (divLoopIn w v v₁ v₂ dv n i)[j]! = w[j]!) ∧
      v.toNat * (divLoopIn w v v₁ v₂ dv n i).valAt n.toNat i.toNat +
          (divLoopIn w v v₁ v₂ dv n i).valAt 0 n.toNat = w.valAt 0 (i.toNat + n.toNat) ∧
      (divLoopIn w v v₁ v₂ dv n i).valAt 0 n.toNat < v.toNat := by
  have hnv : n ≤ v.size := by rw [hn]; exact USize.le_refl _
  have hvv : v.toNat = v.array.valAt v.start.toNat n.toNat := by rw [USlice.toNat_eq_valAt, hn]
  rw [divLoopIn, dite_eq_left_of_eq_true (eq_true hnv), hvv]
  rw [hvv] at hv₀ hR
  exact Schoolbook.divLoopIn_spec w v.array v.start n (v.loopBound hnv) v₁ v₂ dv i hn₂ hk hU hv₀
    hv₁ hv₂ hR

/-! ## Division -/

/--
Writes the limbs of `a / b` into the first `a.size - b.size + 1` limbs of `q`, and those of `a % b`
into the first `b.size` limbs of `r`, like GMP's `mpn_tdiv_qr`. It requires
`0 < b.size ≤ a.size` and a nonzero top limb of `b`. A divisor of one limb uses `divRem1`; a
longer one is normalized, like in GMP: `a` and `b` are shifted left by the `k` bits that set the
top bit of `b`, which keeps the corrections of the estimates in `divStepIn` rare, and the remainder
is shifted back at the end. The quotient of `a 2ᵏ` by `b 2ᵏ` is `a / b` and the remainder
`(a % b) 2ᵏ`.
-/
public def divRem (q r a b : USlice) : UInt64Array × UInt64Array :=
  if b.size ≤ 1 then
    let p := divRem1 q a b.array[b.start.toNat]!
    (p.1, r.array.set! r.start.toNat p.2)
  else
    let n := b.size
    let k := 63 - (b.array[b.start.toNat + n.toNat - 1]!).log2.toNat
    let v := (shiftLeft (UInt64Array.replicate n.toNat 0).toUSlice b k).1
    let p := shiftLeft (UInt64Array.replicate (a.size.toNat + 1) 0).toUSlice a k
    let w := p.1.set! a.size.toNat p.2
    let res := divLoopIn w v.toUSlice v[n.toNat - 1]! v[n.toNat - 2]!
      (divRecip n v[n.toNat - 1]! v[n.toNat - 2]!) n (a.size + 1 - n)
    ((add1 q (res.uslice n (n + (a.size + 1 - n))) 0).1, shiftRight r (res.uslice 0 n) k)

@[simp] public theorem size_divRem_fst (q r a b : USlice) :
    (divRem q r a b).1.size = q.array.size := by
  rw [divRem]
  split
  · exact size_divRem1 ..
  · exact size_add1 ..

@[simp] public theorem size_divRem_snd (q r a b : USlice) :
    (divRem q r a b).2.size = r.array.size := by
  rw [divRem]
  split
  · simp
  · exact size_shiftRight ..

private theorem _root_.UInt64.toNat_log2 (x : UInt64) :
    x.log2.toNat = _root_.Nat.log2 x.toNat :=
  rfl

/-- `a 2ᵏ`, for `k < 64`, shifted into `len` zero limbs. -/
private theorem shift_fresh (a : USlice) (k len : Nat) (hk : k < 64) (hlen : a.size.toNat ≤ len)
    (hU : len < USize.size) :
    (shiftLeft (UInt64Array.replicate len 0).toUSlice a k).1.size = len ∧
      (shiftLeft (UInt64Array.replicate len 0).toUSlice a k).1.valAt 0 a.size.toNat +
          2 ^ (64 * a.size.toNat) * (shiftLeft (UInt64Array.replicate len 0).toUSlice a k).2.toNat =
        a.toNat * 2 ^ k := by
  have hsz := size_toUSlice (UInt64Array.replicate len 0) (by simp; exact hU)
  simp only [UInt64Array.size_replicate] at hsz
  have h := valAt_shiftLeft (UInt64Array.replicate len 0).toUSlice a k (by
    rw [hsz, Nat.div_eq_of_lt hk]; lia)
  rw [Nat.div_eq_of_lt hk, Nat.zero_add, start_toUSlice, USize.toNat_zero] at h
  exact ⟨by simp, h⟩

/-- The divisor is at least `β^(n-1)` and below `β^(n-1) 2^(log₂ t + 1)`, for its top limb `t`. -/
private theorem top_bounds (b : USlice) (h₀ : 0 < b.size.toNat)
    (ht : b.array[b.start.toNat + b.size.toNat - 1]! ≠ 0) :
    2 ^ (64 * (b.size.toNat - 1)) ≤ b.toNat ∧
      b.toNat < 2 ^ (64 * (b.size.toNat - 1)) *
        2 ^ ((b.array[b.start.toNat + b.size.toNat - 1]!).log2.toNat + 1) := by
  have e := UInt64Array.valAt_add b.array b.start.toNat (b.size.toNat - 1) 1
  rw [show b.size.toNat - 1 + 1 = b.size.toNat by lia, valAt_one,
    show b.start.toNat + (b.size.toNat - 1) = b.start.toNat + b.size.toNat - 1 by lia] at e
  rw [USlice.toNat_eq_valAt, e, UInt64.toNat_log2]
  have hlo := valAt_lt b.array b.start.toNat (b.size.toNat - 1)
  have ht' : 1 ≤ (b.array[b.start.toNat + b.size.toNat - 1]!).toNat := by
    refine Nat.pos_of_ne_zero fun e => ht (UInt64.toNat_inj.1 (by rw [e]; rfl))
  have hlog := Nat.lt_log2_self (n := (b.array[b.start.toNat + b.size.toNat - 1]!).toNat)
  generalize (b.array[b.start.toNat + b.size.toNat - 1]!).toNat = t at *
  generalize b.array.valAt _ _ = L at *
  generalize 2 ^ (64 * (b.size.toNat - 1)) = P at *
  have h₁ := Nat.mul_le_mul_left P ht'
  have h₂ := Nat.mul_le_mul_left P (show t + 1 ≤ 2 ^ (_root_.Nat.log2 t + 1) from hlog)
  rw [Nat.mul_add, Nat.mul_one] at h₂
  constructor <;> lia

private theorem divRem_long (q r a b : USlice) (h₁ : ¬b.size ≤ 1) (hab : b.size ≤ a.size)
    (ht : b.array[b.start.toNat + b.size.toNat - 1]! ≠ 0)
    (hq : a.size.toNat - b.size.toNat + 1 ≤ q.size.toNat) (hr : b.size ≤ r.size)
    (hU : a.size.toNat + 1 < USize.size) :
    (divRem q r a b).1.valAt q.start.toNat (a.size.toNat - b.size.toNat + 1) =
        a.toNat / b.toNat ∧
      (divRem q r a b).2.valAt r.start.toNat b.size.toNat = a.toNat % b.toNat ∧
      (∀ i, (i < q.start.toNat ∨ q.start.toNat + (a.size.toNat - b.size.toNat + 1) ≤ i) →
        (divRem q r a b).1[i]! = q.array[i]!) ∧
      (∀ i, (i < r.start.toNat ∨ r.start.toNat + b.size.toNat ≤ i) →
        (divRem q r a b).2[i]! = r.array[i]!) := by
  have hn₂ : 2 ≤ b.size.toNat := by
    have := fun h => h₁ (USize.le_iff_toNat_le.2 h); rw [USize.toNat_one] at this; lia
  have hab' := USize.le_iff_toNat_le.1 hab
  have hr' := USize.le_iff_toNat_le.1 hr
  have hbU := b.size.toNat_lt_size
  -- The shift and the bounds of `b`.
  generalize hk : 63 - (b.array[b.start.toNat + b.size.toNat - 1]!).log2.toNat = k
  have hlog : (b.array[b.start.toNat + b.size.toNat - 1]!).log2.toNat ≤ 63 := by
    rw [UInt64.toNat_log2]
    have := (b.array[b.start.toNat + b.size.toNat - 1]!).toNat_lt
    have := (Nat.log2_lt (n := (b.array[b.start.toNat + b.size.toNat - 1]!).toNat) (k := 64)
      (fun e => ht (UInt64.toNat_inj.1 (by rw [e]; rfl)))).2 this
    lia
  have hk64 : k < 64 := by lia
  obtain ⟨hb₁, hb₂⟩ := top_bounds b (by lia) ht
  have hβn : 2 ^ (64 * (b.size.toNat - 1)) * 2 ^ (_root_.Nat.log2
      (b.array[b.start.toNat + b.size.toNat - 1]!).toNat + 1) * 2 ^ k =
      2 ^ (64 * b.size.toNat) := by
    rw [← Nat.pow_add, ← Nat.pow_add]; congr 1; rw [← UInt64.toNat_log2]; lia
  rw [UInt64.toNat_log2] at hb₂
  have hbk : b.toNat * 2 ^ k < 2 ^ (64 * b.size.toNat) := by
    rw [← hβn]; exact Nat.mul_lt_mul_of_pos_right hb₂ (Nat.two_pow_pos _)
  -- The normalized divisor `v`.
  obtain ⟨v₁, v₂⟩ := shift_fresh b k b.size.toNat hk64 (Nat.le_refl _) hbU
  generalize hv : (shiftLeft (UInt64Array.replicate b.size.toNat 0).toUSlice b k) = pv at v₁ v₂
  have hV : pv.1.valAt 0 b.size.toNat = b.toNat * 2 ^ k := by
    have := valAt_lt pv.1 0 b.size.toNat
    have hc : pv.2.toNat = 0 := by
      rcases Nat.eq_zero_or_pos pv.2.toNat with h | h
      · exact h
      · have := Nat.mul_le_mul_left (2 ^ (64 * b.size.toNat)) h; lia
    rw [hc, Nat.mul_zero, Nat.add_zero] at v₂
    exact v₂
  have hVpos : 0 < b.toNat * 2 ^ k := by
    have := Nat.two_pow_pos (64 * (b.size.toNat - 1))
    exact Nat.mul_pos (by lia) (Nat.two_pow_pos _)
  have hvU : pv.1.toUSlice.size = b.size := by
    apply USize.toNat_inj.1
    rw [size_toUSlice _ (by rw [v₁]; exact hbU), v₁]
  have hvT : pv.1.toUSlice.toNat = b.toNat * 2 ^ k := by
    rw [USlice.toNat_eq_valAt, hvU, start_toUSlice, USize.toNat_zero, array_toUSlice, hV]
  -- The normalized dividend `w`, with one more limb.
  obtain ⟨w₁, w₂⟩ := shift_fresh a k (a.size.toNat + 1) hk64 (by lia) hU
  generalize hp : shiftLeft (UInt64Array.replicate (a.size.toNat + 1) 0).toUSlice a k = pw
    at w₁ w₂
  have hwsz : (pw.1.set! a.size.toNat pw.2).size = a.size.toNat + 1 := by simp [w₁]
  have hW : (pw.1.set! a.size.toNat pw.2).valAt 0 (a.size.toNat + 1) = a.toNat * 2 ^ k := by
    rw [UInt64Array.valAt_add, valAt_one, Nat.zero_add, getElem!_set!_self _ _ _ (by lia),
      valAt_congr (b := pw.1) _ fun i _ hi => getElem!_set!_of_ne _ _ (by lia)]
    exact w₂
  -- The loop.
  have hm : (a.size + 1 - b.size).toNat = a.size.toNat + 1 - b.size.toNat := by
    have h1 : (a.size + 1).toNat = a.size.toNat + 1 :=
      (USize.toNat_add_of_lt (a := a.size) (b := 1) (by rw [USize.toNat_one]; lia)).trans
        (by rw [USize.toNat_one])
    rw [USize.toNat_sub_of_le _ _ (USize.le_iff_toNat_le.2 (by rw [h1]; lia)), h1]
  have hqb : q.start.toNat + q.size.toNat ≤ q.array.size := by
    have := q.toNat_size; have := q.stop_le_size; lia
  have hR : (pw.1.set! a.size.toNat pw.2).valAt 0 ((a.size + 1 - b.size).toNat + b.size.toNat) <
      pv.1.toUSlice.toNat * 2 ^ (64 * (a.size + 1 - b.size).toNat) := by
    rw [hm, show a.size.toNat + 1 - b.size.toNat + b.size.toNat = a.size.toNat + 1 by lia, hW,
      hvT]
    have ha := valAt_lt a.array a.start.toNat a.size.toNat
    rw [← USlice.toNat_eq_valAt] at ha
    have e : 2 ^ (64 * a.size.toNat) = 2 ^ (64 * (b.size.toNat - 1)) *
        2 ^ (64 * (a.size.toNat + 1 - b.size.toNat)) := by
      rw [← Nat.pow_add]; congr 1; lia
    have hle := Nat.mul_le_mul_right (2 ^ (64 * (a.size.toNat + 1 - b.size.toNat))) hb₁
    rw [← e] at hle
    have hlt := Nat.mul_lt_mul_of_pos_right ha (Nat.two_pow_pos k)
    rw [Nat.mul_right_comm]
    exact Nat.lt_of_lt_of_le hlt (Nat.mul_le_mul_right _ hle)
  obtain ⟨l₁, l₂, l₄, l₅⟩ := divLoopIn_spec (pw.1.set! a.size.toNat pw.2)
    pv.1.toUSlice (pv.1[b.size.toNat - 1]!) (pv.1[b.size.toNat - 2]!)
    (divRecip b.size pv.1[b.size.toNat - 1]! pv.1[b.size.toNat - 2]!) b.size (a.size + 1 - b.size)
    hvU hn₂ (by rw [hm, hwsz]; lia) (by rw [hwsz]; exact hU) (by rw [hvT]; exact hVpos)
    (by simp) (by simp) hR
  rw [hm, hvT, show a.size.toNat + 1 - b.size.toNat + b.size.toNat = a.size.toNat + 1 by lia,
    hW] at l₄
  rw [hvT] at l₅
  -- Back to `a` and `b`.
  have hQ := Nat.mul_div_mul_right a.toNat b.toNat (Nat.two_pow_pos k)
  have hRm := Nat.mul_mod_mul_right (2 ^ k) a.toNat b.toNat
  rw [← l₄, Nat.mul_add_div hVpos, Nat.div_eq_of_lt l₅, Nat.add_zero] at hQ
  rw [← l₄, Nat.mul_add_mod, Nat.mod_eq_of_lt l₅] at hRm
  generalize hres : divLoopIn (pw.1.set! a.size.toNat pw.2) pv.1.toUSlice
    (pv.1[b.size.toNat - 1]!) (pv.1[b.size.toNat - 2]!)
    (divRecip b.size pv.1[b.size.toNat - 1]! pv.1[b.size.toNat - 2]!) b.size (a.size + 1 - b.size) = res
    at l₁ l₂ l₄ l₅ hQ hRm
  -- The remainder, from limbs `0` to `n - 1`.
  have hsl := win_spec res 0 b.size (by rw [USize.toNat_zero, l₁, hwsz]; lia)
    (by rw [USize.toNat_zero]; lia)
  rw [USize.zero_add] at hsl
  obtain ⟨sa, ss, sz⟩ := hsl
  have hST : (res.uslice 0 b.size).toNat = (a.toNat % b.toNat) * 2 ^ k := by
    rw [USlice.toNat_eq_valAt, sa, ss, sz, USize.toNat_zero, ← hRm]
  have hshr := valAt_shiftRight r (res.uslice 0 b.size) k (by rw [sz]; lia)
  rw [sz, Nat.div_eq_of_lt hk64, Nat.sub_zero, hST, Nat.mul_div_cancel _ (Nat.two_pow_pos _)]
    at hshr
  -- The quotient, from limbs `n` to `n + m - 1`, copied into `q`.
  obtain ⟨qa, qs, qz⟩ := win_spec res b.size (a.size + 1 - b.size) (by rw [l₁, hwsz, hm]; lia)
    (by rw [hm]; lia)
  rw [hm] at qz
  have hQT : (res.uslice b.size (b.size + (a.size + 1 - b.size))).toNat = a.toNat / b.toNat := by
    rw [USlice.toNat_eq_valAt, qa, qs, qz, hQ]
  have hqm : (res.uslice b.size (b.size + (a.size + 1 - b.size))).size ≤ q.size :=
    USize.le_iff_toNat_le.2 (by rw [qz]; lia)
  have hcp := valAt_add1 q (res.uslice b.size (b.size + (a.size + 1 - b.size))) 0 hqm
  rw [qz, hQT, UInt64.toNat_zero, Nat.add_zero] at hcp
  have hqlt : a.toNat / b.toNat < 2 ^ (64 * (a.size.toNat + 1 - b.size.toNat)) := by
    rw [← hQT, USlice.toNat_eq_valAt, qz]; exact valAt_lt ..
  have hcp' : (add1 q (res.uslice b.size (b.size + (a.size + 1 - b.size))) 0).1.valAt
      q.start.toNat (a.size.toNat + 1 - b.size.toNat) = a.toNat / b.toNat := by
    generalize (add1 _ _ _).1.valAt _ _ = V at hcp ⊢
    generalize (add1 _ _ _).2.toNat = c at hcp
    rcases Nat.eq_zero_or_pos c with h0 | h0
    · subst h0; lia
    · have := Nat.mul_le_mul_left (2 ^ (64 * (a.size.toNat + 1 - b.size.toNat))) h0; lia
  have hdiv : divRem q r a b = ((add1 q (res.uslice b.size (b.size + (a.size + 1 - b.size)))
      0).1, shiftRight r (res.uslice 0 b.size) k) := by
    rw [divRem, ite_eq_right h₁]
    dsimp only
    rw [hk, hv, hp, hres]
  rw [hdiv, show a.size.toNat - b.size.toNat + 1 = a.size.toNat + 1 - b.size.toNat by lia]
  refine ⟨hcp', hshr, fun i hi => ?_, fun i hi => ?_⟩
  · exact getElem!_add1 _ _ _ _ (by rw [qz]; lia)
  · exact getElem!_shiftRight _ _ _ _ (by rw [sz, Nat.div_eq_of_lt hk64, Nat.sub_zero]; exact hi)

private theorem divRem_short (q r a b : USlice) (h₁ : b.size ≤ 1) (h₀ : 0 < b.size.toNat)
    (hab : b.size ≤ a.size) (ht : b.array[b.start.toNat + b.size.toNat - 1]! ≠ 0)
    (hq : a.size.toNat - b.size.toNat + 1 ≤ q.size.toNat) (hr : b.size ≤ r.size) :
    (divRem q r a b).1.valAt q.start.toNat (a.size.toNat - b.size.toNat + 1) =
        a.toNat / b.toNat ∧
      (divRem q r a b).2.valAt r.start.toNat b.size.toNat = a.toNat % b.toNat ∧
      (∀ i, (i < q.start.toNat ∨ q.start.toNat + (a.size.toNat - b.size.toNat + 1) ≤ i) →
        (divRem q r a b).1[i]! = q.array[i]!) ∧
      (∀ i, (i < r.start.toNat ∨ r.start.toNat + b.size.toNat ≤ i) →
        (divRem q r a b).2[i]! = r.array[i]!) := by
  have hb1 : b.size.toNat = 1 := by have := USize.le_iff_toNat_le.1 h₁; simp at this; lia
  have hab' := USize.le_iff_toNat_le.1 hab
  have hr' := USize.le_iff_toNat_le.1 hr
  rw [hb1, Nat.add_sub_cancel] at ht
  have hd : 0 < (b.array[b.start.toNat]!).toNat :=
    Nat.pos_of_ne_zero fun e => ht (UInt64.toNat_inj.1 (by rw [e]; rfl))
  have hbv : b.toNat = (b.array[b.start.toNat]!).toNat := by
    rw [USlice.toNat_eq_valAt, hb1, valAt_one]
  have haq : a.size ≤ q.size := USize.le_iff_toNat_le.2 (by lia)
  have hrs : r.start.toNat < r.array.size := by
    have := r.toNat_size; have := r.stop_le_size; lia
  rw [divRem, ite_eq_left h₁, hb1, show a.size.toNat - 1 + 1 = a.size.toNat by lia, hbv]
  refine ⟨valAt_divRem1 _ _ _ hd haq, ?_, fun i hi => getElem!_divRem1 _ _ _ _ (by
    have := USize.le_iff_toNat_le.1 haq; lia), fun i hi => getElem!_set!_of_ne _ _ (by lia)⟩
  rw [valAt_one, getElem!_set!_self _ _ _ hrs, toNat_divRem1_snd _ _ _ hd haq]

/-- `divRem` writes `a / b` into `q`. -/
public theorem valAt_divRem_fst (q r a b : USlice) (h₀ : 0 < b.size.toNat)
    (hab : b.size ≤ a.size) (ht : b.array[b.start.toNat + b.size.toNat - 1]! ≠ 0)
    (hq : a.size.toNat - b.size.toNat + 1 ≤ q.size.toNat) (hr : b.size ≤ r.size)
    (hU : a.size.toNat + 1 < USize.size) :
    (divRem q r a b).1.valAt q.start.toNat (a.size.toNat - b.size.toNat + 1) =
      a.toNat / b.toNat := by
  by_cases h₁ : b.size ≤ 1
  · exact (divRem_short q r a b h₁ h₀ hab ht hq hr).1
  · exact (divRem_long q r a b h₁ hab ht hq hr hU).1

/-- `divRem` writes `a % b` into `r`. -/
public theorem valAt_divRem_snd (q r a b : USlice) (h₀ : 0 < b.size.toNat)
    (hab : b.size ≤ a.size) (ht : b.array[b.start.toNat + b.size.toNat - 1]! ≠ 0)
    (hq : a.size.toNat - b.size.toNat + 1 ≤ q.size.toNat) (hr : b.size ≤ r.size)
    (hU : a.size.toNat + 1 < USize.size) :
    (divRem q r a b).2.valAt r.start.toNat b.size.toNat = a.toNat % b.toNat := by
  by_cases h₁ : b.size ≤ 1
  · exact (divRem_short q r a b h₁ h₀ hab ht hq hr).2.1
  · exact (divRem_long q r a b h₁ hab ht hq hr hU).2.1

/-- `divRem` leaves the limbs of `q` outside the quotient unchanged. -/
public theorem getElem!_divRem_fst (q r a b : USlice) (h₀ : 0 < b.size.toNat)
    (hab : b.size ≤ a.size) (ht : b.array[b.start.toNat + b.size.toNat - 1]! ≠ 0)
    (hq : a.size.toNat - b.size.toNat + 1 ≤ q.size.toNat) (hr : b.size ≤ r.size)
    (hU : a.size.toNat + 1 < USize.size) (i : Nat)
    (hi : i < q.start.toNat ∨ q.start.toNat + (a.size.toNat - b.size.toNat + 1) ≤ i) :
    (divRem q r a b).1[i]! = q.array[i]! := by
  by_cases h₁ : b.size ≤ 1
  · exact (divRem_short q r a b h₁ h₀ hab ht hq hr).2.2.1 i hi
  · exact (divRem_long q r a b h₁ hab ht hq hr hU).2.2.1 i hi

/-- `divRem` leaves the limbs of `r` outside the remainder unchanged. -/
public theorem getElem!_divRem_snd (q r a b : USlice) (h₀ : 0 < b.size.toNat)
    (hab : b.size ≤ a.size) (ht : b.array[b.start.toNat + b.size.toNat - 1]! ≠ 0)
    (hq : a.size.toNat - b.size.toNat + 1 ≤ q.size.toNat) (hr : b.size ≤ r.size)
    (hU : a.size.toNat + 1 < USize.size) (i : Nat)
    (hi : i < r.start.toNat ∨ r.start.toNat + b.size.toNat ≤ i) :
    (divRem q r a b).2[i]! = r.array[i]! := by
  by_cases h₁ : b.size ≤ 1
  · exact (divRem_short q r a b h₁ h₀ hab ht hq hr).2.2.2 i hi
  · exact (divRem_long q r a b h₁ hab ht hq hr hU).2.2.2 i hi

end MPN
