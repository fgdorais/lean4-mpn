/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import MPN.Bitwise

/-!
# Trimming, numbers as limbs, and comparison

The representation-level operations of both widths, on any `WordArray`, with `valAt` as their
specification:

* `trimTo k x` pops the zero limbs on top of `x` while it has more than `k` limbs, in place when
  `x` is not shared; `isTrimmedTo k x` decides that it has nothing to pop. A width that keeps no
  limb for `0` trims to `0` limbs, and one that keeps one limb trims to `1`.
* `writeHalves a o len v` writes `v % 2^(w len)` into the `len` limbs of `a` from `o` on, by
  halves above `16` limbs, so that the operations on `v` stay linear in all; `ofNatW n` is the
  limbs of `n`, one limb for `0`.
* `ltWin` compares two windows of limbs from the top down, like GMP's `mpn_cmp`, with the limbs
  past the end of the shorter one zero; `ltA` compares two arrays, by `ltW` on machine indices.
-/

namespace MPN

namespace WordArray

open LimbArray

variable {A L : Type} [LA : LimbArray A L] [R : WordArray A L]

/-! ## Trimming -/

/-- `x` without its zero limbs on top, keeping `k` limbs at least. -/
@[expose, specialize] public def trimTo (k : Nat) (x : A) : A :=
  if k < LA.size x then
    if R.isZero (LA.get x (LA.size x - 1)) then trimTo k (R.pop x) else x
  else x
termination_by LA.size x
decreasing_by rw [R.size_pop]; lia

/-- Popping the top limb keeps the limbs below it. -/
public theorem valAt_pop (x : A) (n : Nat) (h : n + 1 ≤ LA.size x) :
    valAt (R.pop x) 0 n = valAt x 0 n :=
  valAt_congr n fun i _ hi => R.get_pop x i (by lia)

omit R in
/-- A zero top limb adds nothing to the value. -/
public theorem valAt_of_top_zero (x : A) (n : Nat) (h : LA.val (LA.get x n) = 0) :
    valAt x 0 (n + 1) = valAt x 0 n := by
  rw [valAt_add, valAt_one, Nat.zero_add, h, Nat.mul_zero, Nat.add_zero]

public theorem trimTo_spec (k : Nat) (x : A) :
    valAt (trimTo k x) 0 (LA.size (trimTo k x)) = valAt x 0 (LA.size x) ∧
      LA.size (trimTo k x) ≤ LA.size x ∧ min k (LA.size x) ≤ LA.size (trimTo k x) ∧
      (LA.size (trimTo k x) ≤ k ∨
        LA.val (LA.get (trimTo k x) (LA.size (trimTo k x) - 1)) ≠ 0) := by
  induction hn : LA.size x using Nat.strongRecOn generalizing x with
  | ind n ih =>
  rw [trimTo]
  split
  · rename_i h
    split
    · rename_i hz
      rw [R.isZero_iff] at hz
      obtain ⟨a₁, a₂, a₃, a₄⟩ := ih (n - 1) (by lia) (R.pop x) (by rw [R.size_pop, hn])
      refine ⟨?_, by lia, by lia, a₄⟩
      rw [a₁, valAt_pop x _ (by lia), show n = (n - 1) + 1 by lia,
        valAt_of_top_zero x _ (by rw [← hn]; exact hz)]
      rfl
    · rename_i hz
      rw [R.isZero_iff] at hz
      exact ⟨by rw [hn], by lia, by lia, .inr hz⟩
  · exact ⟨by rw [hn], by lia, by lia, .inl (by lia)⟩

public theorem valAt_trimTo (k : Nat) (x : A) :
    valAt (trimTo k x) 0 (LA.size (trimTo k x)) = valAt x 0 (LA.size x) :=
  (trimTo_spec k x).1

public theorem size_trimTo_le (k : Nat) (x : A) : LA.size (trimTo k x) ≤ LA.size x :=
  (trimTo_spec k x).2.1

public theorem le_size_trimTo (k : Nat) (x : A) : min k (LA.size x) ≤ LA.size (trimTo k x) :=
  (trimTo_spec k x).2.2.1

/-- Whether `x` has at most `k` limbs or a nonzero top limb. -/
@[expose, specialize] public def isTrimmedTo (k : Nat) (x : A) : Bool :=
  decide (LA.size x ≤ k) || !R.isZero (LA.get x (LA.size x - 1))

public theorem isTrimmedTo_iff (k : Nat) (x : A) :
    isTrimmedTo k x = true ↔ (LA.size x ≤ k ∨ LA.val (LA.get x (LA.size x - 1)) ≠ 0) := by
  rw [isTrimmedTo, Bool.or_eq_true, decide_eq_true_eq, Bool.not_eq_true', ← Bool.not_eq_true,
    R.isZero_iff]

public theorem isTrimmedTo_trimTo (k : Nat) (x : A) : isTrimmedTo k (trimTo k x) = true :=
  (isTrimmedTo_iff k _).2 (trimTo_spec k x).2.2.2

public theorem trimTo_of_isTrimmedTo {k : Nat} {x : A} (h : isTrimmedTo k x = true) :
    trimTo k x = x := by
  rw [isTrimmedTo_iff] at h
  rw [trimTo]
  split
  · rename_i hk
    rcases h with h | h
    · lia
    · have hz : R.isZero (LA.get x (LA.size x - 1)) = false := by
        rw [← Bool.not_eq_true, R.isZero_iff]; exact h
      simp [hz]
  · rfl

/-! ## Numbers as limbs -/

/-- Writes `v % 2^(w len)` into the `len` limbs of `a` from `o` on, one limb at a time. -/
@[expose, specialize] public def writeLimbs (a : A) (o : Nat) : Nat → Nat → A
  | 0, _ => a
  | len + 1, v => writeLimbs (LA.set a o v) (o + 1) len (v >>> LA.w)

omit R in
public theorem writeLimbs_eq (a : A) (o len v : Nat) :
    writeLimbs a o len v = writeNat a o len v := by
  induction len generalizing a o v with
  | zero => rfl
  | succ len ih => rw [writeLimbs, writeNat, ih, Nat.shiftRight_eq_div_pow]

/--
Writes the `c` low limbs of the word `u` into `a` from `o` on, low limb first, each masked on words
first, so that the `Nat` it is written from stays below `2^w`, without an allocation.
-/
@[expose, specialize] public def writeWord (a : A) (o : Nat) (u : UInt64) : Nat → A
  | 0 => a
  | c + 1 =>
    writeWord (LA.set a o (u &&& UInt64.ofNat (2 ^ LA.w - 1)).toNat) (o + 1)
      (u >>> LA.w.toUInt64) c

/-- The low `w` bits of a word, for `w ≤ 64`. -/
private theorem toNat_and_mask (u : UInt64) (w : Nat) (hw : w ≤ 64) :
    (u &&& UInt64.ofNat (2 ^ w - 1)).toNat = u.toNat % 2 ^ w := by
  have h : 2 ^ w - 1 < 2 ^ 64 := by
    have := Nat.pow_le_pow_right (show 0 < 2 by decide) hw; have := Nat.one_le_two_pow (n := w); lia
  rw [UInt64.toNat_and, UInt64.toNat_ofNat', Nat.mod_eq_of_lt h, Nat.and_two_pow_sub_one_eq_mod]

/-- What a write of `len` limbs from `o` on must do: keep the size and the other limbs. -/
@[expose] public def WritesOK (a b : A) (o len p : Nat) : Prop :=
  LA.size b = LA.size a ∧ (∀ i, i < o ∨ o + len ≤ i → LA.get b i = LA.get a i) ∧
    (o + len ≤ LA.size a → valAt b o len = p)

omit R in
/-- Two writes, of `c` limbs and of the `d` limbs above them, write `p + 2^(w c) q`. -/
public theorem WritesOK.append {a b d' : A} {o c d p q : Nat} (h₁ : WritesOK a b o c p)
    (h₂ : WritesOK b d' (o + c) d q) : WritesOK a d' o (c + d) (p + 2 ^ (LA.w * c) * q) := by
  obtain ⟨s₁, g₁, v₁⟩ := h₁
  obtain ⟨s₂, g₂, v₂⟩ := h₂
  refine ⟨by rw [s₂, s₁], fun i hi => by rw [g₂ i (by lia), g₁ i (by lia)], fun hs => ?_⟩
  rw [valAt_add, v₂ (by rw [s₁]; lia), valAt_congr (b := b) c (fun i _ _ => g₂ i (by lia)),
    v₁ (by lia)]

omit R in
private theorem writeWord_spec (o : Nat) (u : UInt64) (c : Nat) (a : A) (hc : LA.w * c ≤ 64) :
    WritesOK a (writeWord a o u c) o c (u.toNat % 2 ^ (LA.w * c)) := by
  induction c generalizing a o u with
  | zero => exact ⟨rfl, fun _ _ => rfl, fun _ => by simp [Nat.mod_one]⟩
  | succ c ih =>
    rw [writeWord]
    have hw := LA.w_pos
    have hw64 : LA.w ≤ 64 := by rw [Nat.mul_succ] at hc; lia
    have h₁ : WritesOK a (LA.set a o (u &&& UInt64.ofNat (2 ^ LA.w - 1)).toNat) o 1
        (u.toNat % 2 ^ (LA.w * 1)) :=
      ⟨LA.size_set .., fun i hi => LA.get_set_ne _ _ _ _ (by lia), fun hs => by
        rw [valAt_one, LA.val_get_set_self _ _ _ (by lia), Nat.mul_one, toNat_and_mask _ _ hw64,
          Nat.mod_mod]⟩
    have h := h₁.append (ih (o + 1) (u >>> LA.w.toUInt64)
      (LA.set a o (u &&& UInt64.ofNat (2 ^ LA.w - 1)).toNat) (by rw [Nat.mul_succ] at hc; lia))
    rw [Nat.add_comm 1 c] at h
    refine ⟨h.1, h.2.1, fun hs => ?_⟩
    rw [h.2.2 hs]
    rcases Nat.eq_zero_or_pos c with hc0 | hc0
    · subst hc0; simp [Nat.mod_one]
    -- Then `w < 64`, and the shift of the word is exact.
    have hw64 : LA.w < 64 := by
      rw [Nat.mul_succ] at hc; have := Nat.mul_le_mul_left LA.w hc0; lia
    have hs : (u >>> LA.w.toUInt64).toNat = u.toNat / 2 ^ LA.w := by
      rw [UInt64.toNat_shiftRight, Nat.shiftRight_eq_div_pow]
      congr 2
      simp only [Nat.toUInt64_eq, UInt64.toNat_ofNat', Nat.mod_eq_of_lt (by lia : LA.w < 2 ^ 64),
        Nat.mod_eq_of_lt hw64]
    rw [hs, Nat.mul_one, ← Nat.mod_mul, ← Nat.pow_add, Nat.mul_succ, Nat.add_comm]

/--
Writes `v % 2^(w len)` into the `len` limbs of `a` from `o` on: when a word holds two limbs or
more, `64 / w` limbs from each word of `v`, which `toUInt64` reads without an operation on `Nat`,
and otherwise one limb at a time (`writeLimbs`), which writes a limb from `v` directly.
-/
@[expose, specialize] public def writeShr (a : A) (o len v : Nat) : A :=
  if 64 / LA.w ≤ 1 ∨ len = 0 then writeLimbs a o len v
  else
    writeShr (writeWord a o v.toUInt64 (min len (64 / LA.w))) (o + min len (64 / LA.w))
      (len - min len (64 / LA.w)) (v >>> (LA.w * min len (64 / LA.w)))
termination_by len
decreasing_by lia

omit R in
private theorem writeShr_spec (len : Nat) : ∀ (a : A) (o v : Nat),
    WritesOK a (writeShr a o len v) o len (v % 2 ^ (LA.w * len)) := by
  induction len using Nat.strongRecOn with
  | ind len ih =>
  intro a o v
  rw [writeShr]
  split
  · rw [writeLimbs_eq]
    exact ⟨size_writeNat .., fun i h => get_writeNat _ _ _ _ _ h,
      fun h => valAt_writeNat _ _ _ _ h⟩
  · rename_i hc
    generalize hc' : min len (64 / LA.w) = c
    have hc64 : LA.w * c ≤ 64 :=
      Nat.le_trans (Nat.mul_le_mul_left _ (by lia : c ≤ 64 / LA.w)) (Nat.mul_div_le ..)
    have h := (writeWord_spec o v.toUInt64 c a hc64).append
      (ih (len - c) (by lia) (writeWord a o v.toUInt64 c) (o + c) (v >>> (LA.w * c)))
    rw [show c + (len - c) = len by lia] at h
    refine ⟨h.1, h.2.1, fun hs => ?_⟩
    rw [h.2.2 hs, Nat.toUInt64_eq, UInt64.toNat_ofNat',
      Nat.mod_mod_of_dvd _ (Nat.pow_dvd_pow 2 hc64), Nat.shiftRight_eq_div_pow, ← Nat.mod_mul,
      ← Nat.pow_add, ← Nat.mul_add, show c + (len - c) = len by lia]

/--
Writes `v % 2^(w len)` into the `len` limbs of `a` from `o` on: the low half and the high half
above `2048` bits, which keeps the operations on `v` linear in all.
-/
@[expose, specialize] public def writeHalves (a : A) (o len v : Nat) : A :=
  if len ≤ 1 ∨ LA.w * len ≤ 2048 then writeShr a o len v
  else
    let hi := v >>> (LA.w * (len / 2))
    writeHalves (writeHalves a o (len / 2) (v - hi <<< (LA.w * (len / 2)))) (o + len / 2)
      (len - len / 2) hi
termination_by len
decreasing_by all_goals lia

omit R in
public theorem writeHalves_spec (len : Nat) : ∀ (a : A) (o v : Nat),
    LA.size (writeHalves a o len v) = LA.size a ∧
      (∀ i, i < o ∨ o + len ≤ i → LA.get (writeHalves a o len v) i = LA.get a i) ∧
      (o + len ≤ LA.size a → valAt (writeHalves a o len v) o len = v % 2 ^ (LA.w * len)) := by
  induction len using Nat.strongRecOn with
  | ind len ih =>
  intro a o v
  rw [writeHalves]
  split
  · exact writeShr_spec len a o v
  · rename_i hl
    have : 1 < len := by lia
    dsimp only
    generalize hh : len / 2 = h
    generalize hhi : v >>> (LA.w * h) = hi
    have hw := WritesOK.append (ih h (by lia) a o (v - hi <<< (LA.w * h)))
      (ih (len - h) (by lia) (writeHalves a o h (v - hi <<< (LA.w * h))) (o + h) hi)
    rw [show h + (len - h) = len by lia] at hw
    refine ⟨hw.1, hw.2.1, fun hs => ?_⟩
    have hlo : v - hi <<< (LA.w * h) = v % 2 ^ (LA.w * h) := by
      rw [← hhi, Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq, Nat.mod_def, Nat.mul_comm]
    rw [hw.2.2 hs, hlo, Nat.mod_mod, ← hhi, Nat.shiftRight_eq_div_pow, ← Nat.mod_mul,
      ← Nat.pow_add, ← Nat.mul_add, show h + (len - h) = len by lia]

/-- The `len` low limbs of `n`, in a fresh array. -/
@[expose, specialize] public def ofNatLen (n len : Nat) : A := writeHalves (R.zeros len) 0 len n

public theorem size_ofNatLen (n len : Nat) : LA.size (ofNatLen (R := R) n len) = len := by
  rw [ofNatLen, (writeHalves_spec len _ _ _).1, R.size_zeros]

public theorem valAt_ofNatLen (n len : Nat) :
    valAt (ofNatLen (R := R) n len) 0 len = n % 2 ^ (LA.w * len) :=
  (writeHalves_spec len _ _ _).2.2 (by rw [R.size_zeros]; lia)

/-- The limbs of `n`, as many as its bits need, and one for `0`. -/
@[expose, specialize] public def ofNatW (n : Nat) : A := ofNatLen (R := R) n (n.log2 / LA.w + 1)

public theorem size_ofNatW (n : Nat) : LA.size (ofNatW (R := R) n) = n.log2 / LA.w + 1 :=
  size_ofNatLen ..

public theorem valAt_ofNatW (n : Nat) :
    valAt (ofNatW (R := R) n) 0 (LA.size (ofNatW (R := R) n)) = n := by
  rw [size_ofNatW, ofNatW, valAt_ofNatLen, Nat.mod_eq_of_lt]
  rcases Nat.eq_zero_or_pos n with h | h
  · subst h; exact Nat.two_pow_pos _
  · exact Nat.lt_of_lt_of_le Nat.lt_log2_self (Nat.pow_le_pow_right (by decide)
      (by have := Nat.lt_mul_div_succ n.log2 LA.w_pos; lia))

/-- The limbs of `n ≠ 0` have a nonzero top limb. -/
public theorem top_ofNatW {n : Nat} (hn : n ≠ 0) :
    LA.val (LA.get (ofNatW (R := R) n) (LA.size (ofNatW (R := R) n) - 1)) ≠ 0 := by
  have hv := valAt_ofNatW (R := R) n
  generalize hs : LA.size (ofNatW (R := R) n) = s at hv ⊢
  have hs' : s = n.log2 / LA.w + 1 := by rw [← hs, size_ofNatW]
  rw [val_get_eq _ (show s - 1 < s by lia), hv]
  have hlo : 2 ^ (LA.w * (s - 1)) ≤ n :=
    Nat.le_trans (Nat.pow_le_pow_right (by decide)
      (by rw [hs', Nat.add_sub_cancel]; exact Nat.mul_div_le ..)) (Nat.log2_self_le hn)
  have hhi : n < 2 ^ (LA.w * (s - 1)) * 2 ^ LA.w := by
    rw [← Nat.pow_add]
    exact Nat.lt_of_lt_of_le Nat.lt_log2_self (Nat.pow_le_pow_right (by decide)
      (by have := Nat.lt_mul_div_succ n.log2 LA.w_pos; rw [hs']; lia))
  rw [Nat.mod_eq_of_lt (Nat.div_lt_of_lt_mul hhi)]
  exact Nat.ne_of_gt (Nat.div_pos hlo (Nat.two_pow_pos _))

/-! ## Comparison -/

/-- Limb `i` of the window of `al` limbs of `a` from `ao` on, and `0` past its end. -/
@[inline] public def limbWin (a : A) (ao al i : Nat) : L :=
  if i < al then LA.get a (ao + i) else R.zero

public theorem val_limbWin (a : A) (ao al i : Nat) :
    LA.val (limbWin a ao al i) = if i < al then LA.val (LA.get a (ao + i)) else 0 := by
  unfold limbWin
  split
  · rfl
  · exact R.val_zero

/-- Whether limbs `0` to `i - 1` of the window of `a` are below those of `b`, from the top down. -/
@[expose, specialize] public def ltLoopW (a : A) (ao al : Nat) (b : A) (bo bl : Nat) : Nat → Bool
  | 0 => false
  | i + 1 =>
    let x := limbWin a ao al i
    let y := limbWin b bo bl i
    if R.eqB x y then ltLoopW a ao al b bo bl i else R.ltB x y

/-- The low `i` limbs of a window, zero past its end. -/
private theorem valAt_min_succ (a : A) (ao al i : Nat) :
    valAt a ao (min al (i + 1)) =
      valAt a ao (min al i) + 2 ^ (LA.w * i) * LA.val (limbWin a ao al i) := by
  rw [val_limbWin]
  split
  · rename_i h
    rw [show min al (i + 1) = i + 1 by lia, show min al i = i by lia, valAt_add, valAt_one]
  · rw [show min al (i + 1) = al by lia, show min al i = al by lia, Nat.mul_zero, Nat.add_zero]

private theorem ltLoopW_iff (a : A) (ao al : Nat) (b : A) (bo bl : Nat) (i : Nat) :
    ltLoopW a ao al b bo bl i = true ↔ valAt a ao (min al i) < valAt b bo (min bl i) := by
  induction i with
  | zero => simp [ltLoopW]
  | succ i ih =>
    rw [valAt_min_succ, valAt_min_succ, ltLoopW]
    have hla := valAt_lt a ao (min al i)
    have hlb := valAt_lt b bo (min bl i)
    have ha : 2 ^ (LA.w * min al i) ≤ 2 ^ (LA.w * i) :=
      Nat.pow_le_pow_right (by decide) (Nat.mul_le_mul_left _ (Nat.min_le_right _ _))
    have hb : 2 ^ (LA.w * min bl i) ≤ 2 ^ (LA.w * i) :=
      Nat.pow_le_pow_right (by decide) (Nat.mul_le_mul_left _ (Nat.min_le_right _ _))
    generalize valAt a ao (min al i) = X at *
    generalize valAt b bo (min bl i) = Y at *
    generalize 2 ^ (LA.w * i) = P at *
    generalize limbWin a ao al i = x
    generalize limbWin b bo bl i = y
    split
    · rename_i he
      rw [R.eqB_iff] at he
      rw [ih, he]
      lia
    · rename_i he
      rw [R.eqB_iff] at he
      rw [R.ltB_iff]
      rcases Nat.lt_or_gt_of_ne he with h | h
      · have := Nat.mul_le_mul_left P (show LA.val x + 1 ≤ LA.val y from h)
        rw [Nat.mul_add, Nat.mul_one] at this
        constructor <;> intro <;> lia
      · have := Nat.mul_le_mul_left P (show LA.val y + 1 ≤ LA.val x from h)
        rw [Nat.mul_add, Nat.mul_one] at this
        constructor <;> intro <;> lia

/-- Whether the window of `al` limbs of `a` from `ao` on is below that of `b`. -/
@[expose, specialize] public def ltWin (a : A) (ao al : Nat) (b : A) (bo bl : Nat) : Bool :=
  ltLoopW a ao al b bo bl (max al bl)

public theorem ltWin_iff (a : A) (ao al : Nat) (b : A) (bo bl : Nat) :
    ltWin a ao al b bo bl = true ↔ valAt a ao al < valAt b bo bl := by
  rw [ltWin, ltLoopW_iff, show min al (max al bl) = al by lia, show min bl (max al bl) = bl by lia]

/-- Limb `i` of a window on machine indices: limb `ao + i` when `i < al`, and `0` past it. -/
@[inline] public def limbWinU (a : A) (ao al i : USize) : L :=
  if i < al then LinComb.limbU a (ao + i) else R.zero

/-- `ltLoopW` on machine indices, from limb `j - 1` down. -/
@[expose, specialize] public def ltWinW (a : A) (ao al : USize) (b : A) (bo bl : USize)
    (j : USize) : Bool :=
  if hj : j = 0 then false
  else
    let x := limbWinU a ao al (j - 1)
    let y := limbWinU b bo bl (j - 1)
    if R.eqB x y then ltWinW a ao al b bo bl (j - 1) else R.ltB x y
termination_by j.toNat
decreasing_by
  have := toNat_pred' (pos_of_ne hj)
  have : j.toNat ≠ 0 := fun e => hj (USize.toNat_inj.1 (by rw [e]; rfl))
  lia

private theorem val_limbWinU (a : A) (ao al i : USize) (hs : LA.size a < USize.size)
    (ha : ao.toNat + al.toNat < USize.size) :
    LA.val (limbWinU a ao al i) = LA.val (limbWin a ao.toNat al.toNat i.toNat) := by
  unfold limbWinU limbWin
  by_cases h : i < al
  · have h' : i.toNat < al.toNat := USize.lt_iff_toNat_lt.1 h
    simp only [h, h', ↓reduceIte]
    rw [LinComb.val_limbU R.val_get_ge _ _ hs, USize.toNat_add, Nat.mod_eq_of_lt (by lia)]
  · have h' : ¬i.toNat < al.toNat := fun h' => h (USize.lt_iff_toNat_lt.2 h')
    simp only [h, h', ↓reduceIte]

private theorem ltWinW_eq (a : A) (ao al : USize) (b : A) (bo bl : USize)
    (hsa : LA.size a < USize.size) (hsb : LA.size b < USize.size)
    (ha : ao.toNat + al.toNat < USize.size) (hb : bo.toNat + bl.toNat < USize.size) (j : USize) :
    ltWinW a ao al b bo bl j = ltLoopW a ao.toNat al.toNat b bo.toNat bl.toNat j.toNat := by
  have hx := fun i => val_limbWinU a ao al i hsa ha
  have hy := fun i => val_limbWinU b bo bl i hsb hb
  induction j using ltWinW.induct (R := R) a ao al b bo bl with
  | case1 =>
    rw [ltWinW]
    simp [ltLoopW]
  | case2 j hj x y he ih =>
    rw [ltWinW, dite_eq_right hj]
    simp only [x, y] at he ⊢
    rw [ite_eq_left he, ih]
    have hp := toNat_pred' (pos_of_ne hj)
    have : j.toNat ≠ 0 := fun e => hj (USize.toNat_inj.1 (by rw [e]; rfl))
    obtain ⟨m, hm⟩ : ∃ m, j.toNat = m + 1 := ⟨j.toNat - 1, by lia⟩
    rw [hm, Nat.add_sub_cancel] at hp
    rw [R.eqB_iff, hx, hy, hp] at he
    rw [hp, hm, ltLoopW]
    simp only [(R.eqB_iff _ _).2 he, ↓reduceIte]
  | case3 j hj x y he =>
    rw [ltWinW, dite_eq_right hj]
    simp only [x, y] at he ⊢
    rw [ite_eq_right he]
    have hp := toNat_pred' (pos_of_ne hj)
    have : j.toNat ≠ 0 := fun e => hj (USize.toNat_inj.1 (by rw [e]; rfl))
    obtain ⟨m, hm⟩ : ∃ m, j.toNat = m + 1 := ⟨j.toNat - 1, by lia⟩
    rw [hm, Nat.add_sub_cancel] at hp
    rw [R.eqB_iff, hx, hy, hp] at he
    rw [hm, ltLoopW]
    have he' : R.eqB (limbWin a ao.toNat al.toNat m) (limbWin b bo.toNat bl.toNat m) = false := by
      rw [← Bool.not_eq_true, R.eqB_iff]; exact he
    simp only [he', Bool.false_eq_true, ↓reduceIte]
    apply Bool.eq_iff_iff.2
    rw [R.ltB_iff, R.ltB_iff, hx, hy, hp]

/-- `ltWin` on machine indices below `2³¹` limbs, which the compiler uses in its place. -/
@[expose, specialize] public def ltWinFast (a : A) (ao al : Nat) (b : A) (bo bl : Nat) : Bool :=
  if LA.size a < 2147483648 ∧ LA.size b < 2147483648 ∧ ao + al < 2147483648 ∧
      bo + bl < 2147483648 then
    ltWinW a ao.toUSize al.toUSize b bo.toUSize bl.toUSize (max al bl).toUSize
  else ltWin a ao al b bo bl

@[csimp] public theorem ltWin_eq_ltWinFast : @ltWin = @ltWinFast := by
  funext A L LA R a ao al b bo bl
  rw [ltWinFast]
  split
  · rename_i h
    have hU : 2147483648 < USize.size := by
      rcases USize.size_eq with e | e <;> rw [e] <;> decide
    have t : ∀ n, n < 2147483648 → n.toUSize.toNat = n := fun n hn => by
      rw [USize.toNat_ofNat', Nat.mod_eq_of_lt (by lia)]
    rw [ltWinW_eq a _ _ b _ _ (by lia) (by lia) (by rw [t _ (by lia), t _ (by lia)]; lia)
      (by rw [t _ (by lia), t _ (by lia)]; lia), t ao (by lia), t al (by lia), t bo (by lia),
      t bl (by lia), t _ (by lia), ltWin]
  · rfl

/-- Whether `a < b` on arrays. -/
@[expose, specialize] public def ltA (a b : A) : Bool := ltWin a 0 (LA.size a) b 0 (LA.size b)

public theorem ltA_iff (a b : A) :
    ltA a b = true ↔ valAt a 0 (LA.size a) < valAt b 0 (LA.size b) :=
  ltWin_iff ..

/-- The value of an array on more limbs than it has. -/
public theorem valAt_of_size_le (a : A) {m : Nat} (h : LA.size a ≤ m) :
    valAt a 0 m = valAt a 0 (LA.size a) := by
  rw [show m = LA.size a + (m - LA.size a) by lia, valAt_add,
    valAt_eq_zero (a := a) (lo := 0 + LA.size a) (m - LA.size a)
      (fun i h₁ _ => R.val_get_ge a i (by lia)), Nat.mul_zero, Nat.add_zero]

/-- `ltA` by `ltW` on machine indices below `2³¹` limbs, which the compiler uses in its place. -/
@[expose, specialize] public def ltAFast (a b : A) : Bool :=
  if max (LA.size a) (LA.size b) < 2147483648 then ltW a b (max (LA.size a) (LA.size b)).toUSize
  else ltA a b

@[csimp] public theorem ltA_eq_ltAFast : @ltA = @ltAFast := by
  funext A L LA R a b
  rw [ltAFast]
  split
  · rename_i h
    have hU : 2147483648 < USize.size := by
      rcases USize.size_eq with e | e <;> rw [e] <;> decide
    have e : (max (LA.size a) (LA.size b)).toUSize.toNat = max (LA.size a) (LA.size b) := by
      rw [USize.toNat_ofNat', Nat.mod_eq_of_lt (by lia)]
    apply Bool.eq_iff_iff.2
    rw [ltA_iff, ltW_iff R.val_get_ge a b _ (by lia) (by lia), e,
      valAt_of_size_le a (m := max (LA.size a) (LA.size b)) (by lia),
      valAt_of_size_le b (m := max (LA.size a) (LA.size b)) (by lia)]
  · rfl

/-! ## Bitwise operations on arrays -/

section Bits

variable [F : WordFolds A L]

omit R F in
/-- The limbs of an array that `USize` indices reach, as a loop bound. -/
public theorem full_bound (a : A) (h : LA.size a < USize.size) :
    LoopBound a 0 (LA.size a).toUSize := by
  have e : (LA.size a).toUSize.toNat = LA.size a := by
    rw [Nat.toUSize_eq, USize.toNat_ofNat_of_lt' h]
  exact ⟨by rw [e]; simp, by rw [e]; simp; exact h⟩

omit F in
/-- New zero limbs, `n` of them, as a loop bound. -/
public theorem zeros_bound' {n : Nat} (h : n < USize.size) : LoopBound (R.zeros n) 0 n.toUSize := by
  have e : n.toUSize.toNat = n := by rw [Nat.toUSize_eq, USize.toNat_ofNat_of_lt' h]
  exact ⟨by rw [R.size_zeros, e]; simp, by rw [e]; simp; exact h⟩

/--
Limb-wise `f` of `a` and `b`, zero past their ends, trimmed to `k` limbs, for an `f` whose value is
the bitwise `op`, by `bitW` into at least `k` new limbs; from the values were the sizes not
`USize`s, which never happens.
-/
@[inline, expose] public def bitA (k : Nat) (f : L → L → L) (op : Nat → Nat → Nat) (a b : A) : A :=
  let n := max (max (LA.size a) (LA.size b)) k
  if h : fitsU n then trimTo k (bitW f a b (R.zeros n) n.toUSize (zeros_bound' (lt_of_fitsU h)))
  else trimTo k (ofNatW (R := R) (op (valAt a 0 (LA.size a)) (valAt b 0 (LA.size b))))

public theorem isTrimmedTo_bitA (k : Nat) (f : L → L → L) (op : Nat → Nat → Nat) (a b : A) :
    isTrimmedTo k (bitA k f op a b) = true := by
  unfold bitA; dsimp only; split <;> exact isTrimmedTo_trimTo ..

public theorem valAt_bitA (k : Nat) (f : L → L → L) (op : Nat → Nat → Nat)
    (hw : ∀ (a b r : A) (n : USize) (hr : LoopBound r 0 n),
      LA.size a < USize.size → LA.size b < USize.size →
      valAt (bitW f a b r n hr) 0 n.toNat = op (valAt a 0 n.toNat) (valAt b 0 n.toNat))
    (a b : A) :
    valAt (bitA k f op a b) 0 (LA.size (bitA k f op a b)) =
      op (valAt a 0 (LA.size a)) (valAt b 0 (LA.size b)) := by
  unfold bitA
  dsimp only
  split
  · rename_i h
    replace h := lt_of_fitsU h
    have e : (max (max (LA.size a) (LA.size b)) k).toUSize.toNat =
        max (max (LA.size a) (LA.size b)) k := by
      rw [Nat.toUSize_eq, USize.toNat_ofNat_of_lt' h]
    rw [valAt_trimTo, size_bitW, R.size_zeros]
    have h' := hw a b _ _ (zeros_bound' h) (by lia) (by lia)
    rw [e] at h'
    rw [h', valAt_of_size_le a (by lia), valAt_of_size_le b (by lia)]
  · rw [valAt_trimTo, valAt_ofNatW]

/-- `bitA k` keeps at least `min k 1` limbs. -/
public theorem size_bitA_ge (k : Nat) (f : L → L → L) (op : Nat → Nat → Nat) (a b : A) :
    min k 1 ≤ LA.size (bitA k f op a b) := by
  unfold bitA
  dsimp only
  split
  · rename_i h
    replace h := lt_of_fitsU h
    have := (trimTo_spec k (bitW f a b (R.zeros (max (max (LA.size a) (LA.size b)) k))
      (max (max (LA.size a) (LA.size b)) k).toUSize (zeros_bound' h))).2.2.1
    rw [size_bitW, R.size_zeros] at this
    lia
  · have := (trimTo_spec k (ofNatW (R := R) (op (valAt a 0 (LA.size a))
      (valAt b 0 (LA.size b))))).2.2.1
    rw [size_ofNatW] at this
    lia

/-- `a &&& b`, trimmed to `k` limbs. -/
@[inline, expose] public def landA (k : Nat) (a b : A) : A := bitA k R.land (· &&& ·) a b

/-- `a ||| b`, trimmed to `k` limbs. -/
@[inline, expose] public def lorA (k : Nat) (a b : A) : A := bitA k R.lor (· ||| ·) a b

/-- `a ^^^ b`, trimmed to `k` limbs. -/
@[inline, expose] public def xorA (k : Nat) (a b : A) : A := bitA k R.xor (· ^^^ ·) a b

public theorem valAt_landA (k : Nat) (a b : A) :
    valAt (landA k a b) 0 (LA.size (landA k a b)) =
      valAt a 0 (LA.size a) &&& valAt b 0 (LA.size b) :=
  valAt_bitA k _ _ (fun a b r n hr ha hb => valAt_bitW_land R.val_get_ge a b r n hr ha hb) a b

public theorem valAt_lorA (k : Nat) (a b : A) :
    valAt (lorA k a b) 0 (LA.size (lorA k a b)) =
      valAt a 0 (LA.size a) ||| valAt b 0 (LA.size b) :=
  valAt_bitA k _ _ (fun a b r n hr ha hb => valAt_bitW_lor R.val_get_ge a b r n hr ha hb) a b

public theorem valAt_xorA (k : Nat) (a b : A) :
    valAt (xorA k a b) 0 (LA.size (xorA k a b)) =
      valAt a 0 (LA.size a) ^^^ valAt b 0 (LA.size b) :=
  valAt_bitA k _ _ (fun a b r n hr ha hb => valAt_bitW_xor R.val_get_ge a b r n hr ha hb) a b

/-! ## Shifts by any number of bits

`shlBits a ao m n` is `a 2ⁿ` for the `m` limbs of `a` from `ao`, in `n / w + m + 1` new limbs, and
`shrBits a ao m n` is `⌊a / 2ⁿ⌋` in `m - n / w` new limbs, both untrimmed: whole limbs move by the
offsets of `lshiftW` and `rshiftW` (or `copyW` and `extract` when `w` divides `n`), which read `a`
where it is.
-/

omit R F in
public theorem toNat_toUSize_of_lt {n : Nat} (h : n < USize.size) : n.toUSize.toNat = n := by
  rw [Nat.toUSize_eq, USize.toNat_ofNat_of_lt' h]

omit R F in
/-- `n` limbs of `a` from `o`, within it, as a loop bound. -/
public theorem win_bound (a : A) {o n : Nat} (h : o + n ≤ LA.size a) (hU : o + n < USize.size) :
    LoopBound a o.toUSize n.toUSize := by
  rw [LoopBound, toNat_toUSize_of_lt (show o < USize.size by lia),
    toNat_toUSize_of_lt (show n < USize.size by lia)]
  exact ⟨h, hU⟩

omit F in
/-- `s < w` as a limb. -/
public theorem val_ofUSize_lt {s : Nat} (hs : s < LA.w) : LA.val (R.ofUSize s.toUSize) = s := by
  have hwU : LA.w < USize.size := by rw [← R.toNat_wU]; exact R.wU.toNat_lt_size
  have hwB : LA.w < 2 ^ LA.w := Nat.lt_two_pow_self
  rw [R.val_ofUSize, toNat_toUSize_of_lt (by lia), Nat.mod_eq_of_lt (by lia)]

omit F in
/-- `extract` copies the `k` limbs of `w` from `i`. -/
public theorem extract_spec (w : A) (i k : Nat) (h : i + k ≤ LA.size w) :
    LA.size (R.extract w i (i + k)) = k ∧
      valAt (R.extract w i (i + k)) 0 k = valAt w i k := by
  have hs : LA.size (R.extract w i (i + k)) = k := by rw [R.size_extract]; lia
  refine ⟨hs, ?_⟩
  have key : ∀ c j, j + c ≤ k → valAt (R.extract w i (i + k)) j c = valAt w (i + j) c := by
    intro c
    induction c with
    | zero => intro j _; simp
    | succ c ih =>
      intro j hj
      rw [valAt_succ, valAt_succ, R.get_extract _ _ _ _ (by rw [hs]; lia), ih (j + 1) (by lia),
        Nat.add_assoc]
  have := key k 0 (by lia)
  rwa [Nat.add_zero] at this

/-- `a 2ⁿ` for the `m` limbs of `a` from `ao`, untrimmed, in `n / w + m + 1` new limbs. -/
@[inline, expose] public def shlBits (a : A) (ao m n : Nat) : A :=
  let q := n / LA.w
  if h : ao + m ≤ LA.size a ∧ fitsU (ao + m) ∧ fitsU (q + m + 1) then
    have h₁ := lt_of_fitsU h.2.1
    have h₂ := lt_of_fitsU h.2.2
    have hr : LoopBound (R.zeros (q + m + 1)) q.toUSize m.toUSize :=
      win_bound _ (by rw [R.size_zeros]; lia) (by lia)
    if n % LA.w = 0 then copyW (R.zeros (q + m + 1)) q.toUSize a ao.toUSize m.toUSize hr
      (win_bound a h.1 h₁)
    else
      let p := lshiftW (R.zeros (q + m + 1)) q.toUSize a ao.toUSize m.toUSize
        (R.ofUSize (n % LA.w).toUSize) hr (win_bound a h.1 h₁)
      R.uset p.1 (q + m).toUSize p.2
        (by rw [size_lshiftW, R.size_zeros, toNat_toUSize_of_lt (by lia)]; lia)
  else ofNatLen (R := R) (valAt a ao m * 2 ^ n) (q + m + 1)

/-- `⌊a / 2ⁿ⌋` for the `m` limbs of `a` from `ao`, untrimmed, in `m - n / w` new limbs. -/
@[inline, expose] public def shrBits (a : A) (ao m n : Nat) : A :=
  let q := n / LA.w
  if hq : q < m then
    if h : ao + m ≤ LA.size a ∧ fitsU (ao + m) then
      have h₁ := lt_of_fitsU h.2
      if n % LA.w = 0 then R.extract a (ao + q) (ao + m)
      else
        (rshiftW (R.zeros (m - q)) 0 a (ao + q).toUSize (m - q).toUSize
          (R.ofUSize (n % LA.w).toUSize)
          (zeros_bound' (by lia))
          (win_bound a (by lia) (by lia))
          (USize.lt_iff_toNat_lt.2 (by rw [toNat_toUSize_of_lt (by lia)]; simp; lia))).1
    else ofNatLen (R := R) (valAt a ao m / 2 ^ n) (m - q)
  else R.zeros 0

public theorem size_shlBits (a : A) (ao m n : Nat) :
    LA.size (shlBits a ao m n) = n / LA.w + m + 1 := by
  unfold shlBits
  dsimp only
  split
  · split
    · rw [size_copyW, R.size_zeros]
    · rw [R.size_uset, size_lshiftW, R.size_zeros]
  · exact size_ofNatLen ..

omit R F in
/-- The value of `q + m + 1` limbs, by the limbs below `q`, the `m` from `q`, and the top one. -/
private theorem valAt_split (x : A) (q m : Nat) :
    valAt x 0 (q + m + 1) =
      valAt x 0 q + 2 ^ (LA.w * q) * valAt x q m +
        2 ^ (LA.w * q) * 2 ^ (LA.w * m) * LA.val (LA.get x (q + m)) := by
  rw [valAt_add, valAt_add x 0 q m, Nat.zero_add, valAt_one, Nat.zero_add, Nat.mul_add,
    Nat.pow_add]

public theorem valAt_shlBits (a : A) (ao m n : Nat) :
    valAt (shlBits a ao m n) 0 (n / LA.w + m + 1) = valAt a ao m * 2 ^ n := by
  have hw := LA.w_pos
  have hn : 2 ^ n = 2 ^ (LA.w * (n / LA.w)) * 2 ^ (n % LA.w) := by
    rw [← Nat.pow_add]; congr 1; exact (Nat.div_add_mod n LA.w).symm
  unfold shlBits
  dsimp only
  split
  · rename_i h
    have h₁ := lt_of_fitsU h.2.1
    have h₂ := lt_of_fitsU h.2.2
    replace h : ao + m ≤ LA.size a ∧ ao + m < USize.size ∧ n / LA.w + m + 1 < USize.size :=
      ⟨h.1, h₁, h₂⟩
    have hq := toNat_toUSize_of_lt (show n / LA.w < USize.size by lia)
    have hm := toNat_toUSize_of_lt (show m < USize.size by lia)
    have ho := toNat_toUSize_of_lt (show ao < USize.size by lia)
    split
    · rename_i hs
      obtain ⟨c₁, c₂, c₃⟩ := copyW_spec (R.zeros (n / LA.w + m + 1)) (n / LA.w).toUSize a
        ao.toUSize m.toUSize (win_bound _ (by rw [R.size_zeros]; lia) (by lia))
        (win_bound a h.1 h.2.1)
      simp only [hq, hm, ho] at c₂ c₃
      rw [valAt_split, c₃, valAt_eq_zero (n / LA.w) fun i _ hi => by
          rw [c₂ i (.inl (by lia)), R.val_get_zeros],
        c₂ _ (.inr (by lia)), R.val_get_zeros, hn, hs, Nat.pow_zero, Nat.mul_one]
      lia
    · rename_i hs
      have hsv := val_ofUSize_lt (R := R) (Nat.mod_lt n hw)
      obtain ⟨p₁, p₂, p₃⟩ := lshiftW_spec (R.zeros (n / LA.w + m + 1)) (n / LA.w).toUSize a
        ao.toUSize m.toUSize (R.ofUSize (n % LA.w).toUSize)
        (win_bound _ (by rw [R.size_zeros]; lia) (by lia)) (win_bound a h.1 h.2.1)
        (by rw [hsv]; lia) (by rw [hsv]; exact Nat.mod_lt n hw)
      simp only [hq, hm, ho, hsv] at p₃
      simp only [hq, hm] at p₂
      rw [valAt_split, R.get_uset, toNat_toUSize_of_lt (by lia)]
      simp only [↓reduceIte]
      rw [valAt_uset_of _ _ _ _ _ _ (.inr (by rw [toNat_toUSize_of_lt (by lia)]; lia)),
        valAt_uset_of _ _ _ _ _ _ (.inr (by rw [toNat_toUSize_of_lt (by lia)]; lia)),
        valAt_eq_zero (n / LA.w) fun i _ hi => by rw [p₂ i (.inl (by lia)), R.val_get_zeros], hn,
        Nat.zero_add, Nat.mul_assoc (2 ^ _) (2 ^ _), ← Nat.mul_add, p₃, Nat.mul_left_comm]
  · rw [valAt_ofNatLen, Nat.mod_eq_of_lt]
    have hA := valAt_lt a ao m
    have : 2 ^ n < 2 ^ (LA.w * (n / LA.w + 1)) :=
      Nat.pow_lt_pow_right (by decide) (by have := Nat.lt_div_mul_add (a := n) hw; lia)
    calc valAt a ao m * 2 ^ n < 2 ^ (LA.w * m) * 2 ^ (LA.w * (n / LA.w + 1)) :=
          Nat.mul_lt_mul'' hA this
      _ = 2 ^ (LA.w * (n / LA.w + m + 1)) := by rw [← Nat.pow_add]; congr 1; lia

public theorem size_shrBits (a : A) (ao m n : Nat) :
    LA.size (shrBits a ao m n) = m - n / LA.w := by
  unfold shrBits
  dsimp only
  split
  · split
    · rename_i hq h
      split
      · rw [R.size_extract]; lia
      · rw [size_rshiftW, R.size_zeros]
    · exact size_ofNatLen ..
  · rw [R.size_zeros]; lia

public theorem valAt_shrBits (a : A) (ao m n : Nat) :
    valAt (shrBits a ao m n) 0 (m - n / LA.w) = valAt a ao m / 2 ^ n := by
  have hw := LA.w_pos
  have hn : 2 ^ n = 2 ^ (LA.w * (n / LA.w)) * 2 ^ (n % LA.w) := by
    rw [← Nat.pow_add]; congr 1; exact (Nat.div_add_mod n LA.w).symm
  unfold shrBits
  dsimp only
  split
  · rename_i hq
    -- The limbs from `q` on are `⌊a / βq⌋`.
    have hsplit : valAt a ao m / 2 ^ (LA.w * (n / LA.w)) =
        valAt a (ao + n / LA.w) (m - n / LA.w) := by
      have e := valAt_add a ao (n / LA.w) (m - n / LA.w)
      rw [show n / LA.w + (m - n / LA.w) = m by lia] at e
      rw [e, Nat.add_mul_div_left _ _ (Nat.two_pow_pos _),
        Nat.div_eq_of_lt (valAt_lt a ao _), Nat.zero_add]
    rw [hn, ← Nat.div_div_eq_div_mul, hsplit]
    split
    · rename_i h
      replace h : ao + m ≤ LA.size a ∧ ao + m < USize.size := ⟨h.1, lt_of_fitsU h.2⟩
      split
      · rename_i hs
        rw [hs, Nat.pow_zero, Nat.div_one]
        have := (extract_spec a (ao + n / LA.w) (m - n / LA.w) (by lia)).2
        rwa [show ao + n / LA.w + (m - n / LA.w) = ao + m by lia] at this
      · rename_i hs
        have hsv := val_ofUSize_lt (R := R) (Nat.mod_lt n hw)
        obtain ⟨-, -, r₃, r₄⟩ := rshiftW_spec (R.zeros (m - n / LA.w)) 0 a
          (ao + n / LA.w).toUSize (m - n / LA.w).toUSize (R.ofUSize (n % LA.w).toUSize) _ _ _
          (by rw [hsv]; lia) (by rw [hsv]; exact Nat.mod_lt n hw)
        rw [hsv, toNat_toUSize_of_lt (by lia), toNat_toUSize_of_lt (by lia)] at r₃
        rw [hsv] at r₄
        simp only [USize.toNat_zero] at r₃
        rw [← r₃, Nat.mul_add_div (Nat.two_pow_pos _), Nat.div_eq_of_lt r₄, Nat.add_zero]
    · rw [valAt_ofNatLen, Nat.mod_eq_of_lt]
      exact Nat.lt_of_le_of_lt (Nat.div_le_self _ _) (valAt_lt ..)
  · rename_i hq
    rw [show m - n / LA.w = 0 by lia, valAt_zero, Nat.div_eq_of_lt]
    calc valAt a ao m < 2 ^ (LA.w * m) := valAt_lt ..
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by decide) (by
          have := Nat.div_mul_le_self n LA.w; rw [Nat.mul_comm] at this
          exact Nat.le_trans (Nat.mul_le_mul_left _ (by lia : m ≤ n / LA.w)) this)

/-! ## Base-two logarithm of arrays -/

omit F in
/-- `⌊log₂ a⌋` of an array, by `log2W` from the top limb; from the value were the size not a
`USize`, which never happens. -/
@[inline, expose] public def log2A (a : A) : Nat :=
  if h : fitsU (LA.size a) then log2W a 0 (LA.size a).toUSize (full_bound a (lt_of_fitsU h))
  else (valAt a 0 (LA.size a)).log2

omit F in
public theorem log2A_eq (a : A) : log2A a = (valAt a 0 (LA.size a)).log2 := by
  unfold log2A
  split
  · rename_i h
    replace h := lt_of_fitsU h
    rw [log2W_eq, USize.toNat_zero, toNat_toUSize_of_lt h]
  · rfl

end Bits

end WordArray

end MPN
