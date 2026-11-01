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

end WordArray

end MPN
