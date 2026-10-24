/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import MPN.Generic.Ops

/-!
# Decimal strings by divide and conquer, at any base

`NatOps.toDec` writes the decimal digits of a number in `O(M(n) log n)` operations with a
subquadratic division, after GMP's `mpn_get_str`: with the powers `p_j = 10^(2ʲ)`, it divides by
the largest `p_j ≤ x`, writes the quotient, and then the remainder with exactly `2ʲ` digits,
splitting it by `p_{j-1}` in the same way (`padDec`). Numbers of at most `T` limbs go to the
instance's own conversion, which only has to be correct (`base`), and are padded with zeros.
The specification is `Nat.toDigits 10`, the digits of `Nat.repr`.
-/

namespace MPN

/-! ## Digits -/

/-- The `k` low decimal digits of `d`, with leading zeros. -/
@[expose] public def padDigits : Nat → Nat → List Char
  | 0, _ => []
  | k + 1, d => padDigits k (d / 10) ++ [Nat.digitChar (d % 10)]

/-- The digits of `10ᵏ n + d` are those of `n` followed by the `k` digits of `d`. -/
public theorem toDigits_pow_mul_add (k : Nat) {n d : Nat} (hn : 0 < n) (hd : d < 10 ^ k) :
    Nat.toDigits 10 (10 ^ k * n + d) = Nat.toDigits 10 n ++ padDigits k d := by
  induction k generalizing d with
  | zero =>
    rw [Nat.pow_zero] at hd
    rw [show d = 0 by lia, padDigits, Nat.pow_zero, Nat.one_mul, Nat.add_zero, List.append_nil]
  | succ k ih =>
    have hpos : 0 < 10 ^ k * n := Nat.mul_pos (Nat.pow_pos (by decide)) hn
    have e : 10 ^ (k + 1) * n + d = 10 * (10 ^ k * n + d / 10) + d % 10 := by
      rw [Nat.pow_succ, Nat.mul_comm (10 ^ k) 10, Nat.mul_assoc]; lia
    rw [e, ← Nat.toDigits_append_toDigits (by decide) (by lia) (Nat.mod_lt _ (by decide)),
      Nat.toDigits_of_lt_base (Nat.mod_lt _ (by decide)),
      ih (by rw [Nat.pow_succ] at hd; lia), padDigits, List.append_assoc]

/-- The `m₁ + m₂` digits of `q 10^m₂ + r` are the `m₁` digits of `q`, then the `m₂` of `r`. -/
public theorem padDigits_add (m₁ m₂ q r : Nat) (hr : r < 10 ^ m₂) :
    padDigits (m₁ + m₂) (q * 10 ^ m₂ + r) = padDigits m₁ q ++ padDigits m₂ r := by
  induction m₂ generalizing r q with
  | zero =>
    rw [Nat.pow_zero] at hr
    rw [show r = 0 by lia, Nat.add_zero, Nat.pow_zero, Nat.mul_one, Nat.add_zero, padDigits,
      List.append_nil]
  | succ m ih =>
    have e₁ : (q * 10 ^ (m + 1) + r) / 10 = q * 10 ^ m + r / 10 := by
      rw [Nat.pow_succ, ← Nat.mul_assoc]; lia
    have e₂ : (q * 10 ^ (m + 1) + r) % 10 = r % 10 := by
      rw [Nat.pow_succ, ← Nat.mul_assoc, Nat.add_comm, Nat.add_mul_mod_self_right]
    rw [← Nat.add_assoc, padDigits, e₁, e₂, ih _ _ (by rw [Nat.pow_succ] at hr; lia), padDigits,
      List.append_assoc]

private theorem padDigits_zero (m : Nat) : padDigits m 0 = List.replicate m '0' := by
  induction m with
  | zero => rfl
  | succ m ih =>
    have h0 : Nat.digitChar 0 = '0' := by
      have h := Nat.toDigits_of_lt_base (b := 10) (n := 0) (by decide)
      rw [Nat.toDigits_zero] at h
      exact (List.singleton_inj.1 h).symm
    rw [padDigits, Nat.zero_div, ih, Nat.zero_mod, List.replicate_succ', h0]

/-- With enough room, the padded digits are the digits after the zeros. -/
public theorem padDigits_eq (m d : Nat) (hm : 1 ≤ m) (hd : d < 10 ^ m) :
    padDigits m d = List.replicate (m - (Nat.toDigits 10 d).length) '0' ++ Nat.toDigits 10 d := by
  induction m generalizing d with
  | zero => lia
  | succ m ih =>
    rw [padDigits]
    by_cases h10 : d < 10
    · rw [Nat.div_eq_of_lt h10, padDigits_zero, Nat.mod_eq_of_lt h10,
        Nat.toDigits_of_lt_base h10]
      simp
    · have hq : 0 < d / 10 := Nat.div_pos (by lia) (by decide)
      have hm' : 1 ≤ m := by
        rcases Nat.eq_zero_or_pos m with h | h
        · rw [h] at hd; lia
        · exact h
      have hd' : d / 10 < 10 ^ m := by rw [Nat.pow_succ] at hd; lia
      have e : Nat.toDigits 10 d = Nat.toDigits 10 (d / 10) ++ [Nat.digitChar (d % 10)] := by
        conv => lhs; rw [← Nat.div_add_mod d 10]
        rw [← Nat.toDigits_append_toDigits (by decide) hq (Nat.mod_lt _ (by decide)),
          Nat.toDigits_of_lt_base (Nat.mod_lt _ (by decide))]
      rw [ih _ hm' hd', e, List.length_append, List.length_singleton, List.append_assoc]
      congr 2
      lia

/-- `n` zeros pushed onto `s`. -/
def pushZeros (s : String) : Nat → String
  | 0 => s
  | n + 1 => (pushZeros s n).push '0'

theorem toList_pushZeros (s : String) (n : Nat) :
    (pushZeros s n).toList = s.toList ++ List.replicate n '0' := by
  induction n with
  | zero => simp [pushZeros]
  | succ n ih => rw [pushZeros, String.toList_push, ih, List.replicate_succ', List.append_assoc]

/-- `s` padded with zeros in front to `m` characters. -/
public def padZerosStr (m : Nat) (s : String) : String := pushZeros "" (m - s.length) ++ s

public theorem toList_padZerosStr (m : Nat) (s : String) :
    (padZerosStr m s).toList = List.replicate (m - s.toList.length) '0' ++ s.toList := by
  rw [padZerosStr, String.toList_append, toList_pushZeros, String.length_toList]
  simp

namespace NatOps

variable {α : Type} (o : NatOps α)

/-! ## Powers of ten -/

/-- `n`, as a sum of ones. -/
def ofSmall : Nat → α
  | 0 => o.sub o.one o.one
  | n + 1 => o.add (ofSmall n) o.one

theorem val_ofSmall (n : Nat) : o.val (o.ofSmall n) = n := by
  induction n with
  | zero => rw [ofSmall, o.val_sub _ _ (Nat.le_refl _), Nat.sub_self]
  | succ n ih => rw [ofSmall, o.val_add, ih, o.val_one]

/-- `ps` are the powers `10^(2ʲ)` for `j` from `ps.length - 1` down to `0`. -/
@[expose] public def IsPows : List α → Prop
  | [] => True
  | p :: ps => o.val p = 10 ^ 2 ^ ps.length ∧ IsPows ps

/-- The powers `10^(2ʲ)` above `ps`, squaring the top one while it is at most `x`. -/
def growPows (x : α) : List α → Nat → List α
  | [], _ => []
  | p :: ps, 0 => p :: ps
  | p :: ps, fuel + 1 => if o.le p x then growPows x (o.mul p p :: p :: ps) fuel else p :: ps

theorem isPows_growPows (x : α) : ∀ (fuel : Nat) (ps : List α), o.IsPows ps →
    o.IsPows (o.growPows x ps fuel) := by
  intro fuel
  induction fuel with
  | zero => intro ps h; cases ps <;> simp [growPows] at * <;> exact h
  | succ fuel ih =>
    intro ps h
    cases ps with
    | nil => simp [growPows, IsPows]
    | cons p ps =>
      simp only [growPows]
      split
      · apply ih
        refine ⟨?_, h⟩
        rw [o.val_mul, h.1, ← Nat.pow_add, List.length_cons, Nat.pow_succ, Nat.mul_two]
      · exact h

/-- The powers `10^(2ʲ)` up to the first above `x`, the largest first. -/
public def decPows (x : α) : List α := o.growPows x [o.ofSmall 10] 64

public theorem isPows_decPows (x : α) : o.IsPows (o.decPows x) :=
  o.isPows_growPows x 64 _ ⟨by rw [val_ofSmall]; rfl, trivial⟩

/-! ## The conversion -/

variable (base : α → String) (T : Nat)

/--
The `2ᵏ` decimal digits of `x < 10^(2ᵏ)`, with leading zeros, for the powers `ps` below
`10^(2ᵏ)`: the digits of the quotient and of the remainder by the top power, recursively, and
`base` below `T` limbs.
-/
public def padDec : List α → α → String
  | [], x => padZerosStr 1 (base x)
  | p :: ps, x =>
    if o.size x ≤ T then padZerosStr (2 ^ (ps.length + 1)) (base x)
    else
      let qr := o.divRem x p
      padDec ps qr.1 ++ padDec ps qr.2

/--
The decimal digits of `x`, for the powers `ps` with `x` below the square of the top one: the
first power `p ≤ x` gives the digits of `x / p`, then the `2ʲ` digits of `x % p`; `base` below
`T` limbs.
-/
public def topDec : List α → α → String
  | [], x => base x
  | p :: ps, x =>
    if o.size x ≤ T then base x
    else if o.le p x then
      let qr := o.divRem x p
      topDec ps qr.1 ++ padDec o base T ps qr.2
    else topDec ps x

/-- The decimal digits of `x`, like `Nat.repr`. -/
public def toDec (x : α) : String :=
  let ps := o.decPows x
  match ps with
  | [] => base x
  | p :: _ => if o.le p x then base x else o.topDec base T ps x

variable (hbase : ∀ x, (base x).toList = Nat.toDigits 10 (o.val x))

include hbase in
public theorem padDec_spec : ∀ (ps : List α) (x : α), o.IsPows ps →
    o.val x < 10 ^ 2 ^ ps.length →
    (o.padDec base T ps x).toList = padDigits (2 ^ ps.length) (o.val x) := by
  intro ps
  induction ps with
  | nil =>
    intro x _ hx
    rw [padDec, toList_padZerosStr, hbase, padDigits_eq _ _ (by simp) hx]
    try rfl
  | cons p ps ih =>
    intro x hps hx
    rw [List.length_cons] at hx ⊢
    rw [padDec]
    split
    · rw [toList_padZerosStr, hbase, padDigits_eq _ _ (Nat.one_le_two_pow (n := ps.length + 1)) hx]
      try rfl
    · dsimp only
      have hp : o.val p = 10 ^ 2 ^ ps.length := hps.1
      have hp0 : 0 < o.val p := by rw [hp]; exact Nat.pow_pos (by decide)
      obtain ⟨hq, hr⟩ := o.val_divRem x p (by lia)
      have hxl : o.val x < o.val p * o.val p := by
        rw [hp, ← Nat.pow_add, ← Nat.two_mul, ← Nat.pow_succ']; exact hx
      have e := padDigits_add (2 ^ ps.length) (2 ^ ps.length) (o.val x / o.val p)
        (o.val x % o.val p) (by rw [← hp]; exact Nat.mod_lt _ hp0)
      rw [← hp, Nat.div_add_mod'] at e
      rw [String.toList_append, ih _ hps.2 (by rw [hq, ← hp]; exact Nat.div_lt_of_lt_mul hxl),
        ih _ hps.2 (by rw [hr, ← hp]; exact Nat.mod_lt _ hp0), hq, hr, ← e, Nat.pow_succ,
        Nat.mul_two]

include hbase in
public theorem topDec_spec : ∀ (ps : List α) (x : α), o.IsPows ps →
    (∀ p ∈ ps.head?, o.val x < o.val p * o.val p) →
    (o.topDec base T ps x).toList = Nat.toDigits 10 (o.val x) := by
  intro ps
  induction ps with
  | nil => intro x _ _; rw [topDec, hbase]
  | cons p ps ih =>
    intro x hps hx
    have hxp := hx p rfl
    rw [topDec]
    split
    · rw [hbase]
    split
    · rename_i _ hle
      rw [o.le_iff] at hle
      dsimp only
      have hp : o.val p = 10 ^ 2 ^ ps.length := hps.1
      have hp0 : 0 < o.val p := by rw [hp]; exact Nat.pow_pos (by decide)
      obtain ⟨hq, hr⟩ := o.val_divRem x p (by lia)
      have hqp : o.val x / o.val p < o.val p := Nat.div_lt_of_lt_mul hxp
      have hq0 : 0 < o.val x / o.val p := Nat.div_pos hle hp0
      have hq' : ∀ p' ∈ ps.head?, o.val (o.divRem x p).1 < o.val p' * o.val p' := by
        intro p' hp'
        cases ps with
        | nil => simp at hp'
        | cons p'' ps' =>
          simp only [List.head?_cons, Option.mem_some_iff] at hp'
          subst hp'
          have : o.val p = o.val p'' * o.val p'' := by
            rw [hp, hps.2.1, ← Nat.pow_add, ← Nat.two_mul, ← Nat.pow_succ', List.length_cons]
          rw [hq, ← this]; exact hqp
      have hrp : o.val x % o.val p < 10 ^ 2 ^ ps.length := by rw [← hp]; exact Nat.mod_lt _ hp0
      have e := toDigits_pow_mul_add (2 ^ ps.length) hq0 hrp
      rw [← hp, Nat.mul_comm, Nat.div_add_mod'] at e
      rw [String.toList_append, ih _ hps.2 hq',
        o.padDec_spec base T hbase ps _ hps.2 (by rw [hr]; exact hrp), hq, hr, ← e]
    · rename_i _ hlt
      rw [o.le_iff] at hlt
      apply ih _ hps.2
      intro p' hp'
      cases ps with
      | nil => simp at hp'
      | cons p'' ps' =>
        simp only [List.head?_cons, Option.mem_some_iff] at hp'
        subst hp'
        have hp : o.val p = o.val p'' * o.val p'' := by
          rw [hps.1, hps.2.1, ← Nat.pow_add, ← Nat.two_mul, ← Nat.pow_succ']; rfl
        lia

include hbase in
public theorem toDec_spec (x : α) : (o.toDec base T x).toList = Nat.toDigits 10 (o.val x) := by
  unfold toDec
  dsimp only
  split
  · rw [hbase]
  · rename_i p ps' hps
    split
    · rw [hbase]
    · rename_i hlt
      rw [o.le_iff] at hlt
      apply o.topDec_spec base T hbase _ x (o.isPows_decPows x)
      intro p' hp'
      rw [hps] at hp'
      simp only [List.head?_cons, Option.mem_some_iff] at hp'
      subst hp'
      have := Nat.le_mul_self (o.val p)
      lia

/-! ## Reading digits -/

/-- The `len` characters of `arr` from `start`. -/
@[expose] public def chars (arr : Array Char) (start len : Nat) : List Char :=
  (arr.toList.drop start).take len

/-- The powers `10^(2ʲ)` for `j` from `k - 1` down to `0`. -/
public def powsN : Nat → List α
  | 0 => []
  | k + 1 =>
    match powsN k with
    | [] => [o.ofSmall 10]
    | p :: ps => o.mul p p :: p :: ps

public theorem isPows_powsN (k : Nat) : o.IsPows (o.powsN k) ∧ (o.powsN k).length = k := by
  induction k with
  | zero => exact ⟨trivial, rfl⟩
  | succ k ih =>
    obtain ⟨h₁, h₂⟩ := ih
    simp only [powsN]
    split
    · rename_i he
      rw [he] at h₂
      subst h₂
      exact ⟨⟨by rw [val_ofSmall]; rfl, trivial⟩, rfl⟩
    · rename_i p ps he
      rw [he] at h₁ h₂
      refine ⟨⟨?_, h₁⟩, by simp [h₂]⟩
      rw [o.val_mul, h₁.1, ← Nat.pow_add, List.length_cons, Nat.pow_succ, Nat.mul_two]

variable (rbase : Array Char → Nat → Nat → α) (D : Nat) (arr : Array Char)

/--
The value of the `len ≤ 2ᵏ` digits of `arr` from `start`, for the powers `ps` below `10^(2ᵏ)`:
the high digits times the top power plus the low `2ᵏ⁻¹` digits, recursively, and `rbase` for
`D` digits or fewer.
-/
public def decVal : List α → Nat → Nat → α
  | [], start, len => rbase arr start len
  | p :: ps, start, len =>
    if len ≤ D then rbase arr start len
    else if len ≤ 2 ^ ps.length then decVal ps start len
    else
      o.add (o.mul (decVal ps start (len - 2 ^ ps.length)) p)
        (decVal ps (start + (len - 2 ^ ps.length)) (2 ^ ps.length))

/-- The value of the decimal digits of `arr`, like `Nat.ofDigitChars 10`. -/
public def fromDec : α :=
  o.decVal rbase D arr (o.powsN (Nat.log2 arr.size + 1)) 0 arr.size

variable (hrbase : ∀ start len, start + len ≤ arr.size →
  o.val (rbase arr start len) = Nat.ofDigitChars 10 (chars arr start len) 0)

private theorem chars_split (start hi lo : Nat) (_h : start + hi + lo ≤ arr.size) :
    chars arr start (hi + lo) = chars arr start hi ++ chars arr (start + hi) lo := by
  unfold chars
  rw [List.take_add, List.drop_drop]

private theorem length_chars (start len : Nat) (h : start + len ≤ arr.size) :
    (chars arr start len).length = len := by
  unfold chars
  simp; lia

include hrbase in
public theorem decVal_spec : ∀ (ps : List α) (start len : Nat), o.IsPows ps →
    start + len ≤ arr.size → len ≤ 2 ^ ps.length →
    o.val (o.decVal rbase D arr ps start len) = Nat.ofDigitChars 10 (chars arr start len) 0 := by
  intro ps
  induction ps with
  | nil => intro start len _ h _; rw [decVal, hrbase _ _ h]
  | cons p ps ih =>
    intro start len hps h hlen
    rw [decVal]
    split
    · exact hrbase _ _ h
    split
    · exact ih _ _ hps.2 h (by assumption)
    · rename_i _ hlo
      rw [List.length_cons, Nat.pow_succ, Nat.mul_two] at hlen
      have e := chars_split arr start (len - 2 ^ ps.length) (2 ^ ps.length) (by lia)
      rw [Nat.sub_add_cancel (by lia)] at e
      rw [o.val_add, o.val_mul, ih _ _ hps.2 (by lia) (by lia),
        ih _ _ hps.2 (by lia) (Nat.le_refl _),
        hps.1, e, Nat.ofDigitChars_append,
        Nat.ofDigitChars_eq_ofDigitChars_zero (l := chars arr (start + (len - 2 ^ ps.length)) _)
          (init := Nat.ofDigitChars 10 (chars arr start (len - 2 ^ ps.length)) 0),
        length_chars arr _ _ (by lia), Nat.mul_comm]

include hrbase in
public theorem fromDec_spec :
    o.val (o.fromDec rbase D arr) = Nat.ofDigitChars 10 arr.toList 0 := by
  have hc : chars arr 0 arr.size = arr.toList := by
    simp [chars, List.take_of_length_le]
  obtain ⟨h₁, h₂⟩ := o.isPows_powsN (Nat.log2 arr.size + 1)
  rw [fromDec, o.decVal_spec rbase D arr hrbase _ _ _ h₁ (by lia)
    (by rw [h₂]; exact Nat.le_of_lt (Nat.lt_log2_self)), hc]

end NatOps

end MPN
