/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import MPN.Mul.Toom4

/-!
# FFT multiplication

Schönhage–Strassen multiplication, like GMP's `mpn_mul_fft`: `a` and `b` are cut into `K = 2ᵏ`
pieces, whose products are the coefficients of a convolution. The convolution is computed modulo
the Fermat number `F = 2ᴺ + 1`, large enough to hold each coefficient, by a discrete Fourier
transform of length `K` with the root of unity `ω = 2^(2N / K)`: multiplying by a power of `ω` is
a shift, so the transforms need no products, and the `K` pointwise products are products of `N`
bits.

This first part is the arithmetic modulo `F` behind the transform, on natural numbers: finite
sums, and the inversion of the transform. The transform of length `K` inverts because its
geometric sums `1 + x + ⋯ + x^(K - 1)` are the products `(1 + x) (1 + x²) ⋯ (1 + x^(K / 2))`, one
of whose factors vanishes when `x` is a power of `ω` other than `1`, since `ω^(K / 2) ≡ -1`. No
division and no primality are needed.
-/

namespace MPN.FFT

/-! ## Finite sums -/

/-- `f 0 + f 1 + ⋯ + f (n - 1)`. -/
@[expose] public def sumRange (f : Nat → Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => sumRange f n + f n

@[simp] public theorem sumRange_zero (f : Nat → Nat) : sumRange f 0 = 0 := rfl

public theorem sumRange_succ (f : Nat → Nat) (n : Nat) :
    sumRange f (n + 1) = sumRange f n + f n := rfl

public theorem sumRange_congr {f g : Nat → Nat} {n : Nat} (h : ∀ i < n, f i = g i) :
    sumRange f n = sumRange g n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [sumRange_succ, sumRange_succ, ih (fun i hi => h i (by lia)), h n (by lia)]

/-- Sums of terms that agree modulo `F` agree modulo `F`. -/
public theorem sumRange_mod {f g : Nat → Nat} {n F : Nat} (h : ∀ i < n, f i % F = g i % F) :
    sumRange f n % F = sumRange g n % F := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [sumRange_succ, sumRange_succ, Nat.add_mod, ih (fun i hi => h i (by lia)), h n (by lia),
      ← Nat.add_mod]

public theorem sumRange_mul_left (c : Nat) (f : Nat → Nat) (n : Nat) :
    c * sumRange f n = sumRange (fun i => c * f i) n := by
  induction n with
  | zero => simp
  | succ n ih => rw [sumRange_succ, sumRange_succ, Nat.mul_add, ih]

public theorem sumRange_mul_right (c : Nat) (f : Nat → Nat) (n : Nat) :
    sumRange f n * c = sumRange (fun i => f i * c) n := by
  rw [Nat.mul_comm, sumRange_mul_left]
  exact sumRange_congr fun i _ => Nat.mul_comm _ _

public theorem sumRange_add (f g : Nat → Nat) (n : Nat) :
    sumRange (fun i => f i + g i) n = sumRange f n + sumRange g n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [sumRange_succ, sumRange_succ, sumRange_succ, ih]; lia

/-- Double sums can be summed in either order. -/
public theorem sumRange_comm (f : Nat → Nat → Nat) (m n : Nat) :
    sumRange (fun j => sumRange (fun i => f i j) m) n =
      sumRange (fun i => sumRange (fun j => f i j) n) m := by
  induction n with
  | zero =>
    simp only [sumRange_zero]
    induction m with
    | zero => rfl
    | succ m ih => rw [sumRange_succ, ← ih]
  | succ n ih =>
    rw [sumRange_succ, ih, ← sumRange_add]
    rfl

public theorem sumRange_const_zero (n : Nat) : sumRange (fun _ => 0) n = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => rw [sumRange_succ, ih]

/-- A sum whose terms vanish modulo `F` except at `l` is the term at `l`, modulo `F`. -/
public theorem sumRange_single_mod {f : Nat → Nat} {n F l : Nat} (hl : l < n)
    (h : ∀ i < n, i ≠ l → f i % F = 0) : sumRange f n % F = f l % F := by
  induction n with
  | zero => lia
  | succ n ih =>
    rw [sumRange_succ]
    by_cases hln : l = n
    · subst hln
      have : sumRange f l % F = 0 := by
        rw [sumRange_mod (g := fun _ => 0)
            (fun i hi => by rw [h i (by lia) (by lia), Nat.zero_mod]),
          sumRange_const_zero, Nat.zero_mod]
      rw [Nat.add_mod, this, Nat.zero_add, Nat.mod_mod]
    · rw [Nat.add_mod, ih (by lia) (fun i hi hil => h i (by lia) hil), h n (by lia) (Ne.symm hln),
        Nat.add_zero, Nat.mod_mod]

/-! ## Geometric sums of length `2ᵏ` -/

/-- `1 + x + ⋯ + x^(2ᵏ⁺¹ - 1) = (1 + x + ⋯ + x^(2ᵏ - 1)) (1 + x^(2ᵏ))`. -/
public theorem sumRange_pow_two_succ (x k : Nat) :
    sumRange (x ^ ·) (2 ^ (k + 1)) = sumRange (x ^ ·) (2 ^ k) * (1 + x ^ 2 ^ k) := by
  -- The second half is the first times `x^(2ᵏ)`.
  have split : ∀ m, sumRange (x ^ ·) (2 ^ k + m) =
      sumRange (x ^ ·) (2 ^ k) + x ^ 2 ^ k * sumRange (x ^ ·) m := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      rw [← Nat.add_assoc, sumRange_succ, ih, sumRange_succ, Nat.mul_add, Nat.pow_add]
      lia
  rw [Nat.pow_succ, Nat.mul_two, split, Nat.mul_add, Nat.mul_one, Nat.mul_comm]

/-- When some `x^(2ˢ)`, `s < k`, is `-1` modulo `F`, the geometric sum of length `2ᵏ` vanishes. -/
public theorem sumRange_pow_two_mod {x k s F : Nat} (hs : s < k)
    (hx : (x ^ 2 ^ s + 1) % F = 0) : sumRange (x ^ ·) (2 ^ k) % F = 0 := by
  induction k with
  | zero => lia
  | succ k ih =>
    rw [sumRange_pow_two_succ, Nat.mul_mod]
    by_cases hsk : s = k
    · subst hsk
      rw [Nat.add_comm 1, hx, Nat.mul_zero, Nat.zero_mod]
    · rw [ih (by lia), Nat.zero_mul, Nat.zero_mod]

/-! ## Roots of unity -/

/-- `y + 1` divides `yᵘ + 1` for an odd `u`. -/
public theorem dvd_pow_odd_add_one (y u : Nat) (hu : u % 2 = 1) : y + 1 ∣ y ^ u + 1 := by
  obtain ⟨t, rfl⟩ : ∃ t, u = 2 * t + 1 := ⟨u / 2, by lia⟩
  rcases Nat.eq_zero_or_pos y with hy | hy
  · subst hy; simp
  obtain ⟨z, rfl⟩ : ∃ z, y = z + 1 := ⟨y - 1, by lia⟩
  induction t with
  | zero => simp
  | succ t ih =>
    -- `y^(2t + 3) + 1 + (y + 1) (y - 1) = y² (y^(2t + 1) + 1)`.
    have e : (z + 1) ^ (2 * (t + 1) + 1) + 1 + (z + 1 + 1) * z =
        (z + 1) * (z + 1) * ((z + 1) ^ (2 * t + 1) + 1) := by
      rw [show 2 * (t + 1) + 1 = 2 * t + 1 + 2 by lia, Nat.pow_add]
      grind
    have h := Nat.dvd_mul_left_of_dvd (ih (by lia)) ((z + 1) * (z + 1))
    rw [← e] at h
    exact (Nat.dvd_add_left (Nat.dvd_mul_right _ _)).mp h

/-- `-1` to an odd power is `-1`, modulo `F`. -/
public theorem pow_odd_mod {y F u : Nat} (hy : (y + 1) % F = 0) (hu : u % 2 = 1) :
    (y ^ u + 1) % F = 0 :=
  Nat.mod_eq_zero_of_dvd
    (Nat.dvd_trans (Nat.dvd_of_mod_eq_zero hy) (dvd_pow_odd_add_one y u hu))

/-- Every positive `d` is `2ᵛ u` with `u` odd. -/
public theorem exists_two_pow_mul_odd (d : Nat) (hd : 0 < d) :
    ∃ v u, d = 2 ^ v * u ∧ u % 2 = 1 := by
  induction d using Nat.strongRecOn with
  | ind d ih =>
    rcases Nat.mod_two_eq_zero_or_one d with h | h
    · obtain ⟨v, u, e, hu⟩ := ih (d / 2) (by lia) (by lia)
      exact ⟨v + 1, u, by rw [Nat.pow_succ]; lia, hu⟩
    · exact ⟨0, d, by simp, h⟩

/--
When `ω^(2ᵏ⁻¹) ≡ -1` modulo `F`, every power `ωᵈ` with `0 < d < 2ᵏ` has a power `(ωᵈ)^(2ˢ)`,
`s < k`, that is `-1` modulo `F`: with `d = 2ᵛ u`, `u` odd, take `s = k - 1 - v`.
-/
public theorem exists_pow_two_neg_one {w F k d : Nat} (hw : (w ^ 2 ^ (k - 1) + 1) % F = 0)
    (hd : 0 < d) (hdk : d < 2 ^ k) : ∃ s < k, ((w ^ d) ^ 2 ^ s + 1) % F = 0 := by
  obtain ⟨v, u, rfl, hu⟩ := exists_two_pow_mul_odd d hd
  have hv : v < k := by
    have : 2 ^ v ≤ 2 ^ v * u := Nat.le_mul_of_pos_right _ (by lia)
    exact (Nat.pow_lt_pow_iff_right (show 1 < 2 by decide)).1 (by lia)
  refine ⟨k - 1 - v, by lia, ?_⟩
  have e : (w ^ (2 ^ v * u)) ^ 2 ^ (k - 1 - v) = (w ^ 2 ^ (k - 1)) ^ u := by
    rw [← Nat.pow_mul, ← Nat.pow_mul]
    congr 1
    rw [Nat.mul_comm (2 ^ v) u, Nat.mul_assoc, ← Nat.pow_add,
      show v + (k - 1 - v) = k - 1 by lia, Nat.mul_comm]
  rw [e]
  exact pow_odd_mod hw hu

/-- The square of `-1` is `1`, modulo `F`. -/
public theorem sq_of_neg_one {y F : Nat} (hy : (y + 1) % F = 0) : (y * y) % F = 1 % F := by
  have h₁ : (y * (y + 1)) % F = 0 := by rw [Nat.mul_mod, hy, Nat.mul_zero, Nat.zero_mod]
  have e : y * y + (y + 1) = y * (y + 1) + 1 := by grind
  have := congrArg (· % F) e
  rw [Nat.add_mod, hy, Nat.add_zero, Nat.mod_mod, Nat.add_mod (y * (y + 1)), h₁,
    Nat.zero_add, Nat.mod_mod] at this
  exact this

/--
The inversion of the transform: with `ω^(2ᵏ⁻¹) ≡ -1` and `ω ω' ≡ 1` modulo `F`, transforming
`z` by `ω` and the result by `ω'` gives `2ᵏ z`, modulo `F`.
-/
public theorem inverse_mod (w w' F k : Nat) (hk : 1 ≤ k) (hw : (w ^ 2 ^ (k - 1) + 1) % F = 0)
    (hww : (w * w') % F = 1 % F) (z : Nat → Nat) (l : Nat) (hl : l < 2 ^ k) :
    sumRange (fun j => sumRange (fun i => z i * w ^ (i * j)) (2 ^ k) * w' ^ (j * l)) (2 ^ k) % F =
      (2 ^ k * z l) % F := by
  -- `Σⱼ (Σᵢ zᵢ ωⁱʲ) ω'ʲˡ = Σᵢ zᵢ Σⱼ (ωⁱ ω'ˡ)ʲ`.
  have e : sumRange (fun j => sumRange (fun i => z i * w ^ (i * j)) (2 ^ k) * w' ^ (j * l))
      (2 ^ k) = sumRange (fun i => z i * sumRange ((w ^ i * w' ^ l) ^ ·) (2 ^ k)) (2 ^ k) := by
    rw [sumRange_congr (g := fun j => sumRange (fun i => z i * (w ^ i * w' ^ l) ^ j) (2 ^ k))
      (fun j _ => by
        rw [sumRange_mul_right]
        exact sumRange_congr fun i _ => by
          rw [Nat.mul_pow, ← Nat.pow_mul, ← Nat.pow_mul, Nat.mul_comm l j]; grind),
      sumRange_comm]
    exact sumRange_congr fun i _ => by rw [sumRange_mul_left]
  rw [e]
  -- `ωᴷ ≡ 1`.
  have hK : (w ^ 2 ^ k) % F = 1 % F := by
    have := sq_of_neg_one hw
    rw [← Nat.pow_two, ← Nat.pow_mul,
      show 2 ^ (k - 1) * 2 = 2 ^ k by rw [← Nat.pow_succ]; congr 1; lia] at this
    exact this
  -- `ωⁿ ω'ⁿ ≡ 1`.
  have hpow : ∀ n, (w ^ n * w' ^ n) % F = 1 % F := fun n => by
    rw [← Nat.mul_pow, Nat.pow_mod, hww, ← Nat.pow_mod, Nat.one_pow]
  rw [sumRange_single_mod hl (fun i hi hil => ?_)]
  · -- At `i = l`, every term is `1`.
    rw [Nat.mul_mod, sumRange_mod (g := fun _ => 1) (fun j _ => by
      rw [Nat.pow_mod, hpow l, ← Nat.pow_mod, Nat.one_pow]), ← Nat.mul_mod]
    have : sumRange (fun _ => 1) (2 ^ k) = 2 ^ k := by
      generalize 2 ^ k = K
      induction K with
      | zero => rfl
      | succ K ih => rw [sumRange_succ, ih]
    rw [this, Nat.mul_comm]
  · -- Elsewhere, `ωⁱ ω'ˡ ≡ ωᵈ` with `0 < d < 2ᵏ`, whose geometric sum vanishes.
    have hd : 0 < (i + 2 ^ k - l) % 2 ^ k := by
      rcases Nat.lt_or_ge i l with h | h
      · rw [Nat.mod_eq_of_lt (by lia)]; lia
      · rw [show i + 2 ^ k - l = (i - l) + 2 ^ k by lia, Nat.add_mod_right,
          Nat.mod_eq_of_lt (by lia)]
        lia
    generalize hdd : (i + 2 ^ k - l) % 2 ^ k = d at hd
    have hdk : d < 2 ^ k := by rw [← hdd]; exact Nat.mod_lt _ (Nat.two_pow_pos k)
    -- `d + l = i + 2ᵏ c`.
    have hdl : ∃ c, d + l = i + 2 ^ k * c := by
      rcases Nat.lt_or_ge i l with h | h
      · refine ⟨1, ?_⟩
        rw [← hdd, Nat.mod_eq_of_lt (by lia)]; lia
      · refine ⟨0, ?_⟩
        rw [← hdd, show i + 2 ^ k - l = (i - l) + 2 ^ k by lia, Nat.add_mod_right,
          Nat.mod_eq_of_lt (by lia)]
        lia
    obtain ⟨c, hc⟩ := hdl
    have hx : (w ^ i * w' ^ l) % F = (w ^ d) % F := by
      -- `ωᵈ ≡ ωᵈ (ωˡ ω'ˡ) = ω^(d + l) ω'ˡ ≡ ωⁱ ω'ˡ`.
      have h₁ : (w ^ d) % F = (w ^ d * (w ^ l * w' ^ l)) % F := by
        rw [Nat.mul_mod (w ^ d), hpow l, ← Nat.mul_mod, Nat.mul_one]
      have h₂ : w ^ d * (w ^ l * w' ^ l) = w ^ i * (w ^ 2 ^ k) ^ c * w' ^ l := by
        rw [← Nat.mul_assoc, ← Nat.pow_add, hc, Nat.pow_add, Nat.pow_mul]
      have hKc : ((w ^ 2 ^ k) ^ c) % F = 1 % F := by
        rw [Nat.pow_mod, hK, ← Nat.pow_mod, Nat.one_pow]
      have h₃ : (w ^ i * (w ^ 2 ^ k) ^ c * w' ^ l) % F = (w ^ i * w' ^ l) % F := by
        rw [show w ^ i * (w ^ 2 ^ k) ^ c * w' ^ l = (w ^ 2 ^ k) ^ c * (w ^ i * w' ^ l) by
          rw [Nat.mul_comm (w ^ i), Nat.mul_assoc], Nat.mul_mod, hKc, ← Nat.mul_mod, Nat.one_mul]
      rw [h₁, h₂, h₃]
    obtain ⟨s, hs, hroot⟩ := exists_pow_two_neg_one hw hd hdk
    have hsum : sumRange ((w ^ i * w' ^ l) ^ ·) (2 ^ k) % F = 0 := by
      rw [sumRange_mod (g := ((w ^ d) ^ ·)) (fun j _ => by
        rw [Nat.pow_mod, hx, ← Nat.pow_mod])]
      exact sumRange_pow_two_mod hs hroot
    rw [Nat.mul_mod, hsum, Nat.mul_zero, Nat.zero_mod]

/-- A congruence of natural numbers is a divisibility of their difference in `Int`. -/
public theorem mod_eq_iff_dvd {a b F : Nat} : a % F = b % F ↔ (F : Int) ∣ (a : Int) - b := by
  rw [← Int.ofNat_inj, Int.natCast_emod, Int.natCast_emod, Int.emod_eq_emod_iff_emod_sub_eq_zero,
    Int.dvd_iff_emod_eq_zero]

public theorem dvd_mod_sub (x F : Nat) : (F : Int) ∣ ((x % F : Nat) : Int) - x :=
  mod_eq_iff_dvd.1 (Nat.mod_mod _ _)

/-! ## Polynomials -/

/-- `polyVal` is a finite sum, over any range that covers the coefficients. -/
public theorem polyVal_eq_sumRange (x : Nat) (as : List Nat) (n : Nat) (h : as.length ≤ n) :
    polyVal x as = sumRange (fun i => as.getD i 0 * x ^ i) n := by
  induction as generalizing n with
  | nil =>
    simp only [polyVal, List.getD_nil, Nat.zero_mul]
    exact (sumRange_const_zero n).symm
  | cons a as ih =>
    obtain ⟨n, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by simp at h; lia⟩
    rw [polyVal, ih n (by simp at h; lia)]
    -- Peel off the first term.
    have shift : ∀ m, sumRange (fun i => (a :: as).getD i 0 * x ^ i) (m + 1) =
        a + x * sumRange (fun i => as.getD i 0 * x ^ i) m := by
      intro m
      induction m with
      | zero => simp [sumRange]
      | succ m ihm =>
        rw [sumRange_succ, ihm, sumRange_succ, Nat.mul_add]
        simp only [List.getD_cons_succ, Nat.pow_succ]
        grind
    rw [shift]

/-- Evaluating at congruent points gives congruent values. -/
public theorem polyVal_mod {x y F : Nat} (h : x % F = y % F) (as : List Nat) :
    polyVal x as % F = polyVal y as % F := by
  induction as with
  | nil => rfl
  | cons a as ih =>
    simp only [polyVal]
    rw [Nat.add_mod, Nat.mul_mod, h, ih, ← Nat.mul_mod, ← Nat.add_mod]

/-- The sum of two coefficient lists. -/
@[expose] public def polyAdd : List Nat → List Nat → List Nat
  | [], bs => bs
  | as, [] => as
  | a :: as, b :: bs => (a + b) :: polyAdd as bs

/-- The product of two coefficient lists: the convolution of the coefficients. -/
@[expose] public def polyMul : List Nat → List Nat → List Nat
  | [], _ => []
  | a :: as, bs => polyAdd (bs.map (a * ·)) (0 :: polyMul as bs)

public theorem polyVal_polyAdd (x : Nat) (as bs : List Nat) :
    polyVal x (polyAdd as bs) = polyVal x as + polyVal x bs := by
  induction as generalizing bs with
  | nil => simp [polyAdd, polyVal]
  | cons a as ih =>
    cases bs with
    | nil => simp [polyAdd, polyVal]
    | cons b bs => simp only [polyAdd, polyVal, ih]; grind

public theorem polyVal_map_mul (x c : Nat) (bs : List Nat) :
    polyVal x (bs.map (c * ·)) = c * polyVal x bs := by
  induction bs with
  | nil => simp [polyVal]
  | cons b bs ih => simp only [List.map_cons, polyVal, ih]; grind

public theorem polyVal_polyMul (x : Nat) (as bs : List Nat) :
    polyVal x (polyMul as bs) = polyVal x as * polyVal x bs := by
  induction as with
  | nil => simp [polyMul, polyVal]
  | cons a as ih =>
    simp only [polyMul, polyVal_polyAdd, polyVal_map_mul, polyVal, ih]
    grind

public theorem length_polyAdd (as bs : List Nat) :
    (polyAdd as bs).length = max as.length bs.length := by
  induction as generalizing bs with
  | nil => simp [polyAdd]
  | cons a as ih =>
    cases bs with
    | nil => simp [polyAdd]
    | cons b bs => simp only [polyAdd, List.length_cons, ih]; lia

public theorem length_polyMul (as bs : List Nat) (hb : bs ≠ []) :
    (polyMul as bs).length ≤ as.length + bs.length - 1 := by
  induction as with
  | nil => simp [polyMul]
  | cons a as ih =>
    have : bs.length ≠ 0 := by simpa using hb
    simp only [polyMul, length_polyAdd, List.length_map, List.length_cons]
    lia

public theorem getD_polyAdd_le (as bs : List Nat) (i : Nat) :
    (polyAdd as bs).getD i 0 ≤ as.getD i 0 + bs.getD i 0 := by
  induction as generalizing bs i with
  | nil => simp [polyAdd]
  | cons a as ih =>
    cases bs with
    | nil => simp [polyAdd]
    | cons b bs =>
      cases i with
      | zero => simp [polyAdd]
      | succ i => simpa [polyAdd] using ih bs i

/-- With coefficients at most `A` and `B`, a product's coefficients are at most `len · A · B`. -/
public theorem getD_polyMul_le (as bs : List Nat) (A B : Nat) (ha : ∀ a ∈ as, a ≤ A)
    (hb : ∀ b ∈ bs, b ≤ B) (i : Nat) : (polyMul as bs).getD i 0 ≤ as.length * (A * B) := by
  induction as generalizing i with
  | nil => simp [polyMul]
  | cons a as ih =>
    simp only [polyMul, List.length_cons]
    refine Nat.le_trans (getD_polyAdd_le _ _ i) ?_
    have h₁ : (bs.map (a * ·)).getD i 0 ≤ A * B := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_map]
      cases h : bs[i]? with
      | none => simp
      | some b =>
        have hbm := hb b (List.mem_of_getElem? h)
        simp only [Option.map_some, Option.getD_some]
        exact Nat.mul_le_mul (ha a (by simp)) hbm
    have h₂ : (0 :: polyMul as bs).getD i 0 ≤ as.length * (A * B) := by
      cases i with
      | zero => simp
      | succ i => simpa using ih (fun a h => ha a (by simp [h])) i
    rw [Nat.add_mul, Nat.one_mul]
    lia

/-- The entries at even places. -/
@[expose] public def evens {α : Type} : List α → List α
  | a :: _ :: t => a :: evens t
  | [a] => [a]
  | [] => []

/-- The entries at odd places. -/
@[expose] public def odds {α : Type} : List α → List α
  | _ :: b :: t => b :: odds t
  | _ => []

public theorem map_evens {α β : Type} (f : α → β) (as : List α) :
    (evens as).map f = evens (as.map f) := by
  induction as using evens.induct with
  | case1 a b t ih => simp [evens, ih]
  | case2 a => simp [evens]
  | case3 => simp [evens]

public theorem map_odds {α β : Type} (f : α → β) (as : List α) :
    (odds as).map f = odds (as.map f) := by
  induction as using evens.induct with
  | case1 a b t ih => simp [odds, ih]
  | case2 a => simp [odds]
  | case3 => simp [odds]

public theorem mem_evens {α : Type} {as : List α} {x : α} (h : x ∈ evens as) : x ∈ as := by
  induction as using evens.induct with
  | case1 a b t ih =>
    simp only [evens, List.mem_cons] at h
    rcases h with h | h
    · simp [h]
    · simp [ih h]
  | case2 a => simpa [evens] using h
  | case3 => simp [evens] at h

public theorem mem_odds {α : Type} {as : List α} {x : α} (h : x ∈ odds as) : x ∈ as := by
  induction as using evens.induct with
  | case1 a b t ih =>
    simp only [odds, List.mem_cons] at h
    rcases h with h | h
    · simp [h]
    · simp [ih h]
  | case2 a => simp [odds] at h
  | case3 => simp [odds] at h

/-- `p(x) = p_even(x²) + x p_odd(x²)`, the split of the radix-2 transform. -/
public theorem polyVal_evens_odds (x : Nat) (as : List Nat) :
    polyVal x as = polyVal (x * x) (evens as) + x * polyVal (x * x) (odds as) := by
  induction as using evens.induct with
  | case1 a b t ih => simp only [evens, odds, polyVal, ih]; grind
  | case2 a => simp [evens, odds, polyVal]
  | case3 => simp [evens, odds, polyVal]

public theorem length_evens_odds {α : Type} (as : List α) (k : Nat) (h : as.length = 2 * k) :
    (evens as).length = k ∧ (odds as).length = k := by
  induction as using evens.induct generalizing k with
  | case1 a b t ih =>
    simp only [List.length_cons] at h
    obtain ⟨h₁, h₂⟩ := ih (k - 1) (by lia)
    simp only [evens, odds, List.length_cons, h₁, h₂]
    lia
  | case2 a => simp at h; lia
  | case3 => simp at h; simp [evens, odds]; lia

end MPN.FFT
