/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import MPN.LimbArray
public import MPN.Log2

/-!
# Arrays of words

`WordArray A L` gives arrays `A` of limbs `L` of `w` bits the reads and writes at `USize` indices
of their in-place loops, and the word operations on limbs that carry loops use: sums and
differences modulo `2ʷ` with their carries and borrows, shifts and comparisons with zero, each with
its value. `WordFolds A L` adds the in-place folds of lean4-scalar-arrays over one window (`foldThen`)
and over one window while reading two others of the same array (`fold2Then`), which make the array
exclusive once and then store without checks, and states that they are the plain loops of `uget`s
and `uset`s (`foldUInPlaceThen`, `foldUInPlace2Then`), which the proofs are about.

Code written once over these classes, with `@[expose, specialize]`, compiles in `main32` and
`main64` to the loops on their own arrays of 32-bit and 64-bit limbs.
-/

namespace MPN

/-! ## `USize` arithmetic -/

/-- `USize` addition that does not overflow. -/
public theorem _root_.USize.toNat_add_of_lt {a b : USize} (h : a.toNat + b.toNat < USize.size) :
    (a + b).toNat = a.toNat + b.toNat := by
  rw [USize.toNat_add]
  exact Nat.mod_eq_of_lt h

/-- The successor of an index below `n` does not overflow. -/
public theorem _root_.USize.toNat_add_one_of_lt {j n : USize} (h : j < n) :
    (j + 1).toNat = j.toNat + 1 := by
  have := USize.lt_iff_toNat_lt.1 h
  have := n.toNat_lt_size
  have : 4294967296 ≤ USize.size := by cases USize.size_eq <;> lia
  rw [USize.toNat_add_of_lt (a := j) (b := 1) (by rw [USize.toNat_one]; lia), USize.toNat_one]

namespace WordArray

/--
Whether `n` is below `USize.size`, decided on constants that are machine words: a comparison with
`USize.size` itself is one with a big number, a call into the runtime.
-/
@[inline] public def fitsU (n : Nat) : Bool :=
  n < 2147483648 || (System.Platform.numBits == 64 && n < 4611686018427387904)

public theorem lt_of_fitsU {n : Nat} (h : fitsU n = true) : n < USize.size := by
  simp only [fitsU, Bool.or_eq_true, decide_eq_true_eq, Bool.and_eq_true, beq_iff_eq] at h
  have := USize.size_eq
  rcases h with h | ⟨h₁, h₂⟩
  · rcases this with e | e <;> rw [e] <;> lia
  · rw [USize.size, h₁]; lia

variable {A L : Type} [LA : LimbArray A L]

/--
The bounds of a loop over limbs `rs` to `rs + n - 1` of `arr`: they are limbs of `arr`, and their
indices do not overflow.
-/
public abbrev LoopBound (arr : A) (rs n : USize) : Prop :=
  rs.toNat + n.toNat ≤ LA.size arr ∧ rs.toNat + n.toNat < USize.size

public theorem LoopBound.toNat_add {arr : A} {rs n j : USize} (hr : LoopBound arr rs n)
    (h : j < n) : (rs + j).toNat = rs.toNat + j.toNat := by
  have := USize.lt_iff_toNat_lt.1 h
  exact USize.toNat_add_of_lt (by lia)

public theorem LoopBound.uset_bound {arr : A} {rs n j : USize} (hr : LoopBound arr rs n)
    (h : j < n) : (rs + j).toNat < LA.size arr := by
  have := USize.lt_iff_toNat_lt.1 h
  rw [hr.toNat_add h]
  lia

/-- The same bounds on an array of the same size. -/
public theorem LoopBound.of_size {arr arr' : A} {rs n : USize} (hr : LoopBound arr rs n)
    (h : LA.size arr' = LA.size arr) : LoopBound arr' rs n := by
  simp only [LoopBound, h]; exact hr

end WordArray

open WordArray in
/--
Arrays `A` of limbs `L` with reads and writes at `USize` indices, and the word operations of their
limbs, with their values.
-/
public class WordArray (A : Type) (L : outParam Type) [LA : LimbArray A L] where
  /-- Limb `i` of an array, within it. -/
  uget : (a : A) → (i : USize) → i.toNat < LA.size a → L
  /-- Sets limb `i` of an array, within it. -/
  uset : (a : A) → (i : USize) → L → i.toNat < LA.size a → A
  uget_eq : ∀ a i h, uget a i h = LA.get a i.toNat
  size_uset : ∀ a i v h, LA.size (uset a i v h) = LA.size a
  get_uset : ∀ a i v h j, LA.get (uset a i v h) j = if i.toNat = j then v else LA.get a j
  /-- An array of `n` zero limbs. -/
  zeros : Nat → A
  size_zeros : ∀ n, LA.size (zeros n) = n
  val_get_zeros : ∀ n i, LA.val (LA.get (zeros n) i) = 0
  /-- The limbs past the end of an array read as zero. -/
  val_get_ge : ∀ a i, LA.size a ≤ i → LA.val (LA.get a i) = 0
  /-- `a` without its top limb, in place when `a` is not shared. -/
  pop : A → A
  size_pop : ∀ a, LA.size (pop a) = LA.size a - 1
  get_pop : ∀ a i, i < LA.size a - 1 → LA.get (pop a) i = LA.get a i
  /-- Limbs `i` to `j - 1` of `a`, up to its end, copied into a new array. -/
  extract : A → Nat → Nat → A
  size_extract : ∀ a i j, LA.size (extract a i j) = min j (LA.size a) - i
  get_extract : ∀ a i j k, k < LA.size (extract a i j) → LA.get (extract a i j) k = LA.get a (i + k)
  /-- The limb `0`. -/
  zero : L
  /-- The limb `1`. -/
  one : L
  /-- `x + y` modulo `2ʷ`. -/
  add : L → L → L
  /-- `x - y` modulo `2ʷ`. -/
  sub : L → L → L
  /-- `x 2ᵇ` modulo `2ʷ`, for `b < w`. -/
  shl : L → L → L
  /-- `⌊x / 2ᵇ⌋`, for `b < w`. -/
  shr : L → L → L
  /-- `c` plus the carry out of `x + y`. -/
  addh : L → L → L → L
  /-- `b` plus the borrow out of `x - y`. -/
  subh : L → L → L → L
  /-- `x y` modulo `2ʷ`. -/
  mul : L → L → L
  /-- The high limb of `x y`. -/
  mulh : L → L → L
  /-- `⌊(h 2ʷ + l) / d⌋`, for `h < d`: `div2 h l d`. -/
  div2 : L → L → L → L
  /-- The quotient and remainder of `h 2ʷ + l` by `d`, for `h < d`: one step of division. -/
  div2Rem : L → L → L → L × L
  /-- The double limb `y x + z + c`, low limb first: one step of a multiply-add pass. -/
  mulAdd2 : L → L → L → L → L × L
  /-- Whether `x < y`. -/
  ltB : L → L → Bool
  /-- Whether `x = y`. -/
  eqB : L → L → Bool
  /-- The bitwise and. -/
  land : L → L → L
  /-- The bitwise or. -/
  lor : L → L → L
  /-- The bitwise exclusive or. -/
  xor : L → L → L
  /-- `⌊log₂ x⌋`, and `0` for `0`, like `Nat.log2`. -/
  log2 : L → Nat
  /-- `1` or `0`. -/
  ofBool : Bool → L
  /--
  One limb of a multiply-subtract pass: `z - y x - c` modulo `2ʷ`, and the borrow out, for the
  borrow `c = unB h` carried in a form of the instance's choice, `h`, such as one that shortens the
  dependency chain from one limb to the next.
  -/
  subMulB : L → L → L → L → L × L
  /-- The borrow that the carried form `h` of `subMulB` stands for. -/
  unB : L → L
  /-- The carried form of the borrow `0`. -/
  b0 : L
  /-- `x + y + c` modulo `2ʷ`, and the carry out: one limb of an addition. -/
  addC : L → L → L → L × L
  /-- `x - y - c` modulo `2ʷ`, and the borrow out: one limb of a subtraction. -/
  subC : L → L → L → L × L
  /--
  One limb of Karatsuba's middle term, `v + x + (c - 2) - y - z` modulo `2ʷ`, and the carry out
  plus `2`, for a carry `c` between `0` and `3` that is the carry in plus `2`.
  -/
  addDiffC : L → L → L → L → L → L × L
  /-- `copyIn d o s so n`: `d` with its `n` limbs from `o` on replaced by those of `s` from `so`. -/
  copyIn : A → Nat → A → Nat → Nat → A
  /--
  One limb of a multiply-subtract pass by two limbs: `z - y (x₀ + 2ʷ x₁) - (c₀ + 2ʷ c₁)` modulo
  `2ʷ`, and the two limbs of the borrow out, like a limb of GMP's `mpn_submul_2`.
  -/
  subMul2B : L → L → L → L → L → L → L × L × L
  /-- Whether a limb is zero. -/
  isZero : L → Bool
  /-- A `USize` as a limb, modulo `2ʷ`. -/
  ofUSize : USize → L
  /-- The width `w` as a `USize`. -/
  wU : USize
  val_zero : LA.val zero = 0
  val_one : LA.val one = 1
  val_add : ∀ x y, LA.val (add x y) = (LA.val x + LA.val y) % 2 ^ LA.w
  val_sub : ∀ x y, LA.val (sub x y) = (LA.val x + (2 ^ LA.w - LA.val y)) % 2 ^ LA.w
  val_shl : ∀ x b, LA.val (shl x b) = LA.val x * 2 ^ (LA.val b % LA.w) % 2 ^ LA.w
  val_shr : ∀ x b, LA.val (shr x b) = LA.val x / 2 ^ (LA.val b % LA.w)
  val_addh : ∀ c x y,
    LA.val (addh c x y) = (LA.val c + (LA.val x + LA.val y) / 2 ^ LA.w) % 2 ^ LA.w
  val_subh : ∀ b x y,
    LA.val (subh b x y) = (LA.val b + if LA.val x < LA.val y then 1 else 0) % 2 ^ LA.w
  val_mul : ∀ x y, LA.val (mul x y) = LA.val x * LA.val y % 2 ^ LA.w
  val_mulh : ∀ x y, LA.val (mulh x y) = LA.val x * LA.val y / 2 ^ LA.w
  val_div2 : ∀ h l d, LA.val h < LA.val d →
    LA.val (div2 h l d) = (LA.val h * 2 ^ LA.w + LA.val l) / LA.val d
  val_mulAdd2 : ∀ y x z c, LA.val (mulAdd2 y x z c).1 + 2 ^ LA.w * LA.val (mulAdd2 y x z c).2 =
    LA.val y * LA.val x + LA.val z + LA.val c
  val_div2Rem : ∀ h l d, LA.val h < LA.val d →
    LA.val (div2Rem h l d).1 = (LA.val h * 2 ^ LA.w + LA.val l) / LA.val d ∧
      LA.val (div2Rem h l d).2 = (LA.val h * 2 ^ LA.w + LA.val l) % LA.val d
  ltB_iff : ∀ x y, ltB x y = true ↔ LA.val x < LA.val y
  val_subMulB : ∀ z y x h, LA.val (subMulB z y x h).1 + LA.val y * LA.val x + LA.val (unB h) =
    LA.val z + 2 ^ LA.w * LA.val (unB (subMulB z y x h).2)
  val_unB_b0 : LA.val (unB b0) = 0
  val_addC : ∀ x y c, LA.val (addC x y c).1 + 2 ^ LA.w * LA.val (addC x y c).2 =
    LA.val x + LA.val y + LA.val c
  val_subC : ∀ x y c, LA.val (subC x y c).1 + LA.val y + LA.val c =
    LA.val x + 2 ^ LA.w * LA.val (subC x y c).2
  val_addDiffC : ∀ v x y z c, LA.val c ≤ 3 →
    LA.val (addDiffC v x y z c).1 + 2 ^ LA.w * LA.val (addDiffC v x y z c).2 + LA.val y +
        LA.val z + 2 = LA.val v + LA.val x + LA.val c + 2 * 2 ^ LA.w ∧
      LA.val (addDiffC v x y z c).2 ≤ 3
  size_copyIn : ∀ d o s so n, o + n ≤ LA.size d → LA.size (copyIn d o s so n) = LA.size d
  get_copyIn : ∀ d o s so n i, o + n ≤ LA.size d → so + n ≤ LA.size s →
    LA.get (copyIn d o s so n) i =
      if o ≤ i ∧ i < o + n then LA.get s (so + (i - o)) else LA.get d i
  val_subMul2B : ∀ z y x₀ x₁ c₀ c₁, LA.val (subMul2B z y x₀ x₁ c₀ c₁).1 +
      LA.val y * (LA.val x₀ + 2 ^ LA.w * LA.val x₁) + (LA.val c₀ + 2 ^ LA.w * LA.val c₁) =
    LA.val z + 2 ^ LA.w * (LA.val (subMul2B z y x₀ x₁ c₀ c₁).2.1 +
      2 ^ LA.w * LA.val (subMul2B z y x₀ x₁ c₀ c₁).2.2)
  eqB_iff : ∀ x y, eqB x y = true ↔ LA.val x = LA.val y
  isZero_iff : ∀ x, isZero x = true ↔ LA.val x = 0
  val_ofUSize : ∀ i, LA.val (ofUSize i) = i.toNat % 2 ^ LA.w
  toNat_wU : wU.toNat = LA.w
  val_land : ∀ x y, LA.val (land x y) = LA.val x &&& LA.val y
  val_lor : ∀ x y, LA.val (lor x y) = LA.val x ||| LA.val y
  val_xor : ∀ x y, LA.val (xor x y) = LA.val x ^^^ LA.val y
  log2_eq : ∀ x, log2 x = (LA.val x).log2
  val_ofBool : ∀ b, LA.val (ofBool b) = if b then 1 else 0
  /-- Limbs have at least two bits, so that a limb holds a sum of two carries. -/
  w_ge : 2 ≤ LA.w

namespace WordArray

/-! ## Carries and borrows of limbs -/

/-- A sum below `2 B` carries at most `1`. -/
public theorem carry_le {s B : Nat} (h : s < 2 * B) : s / B ≤ 1 :=
  Nat.le_of_lt_succ ((Nat.div_lt_iff_lt_mul (by lia)).2 (by lia))

/-- `(a - b) % B` with its borrow, for `a, b < B`. -/
public theorem sub_mod_eq {a b B : Nat} (ha : a < B) (hb : b < B) :
    (a + (B - b)) % B + b = a + B * (if a < b then 1 else 0) := by
  split
  · rw [Nat.mod_eq_of_lt (by lia)]; lia
  · rw [show a + (B - b) = (a - b) + B * 1 by lia, Nat.add_mul_mod_self_left,
      Nat.mod_eq_of_lt (by lia)]
    lia

variable {A L : Type} [LA : LimbArray A L] [R : WordArray A L]

/-- `2ʷ` is at least `4`. -/
public theorem four_le : 4 ≤ 2 ^ LA.w :=
  calc 4 = 2 ^ 2 := rfl
    _ ≤ 2 ^ LA.w := Nat.pow_le_pow_right (by decide) R.w_ge

/-- The quotient and remainder of `div2`. -/
public theorem div2_rem (hi lo d : L) (h : LA.val hi < LA.val d) :
    LA.val (R.sub lo (R.mul (R.div2 hi lo d) d)) = (LA.val hi * 2 ^ LA.w + LA.val lo) % LA.val d ∧
      LA.val d * LA.val (R.div2 hi lo d) + LA.val (R.sub lo (R.mul (R.div2 hi lo d) d)) =
        LA.val hi * 2 ^ LA.w + LA.val lo := by
  have hq := R.val_div2 hi lo d h
  have hd := LA.val_lt d; have hl := LA.val_lt lo
  rw [R.val_sub, R.val_mul, hq]
  generalize LA.val hi = H at *
  generalize LA.val lo = Lo at *
  generalize LA.val d = D at *
  generalize 2 ^ LA.w = B at *
  have hD : 0 < D := by lia
  have e := Nat.div_add_mod (H * B + Lo) D
  have hr := Nat.mod_lt (H * B + Lo) hD
  generalize (H * B + Lo) / D = q at *
  generalize (H * B + Lo) % D = r at *
  -- `m` is `q D` modulo `B`, and `m + r` is `Lo` or `Lo + B`.
  have hB : 0 < B := by lia
  have hm := Nat.mod_lt (q * D) hB
  have hmr : (q * D % B + r) % B = Lo := by
    rw [Nat.mod_add_mod, Nat.mul_comm, e, Nat.mul_comm, Nat.mul_add_mod, Nat.mod_eq_of_lt hl]
  have hk := carry_le (s := q * D % B + r) (B := B) (by lia)
  have e₂ := Nat.mod_add_div (q * D % B + r) B
  rw [hmr] at e₂
  generalize q * D % B = m at *
  generalize (m + r) / B = k at *
  have h₁ : (Lo + (B - m)) % B = r := by
    rcases Nat.lt_or_ge k 1 with h₀ | h₁
    · obtain rfl : k = 0 := by lia
      rw [show Lo + (B - m) = r + B * 1 by lia, Nat.add_mul_mod_self_left,
        Nat.mod_eq_of_lt (by lia)]
    · obtain rfl : k = 1 := by lia
      rw [show Lo + (B - m) = r by lia, Nat.mod_eq_of_lt (by lia)]
  exact ⟨h₁, by rw [h₁]; exact e⟩

/-- `x + c` with its carry. -/
public theorem incr_step (x c : L) :
    LA.val (R.add x c) + 2 ^ LA.w * LA.val (R.addh R.zero x c) = LA.val x + LA.val c := by
  have hx := LA.val_lt x; have hc := LA.val_lt c; have hB := four_le (R := R)
  rw [R.val_add, R.val_addh, R.val_zero, Nat.zero_add]
  have := carry_le (s := LA.val x + LA.val c) (B := 2 ^ LA.w) (by lia)
  rw [Nat.mod_eq_of_lt (a := _ / _) (by lia)]
  exact Nat.mod_add_div _ _

/-- `x - c` with its borrow. -/
public theorem decr_step (x c : L) :
    LA.val (R.sub x c) + LA.val c = LA.val x + 2 ^ LA.w * LA.val (R.subh R.zero x c) := by
  have hx := LA.val_lt x; have hc := LA.val_lt c; have hB := four_le (R := R)
  rw [R.val_sub, R.val_subh, R.val_zero, Nat.zero_add, sub_mod_eq hx hc]
  split <;> simp [Nat.mod_eq_of_lt (show 1 < 2 ^ LA.w by lia)]

/-- `x + y + c` with its carry. -/
public theorem add_step (x y c : L) :
    LA.val (R.add (R.add x y) c) + 2 ^ LA.w * LA.val (R.addh (R.addh R.zero x y) (R.add x y) c) =
      LA.val x + LA.val y + LA.val c := by
  have hx := LA.val_lt x; have hy := LA.val_lt y; have hc := LA.val_lt c
  have hB := four_le (R := R)
  simp only [R.val_add, R.val_addh, R.val_zero, Nat.zero_add]
  generalize LA.val x = X at *
  generalize LA.val y = Y at *
  generalize LA.val c = C at *
  generalize 2 ^ LA.w = B at *
  have h₁ : (X + Y) / B ≤ 1 := carry_le (by lia)
  have hm := Nat.mod_lt (X + Y) (show 0 < B by lia)
  have h₂ : ((X + Y) % B + C) / B ≤ 1 := carry_le (by lia)
  rw [Nat.mod_eq_of_lt (a := (X + Y) / B) (by lia), Nat.mod_eq_of_lt (a := (X + Y) / B + _) (by lia)]
  have e₁ := Nat.mod_add_div (X + Y) B
  have e₂ := Nat.mod_add_div ((X + Y) % B + C) B
  generalize (X + Y) / B = q₁ at *
  generalize ((X + Y) % B + C) / B = q₂ at *
  rw [Nat.mul_add]
  lia

/-- `x - y - c` with its borrow. -/
public theorem sub_step (x y c : L) :
    LA.val (R.sub (R.sub x y) c) + LA.val y + LA.val c =
      LA.val x + 2 ^ LA.w * LA.val (R.subh (R.subh R.zero x y) (R.sub x y) c) := by
  have hx := LA.val_lt x; have hy := LA.val_lt y; have hc := LA.val_lt c
  have hB := four_le (R := R)
  simp only [R.val_sub, R.val_subh, R.val_zero, Nat.zero_add]
  generalize LA.val x = X at *
  generalize LA.val y = Y at *
  generalize LA.val c = C at *
  generalize 2 ^ LA.w = B at *
  have e₁ := sub_mod_eq hx hy
  have hm := Nat.mod_lt (X + (B - Y)) (show 0 < B by lia)
  have e₂ := sub_mod_eq hm hc
  generalize (X + (B - Y)) % B = D at *
  rw [Nat.mod_eq_of_lt (a := if X < Y then 1 else 0) (by split <;> lia),
    Nat.mod_eq_of_lt (a := (if X < Y then 1 else 0) + _) (by split <;> split <;> lia)]
  generalize (if X < Y then 1 else 0) = b₁ at *
  generalize (if D < C then 1 else 0) = b₂ at *
  rw [Nat.mul_add]
  lia

public theorem LoopBound.of_uset {arr : A} {rs n : USize} (hr : LoopBound arr rs n)
    (i : USize) (v : L) (h) : LoopBound (R.uset arr i v h) rs n :=
  hr.of_size (R.size_uset ..)

/-- `valAt` does not see a `uset` outside the limbs it reads. -/
public theorem valAt_uset_of (a : A) (i : USize) (v : L) (h : i.toNat < LA.size a)
    (lo n : Nat) (hi : i.toNat < lo ∨ lo + n ≤ i.toNat) :
    LimbArray.valAt (R.uset a i v h) lo n = LimbArray.valAt a lo n :=
  LimbArray.valAt_congr _ fun k h₁ h₂ => by
    rw [R.get_uset]
    simp only [show ¬(i.toNat = k) by lia, ↓reduceIte]

/-! ## In-place loops

`foldUInPlace n f arr rs hr j b` replaces limbs `rs + j` to `rs + n - 1` of `arr` while threading
an accumulator: limb `rs + j` holding `x` becomes `(f j hj x b).1`, and `(f j hj x b).2` is the
next accumulator. `f` may read other arrays, such as the operand of a multiply-subtract pass.
-/

/-- Replaces limbs `rs + j` to `rs + n - 1` of `arr` with `f`, threading an accumulator. -/
@[expose] public def foldUInPlace {β : Type} (n : USize) (f : (j : USize) → j < n → L → β → L × β)
    (arr : A) (rs : USize) (hr : LoopBound arr rs n) (j : USize) (b : β) : A × β :=
  if h : j < n then
    let p := f j h (R.uget arr (rs + j) (hr.uset_bound h)) b
    foldUInPlace n f (R.uset arr (rs + j) p.1 (hr.uset_bound h)) rs (hr.of_uset ..) (j + 1) p.2
  else
    (arr, b)
termination_by n.toNat - j.toNat
decreasing_by
  have := USize.lt_iff_toNat_lt.1 h
  rw [USize.toNat_add_one_of_lt h]
  lia

public theorem foldUInPlace_lt {β : Type} (n : USize) (f : (j : USize) → j < n → L → β → L × β)
    (arr : A) (rs : USize) (hr : LoopBound arr rs n) (j : USize) (b : β) (h : j < n) :
    foldUInPlace n f arr rs hr j b =
      foldUInPlace n f (R.uset arr (rs + j) (f j h (R.uget arr (rs + j) (hr.uset_bound h)) b).1
        (hr.uset_bound h)) rs (hr.of_uset ..) (j + 1)
        (f j h (R.uget arr (rs + j) (hr.uset_bound h)) b).2 := by
  rw [foldUInPlace]
  simp only [h, ↓reduceDIte]

public theorem foldUInPlace_ge {β : Type} (n : USize) (f : (j : USize) → j < n → L → β → L × β)
    (arr : A) (rs : USize) (hr : LoopBound arr rs n) (j : USize) (b : β) (h : ¬j < n) :
    foldUInPlace n f arr rs hr j b = (arr, b) := by
  rw [foldUInPlace]
  simp only [h, ↓reduceDIte]

public theorem size_foldUInPlace {β : Type} (n : USize) (f : (j : USize) → j < n → L → β → L × β)
    (arr : A) (rs : USize) (hr : LoopBound arr rs n) (j : USize) (b : β) :
    LA.size (foldUInPlace n f arr rs hr j b).1 = LA.size arr := by
  induction arr, hr, j, b using foldUInPlace.induct (R := R) n f rs with
  | case1 arr hr j b h p ih =>
    rw [foldUInPlace_lt _ _ _ _ _ _ _ h]
    exact ih.trans (R.size_uset ..)
  | case2 arr hr j b h =>
    rw [foldUInPlace_ge _ _ _ _ _ _ _ h]

/-- `foldUInPlace` followed by `g` on the new array and the last accumulator, like
`foldUInPlace2Then`. -/
@[expose]
public def foldUInPlaceThen {β γ : Type} (n : USize) (f : (j : USize) → j < n → L → β → L × β)
    (arr : A) (rs : USize) (hr : LoopBound arr rs n) (j : USize) (b : β)
    (g : (arr' : A) → LA.size arr' = LA.size arr → β → γ) : γ :=
  g (foldUInPlace n f arr rs hr j b).1 (size_foldUInPlace ..) (foldUInPlace n f arr rs hr j b).2

/-! ## In-place loops reading the same array

`foldUInPlace2 n f arr rs xs ys hr hx hy j b` replaces limbs `rs + j` to `rs + n - 1` of `arr`
while threading an accumulator, where `f` also receives limbs `xs + j` and `ys + j` of `arr`
itself, read at the time of the step. A function on several windows of one array, such as the
butterflies of the FFT on its flat array, can then read and write them without a second reference
to the array, which would copy it. When each window read starts at or after the window written, or
ends before it, the limbs read are those from before the loop (`foldUInPlace2_spec`).
-/

/-- Replaces limbs `rs + j` to `rs + n - 1` of `arr` with `f` of limbs `xs + j` and `ys + j`. -/
@[expose] public def foldUInPlace2 {β : Type} (n : USize)
    (f : (j : USize) → j < n → L → L → β → L × β)
    (arr : A) (rs xs ys : USize) (hr : LoopBound arr rs n) (hx : LoopBound arr xs n)
    (hy : LoopBound arr ys n) (j : USize) (b : β) : A × β :=
  if h : j < n then
    let p := f j h (R.uget arr (xs + j) (hx.uset_bound h)) (R.uget arr (ys + j) (hy.uset_bound h)) b
    foldUInPlace2 n f (R.uset arr (rs + j) p.1 (hr.uset_bound h)) rs xs ys (hr.of_uset ..)
      (hx.of_uset ..) (hy.of_uset ..) (j + 1) p.2
  else
    (arr, b)
termination_by n.toNat - j.toNat
decreasing_by
  have := USize.lt_iff_toNat_lt.1 h
  rw [USize.toNat_add_one_of_lt h]
  lia

public theorem size_foldUInPlace2 {β : Type} (n : USize)
    (f : (j : USize) → j < n → L → L → β → L × β) (arr : A)
    (rs xs ys : USize) (hr : LoopBound arr rs n) (hx : LoopBound arr xs n)
    (hy : LoopBound arr ys n) (j : USize) (b : β) :
    LA.size (foldUInPlace2 n f arr rs xs ys hr hx hy j b).1 = LA.size arr := by
  induction arr, hr, hx, hy, j, b using foldUInPlace2.induct (R := R) n f rs xs ys with
  | case1 arr hr hx hy j b h p ih =>
    rw [foldUInPlace2]
    simp only [h, ↓reduceDIte]
    exact ih.trans (R.size_uset ..)
  | case2 arr hr hx hy j b h =>
    rw [foldUInPlace2]
    simp only [h, ↓reduceDIte]

/--
`foldUInPlace2` followed by `g` on the new array and the last accumulator, which the loop calls
itself instead of returning a pair. `g` also receives a proof that the size is unchanged.
-/
@[expose]
public def foldUInPlace2Then {β γ : Type} (n : USize)
    (f : (j : USize) → j < n → L → L → β → L × β) (arr : A)
    (rs xs ys : USize) (hr : LoopBound arr rs n) (hx : LoopBound arr xs n)
    (hy : LoopBound arr ys n) (j : USize) (b : β)
    (g : (arr' : A) → LA.size arr' = LA.size arr → β → γ) : γ :=
  g (foldUInPlace2 n f arr rs xs ys hr hx hy j b).1 (size_foldUInPlace2 ..)
    (foldUInPlace2 n f arr rs xs ys hr hx hy j b).2

/--
The value of `foldUInPlace2` for a step with a linear carry law: if every step turns limbs `x`,
`y` and the accumulator `c` into a limb `out` and an accumulator `c'` with
`out + 2ʷ P c' + ux x + uy y + Q c = vx x + vy y + 2ʷ Q c' + P c` and keeps the invariant `I` of
the accumulator, then the limbs written and the last accumulator satisfy the same law with the
values of the windows, as long as the windows read are not overwritten before they are read. `P`
is a carry and `Q` a borrow.
-/
public theorem foldUInPlace2_spec {β : Type} (n : USize)
    (f : (j : USize) → j < n → L → L → β → L × β) (P Q : β → Nat)
    (ux uy vx vy : Nat) (I : β → Prop) (inv : ∀ j h x y c, I c → I (f j h x y c).2)
    (law : ∀ j h x y c, I c → LA.val (f j h x y c).1 + 2 ^ LA.w * P (f j h x y c).2 +
      ux * LA.val x + uy * LA.val y + Q c =
        vx * LA.val x + vy * LA.val y + 2 ^ LA.w * Q (f j h x y c).2 + P c)
    (arr : A) (rs xs ys : USize) (hr : LoopBound arr rs n) (hx : LoopBound arr xs n)
    (hy : LoopBound arr ys n)
    (hdx : rs.toNat ≤ xs.toNat ∨ xs.toNat + n.toNat ≤ rs.toNat)
    (hdy : rs.toNat ≤ ys.toNat ∨ ys.toNat + n.toNat ≤ rs.toNat) (j : USize) (b : β) (hb : I b) :
    LA.size (foldUInPlace2 n f arr rs xs ys hr hx hy j b).1 = LA.size arr ∧
      I (foldUInPlace2 n f arr rs xs ys hr hx hy j b).2 ∧
      (∀ i, (i < rs.toNat + j.toNat ∨ rs.toNat + n.toNat ≤ i) →
        LA.get (foldUInPlace2 n f arr rs xs ys hr hx hy j b).1 i = LA.get arr i) ∧
      LimbArray.valAt (foldUInPlace2 n f arr rs xs ys hr hx hy j b).1 (rs.toNat + j.toNat)
          (n.toNat - j.toNat) +
        2 ^ (LA.w * (n.toNat - j.toNat)) * P (foldUInPlace2 n f arr rs xs ys hr hx hy j b).2 +
        ux * LimbArray.valAt arr (xs.toNat + j.toNat) (n.toNat - j.toNat) +
        uy * LimbArray.valAt arr (ys.toNat + j.toNat) (n.toNat - j.toNat) + Q b =
      vx * LimbArray.valAt arr (xs.toNat + j.toNat) (n.toNat - j.toNat) +
        vy * LimbArray.valAt arr (ys.toNat + j.toNat) (n.toNat - j.toNat) +
        2 ^ (LA.w * (n.toNat - j.toNat)) * Q (foldUInPlace2 n f arr rs xs ys hr hx hy j b).2 +
        P b := by
  induction arr, hr, hx, hy, j, b using foldUInPlace2.induct (R := R) n f rs xs ys with
  | case1 arr hr hx hy j b h p ih =>
    rw [foldUInPlace2]
    simp only [h, ↓reduceDIte]
    have hI := inv j h (R.uget arr (xs + j) (hx.uset_bound h)) (R.uget arr (ys + j) (hy.uset_bound h))
      b hb
    have hj := USize.lt_iff_toNat_lt.1 h
    have hj₁ := USize.toNat_add_one_of_lt h
    have hri := hr.toNat_add h
    have hxi := hx.toNat_add h
    have hyi := hy.toNat_add h
    obtain ⟨ih₁, ih₀, ih₂, ih₃⟩ := ih hI
    rw [hj₁] at ih₂ ih₃
    rw [R.size_uset] at ih₁
    have hv : LA.get (foldUInPlace2 n f (R.uset arr (rs + j) p.1 (hr.uset_bound h)) rs xs ys
        (hr.of_uset ..) (hx.of_uset ..) (hy.of_uset ..) (j + 1) p.2).1 (rs.toNat + j.toNat) =
          p.1 := by
      rw [ih₂ _ (.inl (by lia)), R.get_uset]
      simp [hri]
    have hX : LimbArray.valAt (R.uset arr (rs + j) p.1 (hr.uset_bound h))
        (xs.toNat + (j.toNat + 1)) (n.toNat - (j.toNat + 1)) =
          LimbArray.valAt arr (xs.toNat + (j.toNat + 1)) (n.toNat - (j.toNat + 1)) :=
      valAt_uset_of _ _ _ _ _ _ (by rw [hri]; lia)
    have hY : LimbArray.valAt (R.uset arr (rs + j) p.1 (hr.uset_bound h))
        (ys.toNat + (j.toNat + 1)) (n.toNat - (j.toNat + 1)) =
          LimbArray.valAt arr (ys.toNat + (j.toNat + 1)) (n.toNat - (j.toNat + 1)) :=
      valAt_uset_of _ _ _ _ _ _ (by rw [hri]; lia)
    have hx' : R.uget arr (xs + j) (hx.uset_bound h) = LA.get arr (xs.toNat + j.toNat) := by
      rw [R.uget_eq, hxi]
    have hy' : R.uget arr (ys + j) (hy.uset_bound h) = LA.get arr (ys.toNat + j.toNat) := by
      rw [R.uget_eq, hyi]
    refine ⟨ih₁, ih₀, fun i hi => ?_, ?_⟩
    · rw [ih₂ i (by lia), R.get_uset]
      simp only [hri]
      split <;> lia
    · rw [hX, hY] at ih₃
      obtain ⟨k, hk⟩ : ∃ k, n.toNat - j.toNat = k + 1 := ⟨n.toNat - j.toNat - 1, by lia⟩
      rw [show n.toNat - (j.toNat + 1) = k by lia, ← Nat.add_assoc, ← Nat.add_assoc,
        ← Nat.add_assoc] at ih₃
      have hl := law j h (R.uget arr (xs + j) (hx.uset_bound h))
        (R.uget arr (ys + j) (hy.uset_bound h)) b hb
      rw [hx', hy'] at hl
      rw [hk, LimbArray.valAt_succ, LimbArray.valAt_succ, LimbArray.valAt_succ, hv, Nat.mul_succ,
        Nat.pow_add]
      show _ + _ * P (foldUInPlace2 n f (R.uset arr (rs + j) p.1 (hr.uset_bound h)) rs xs ys
        (hr.of_uset ..) (hx.of_uset ..) (hy.of_uset ..) (j + 1) p.2).2 + _ + _ + _ = _
      generalize (foldUInPlace2 n f (R.uset arr (rs + j) p.1 (hr.uset_bound h)) rs xs ys
        (hr.of_uset ..) (hx.of_uset ..) (hy.of_uset ..) (j + 1) p.2) = q at *
      simp only [p] at *
      generalize f j h (LA.get arr (xs.toNat + j.toNat)) (LA.get arr (ys.toNat + j.toNat)) b = p'
        at *
      generalize LimbArray.valAt q.1 _ _ = V at *
      generalize LimbArray.valAt arr (xs.toNat + j.toNat + 1) k = X at *
      generalize LimbArray.valAt arr (ys.toNat + j.toNat + 1) k = Y at *
      generalize 2 ^ (LA.w * k) = B at *
      generalize 2 ^ LA.w = W at *
      grind
  | case2 arr hr hx hy j b h =>
    rw [foldUInPlace2]
    have : n.toNat - j.toNat = 0 := by have := USize.lt_iff_toNat_lt (a := j) (b := n); lia
    simp [h, this, Nat.add_comm, hb]

/-- One step of the carry law of a fold, from the law of the rest. -/
private theorem law_step {o V P' Q' X Y x y Pp Qp Pb Qb W B ux uy vx vy : Nat}
    (ih : V + B * P' + ux * X + uy * Y + Qp = vx * X + vy * Y + B * Q' + Pp)
    (hl : o + W * Pp + ux * x + uy * y + Qb = vx * x + vy * y + W * Qp + Pb) :
    o + W * V + B * W * P' + ux * (x + W * X) + uy * (y + W * Y) + Qb =
      vx * (x + W * X) + vy * (y + W * Y) + B * W * Q' + Pb := by
  have := congrArg (W * ·) ih
  simp only [Nat.mul_add] at this
  grind

/--
Two passes of `foldUInPlace2` over the same windows in one: each step reads limbs `xs + j` and
`ys + j` once, writes `(f₁ j hj x y b₁).1` at `rs + j` and `(f₂ j hj x y b₂).1` at `ts + j`, and
threads the two accumulators apart, like the sum and the difference of the FFT's butterflies.
-/
@[expose] public def foldUInPlace2x2 {β₁ β₂ : Type} (n : USize)
    (f₁ : (j : USize) → j < n → L → L → β₁ → L × β₁)
    (f₂ : (j : USize) → j < n → L → L → β₂ → L × β₂)
    (arr : A) (rs ts xs ys : USize) (hr : LoopBound arr rs n) (ht : LoopBound arr ts n)
    (hx : LoopBound arr xs n) (hy : LoopBound arr ys n) (j : USize) (b₁ : β₁) (b₂ : β₂) :
    A × β₁ × β₂ :=
  if h : j < n then
    let x := R.uget arr (xs + j) (hx.uset_bound h)
    let y := R.uget arr (ys + j) (hy.uset_bound h)
    let p := f₁ j h x y b₁
    let q := f₂ j h x y b₂
    let a₁ := R.uset arr (rs + j) p.1 (hr.uset_bound h)
    foldUInPlace2x2 n f₁ f₂ (R.uset a₁ (ts + j) q.1 ((ht.of_uset ..).uset_bound h)) rs ts xs ys
      ((hr.of_uset ..).of_uset ..) ((ht.of_uset ..).of_uset ..) ((hx.of_uset ..).of_uset ..)
      ((hy.of_uset ..).of_uset ..) (j + 1) p.2 q.2
  else
    (arr, b₁, b₂)
termination_by n.toNat - j.toNat
decreasing_by
  have := USize.lt_iff_toNat_lt.1 h
  rw [USize.toNat_add_one_of_lt h]
  lia

public theorem size_foldUInPlace2x2 {β₁ β₂ : Type} (n : USize)
    (f₁ : (j : USize) → j < n → L → L → β₁ → L × β₁)
    (f₂ : (j : USize) → j < n → L → L → β₂ → L × β₂)
    (arr : A) (rs ts xs ys : USize) (hr : LoopBound arr rs n) (ht : LoopBound arr ts n)
    (hx : LoopBound arr xs n) (hy : LoopBound arr ys n) (j : USize) (b₁ : β₁) (b₂ : β₂) :
    LA.size (foldUInPlace2x2 n f₁ f₂ arr rs ts xs ys hr ht hx hy j b₁ b₂).1 = LA.size arr := by
  induction arr, hr, ht, hx, hy, j, b₁, b₂ using foldUInPlace2x2.induct (R := R) n f₁ f₂ rs ts xs ys
    with
  | case1 arr hr ht hx hy j b₁ b₂ h x y p q a₁ ih =>
    rw [foldUInPlace2x2]
    simp only [h, ↓reduceDIte]
    exact ih.trans ((R.size_uset ..).trans (R.size_uset ..))
  | case2 arr hr ht hx hy j b₁ b₂ h =>
    rw [foldUInPlace2x2]
    simp only [h, ↓reduceDIte]

/--
`foldUInPlace2x2` followed by `g` on the new array and the last accumulators, which the loop calls
itself instead of returning a triple.
-/
@[expose]
public def foldUInPlace2x2Then {β₁ β₂ γ : Type} (n : USize)
    (f₁ : (j : USize) → j < n → L → L → β₁ → L × β₁)
    (f₂ : (j : USize) → j < n → L → L → β₂ → L × β₂)
    (arr : A) (rs ts xs ys : USize) (hr : LoopBound arr rs n) (ht : LoopBound arr ts n)
    (hx : LoopBound arr xs n) (hy : LoopBound arr ys n) (j : USize) (b₁ : β₁) (b₂ : β₂)
    (g : (arr' : A) → LA.size arr' = LA.size arr → β₁ → β₂ → γ) : γ :=
  g (foldUInPlace2x2 n f₁ f₂ arr rs ts xs ys hr ht hx hy j b₁ b₂).1 (size_foldUInPlace2x2 ..)
    (foldUInPlace2x2 n f₁ f₂ arr rs ts xs ys hr ht hx hy j b₁ b₂).2.1
    (foldUInPlace2x2 n f₁ f₂ arr rs ts xs ys hr ht hx hy j b₁ b₂).2.2

/--
The values of `foldUInPlace2x2`, for steps with linear carry laws as in `foldUInPlace2_spec`, one
for each window written: the two windows written are disjoint, and neither overwrites a limb of
the windows read before it is read.
-/
public theorem foldUInPlace2x2_spec {β₁ β₂ : Type} (n : USize)
    (f₁ : (j : USize) → j < n → L → L → β₁ → L × β₁)
    (f₂ : (j : USize) → j < n → L → L → β₂ → L × β₂)
    (P₁ Q₁ : β₁ → Nat) (ux₁ uy₁ vx₁ vy₁ : Nat) (I₁ : β₁ → Prop)
    (inv₁ : ∀ j h x y c, I₁ c → I₁ (f₁ j h x y c).2)
    (law₁ : ∀ j h x y c, I₁ c → LA.val (f₁ j h x y c).1 + 2 ^ LA.w * P₁ (f₁ j h x y c).2 +
      ux₁ * LA.val x + uy₁ * LA.val y + Q₁ c =
        vx₁ * LA.val x + vy₁ * LA.val y + 2 ^ LA.w * Q₁ (f₁ j h x y c).2 + P₁ c)
    (P₂ Q₂ : β₂ → Nat) (ux₂ uy₂ vx₂ vy₂ : Nat) (I₂ : β₂ → Prop)
    (inv₂ : ∀ j h x y c, I₂ c → I₂ (f₂ j h x y c).2)
    (law₂ : ∀ j h x y c, I₂ c → LA.val (f₂ j h x y c).1 + 2 ^ LA.w * P₂ (f₂ j h x y c).2 +
      ux₂ * LA.val x + uy₂ * LA.val y + Q₂ c =
        vx₂ * LA.val x + vy₂ * LA.val y + 2 ^ LA.w * Q₂ (f₂ j h x y c).2 + P₂ c)
    (arr : A) (rs ts xs ys : USize) (hr : LoopBound arr rs n) (ht : LoopBound arr ts n)
    (hx : LoopBound arr xs n) (hy : LoopBound arr ys n)
    (hrt : rs.toNat + n.toNat ≤ ts.toNat ∨ ts.toNat + n.toNat ≤ rs.toNat)
    (hrx : rs.toNat ≤ xs.toNat ∨ xs.toNat + n.toNat ≤ rs.toNat)
    (hry : rs.toNat ≤ ys.toNat ∨ ys.toNat + n.toNat ≤ rs.toNat)
    (htx : ts.toNat ≤ xs.toNat ∨ xs.toNat + n.toNat ≤ ts.toNat)
    (hty : ts.toNat ≤ ys.toNat ∨ ys.toNat + n.toNat ≤ ts.toNat)
    (j : USize) (b₁ : β₁) (b₂ : β₂) (hb₁ : I₁ b₁) (hb₂ : I₂ b₂) :
    LA.size (foldUInPlace2x2 n f₁ f₂ arr rs ts xs ys hr ht hx hy j b₁ b₂).1 = LA.size arr ∧
      I₁ (foldUInPlace2x2 n f₁ f₂ arr rs ts xs ys hr ht hx hy j b₁ b₂).2.1 ∧
      I₂ (foldUInPlace2x2 n f₁ f₂ arr rs ts xs ys hr ht hx hy j b₁ b₂).2.2 ∧
      (∀ i, (i < rs.toNat + j.toNat ∨ rs.toNat + n.toNat ≤ i) →
        (i < ts.toNat + j.toNat ∨ ts.toNat + n.toNat ≤ i) →
        LA.get (foldUInPlace2x2 n f₁ f₂ arr rs ts xs ys hr ht hx hy j b₁ b₂).1 i = LA.get arr i) ∧
      LimbArray.valAt (foldUInPlace2x2 n f₁ f₂ arr rs ts xs ys hr ht hx hy j b₁ b₂).1
          (rs.toNat + j.toNat) (n.toNat - j.toNat) +
        2 ^ (LA.w * (n.toNat - j.toNat)) *
          P₁ (foldUInPlace2x2 n f₁ f₂ arr rs ts xs ys hr ht hx hy j b₁ b₂).2.1 +
        ux₁ * LimbArray.valAt arr (xs.toNat + j.toNat) (n.toNat - j.toNat) +
        uy₁ * LimbArray.valAt arr (ys.toNat + j.toNat) (n.toNat - j.toNat) + Q₁ b₁ =
      vx₁ * LimbArray.valAt arr (xs.toNat + j.toNat) (n.toNat - j.toNat) +
        vy₁ * LimbArray.valAt arr (ys.toNat + j.toNat) (n.toNat - j.toNat) +
        2 ^ (LA.w * (n.toNat - j.toNat)) *
          Q₁ (foldUInPlace2x2 n f₁ f₂ arr rs ts xs ys hr ht hx hy j b₁ b₂).2.1 + P₁ b₁ ∧
      LimbArray.valAt (foldUInPlace2x2 n f₁ f₂ arr rs ts xs ys hr ht hx hy j b₁ b₂).1
          (ts.toNat + j.toNat) (n.toNat - j.toNat) +
        2 ^ (LA.w * (n.toNat - j.toNat)) *
          P₂ (foldUInPlace2x2 n f₁ f₂ arr rs ts xs ys hr ht hx hy j b₁ b₂).2.2 +
        ux₂ * LimbArray.valAt arr (xs.toNat + j.toNat) (n.toNat - j.toNat) +
        uy₂ * LimbArray.valAt arr (ys.toNat + j.toNat) (n.toNat - j.toNat) + Q₂ b₂ =
      vx₂ * LimbArray.valAt arr (xs.toNat + j.toNat) (n.toNat - j.toNat) +
        vy₂ * LimbArray.valAt arr (ys.toNat + j.toNat) (n.toNat - j.toNat) +
        2 ^ (LA.w * (n.toNat - j.toNat)) *
          Q₂ (foldUInPlace2x2 n f₁ f₂ arr rs ts xs ys hr ht hx hy j b₁ b₂).2.2 + P₂ b₂ := by
  induction arr, hr, ht, hx, hy, j, b₁, b₂ using foldUInPlace2x2.induct (R := R) n f₁ f₂ rs ts xs ys
    with
  | case1 arr hr ht hx hy j b₁ b₂ h x y p q a₁ ih =>
    rw [foldUInPlace2x2]
    simp only [h, ↓reduceDIte]
    have hI₁ := inv₁ j h x y b₁ hb₁
    have hI₂ := inv₂ j h x y b₂ hb₂
    have hj := USize.lt_iff_toNat_lt.1 h
    have hj₁ := USize.toNat_add_one_of_lt h
    have hri := hr.toNat_add h
    have hti := ht.toNat_add h
    have hxi := hx.toNat_add h
    have hyi := hy.toNat_add h
    obtain ⟨ih₁, ih₀₁, ih₀₂, ih₂, ih₃, ih₄⟩ := ih hI₁ hI₂
    rw [hj₁] at ih₂ ih₃ ih₄
    rw [R.size_uset, R.size_uset] at ih₁
    generalize foldUInPlace2x2 (A := A) n f₁ f₂ _ rs ts xs ys _ _ _ _ (j + 1) p.2 q.2 = F at *
    -- The two limbs of step `j`, and the windows read above it.
    have hget : ∀ i, LA.get (R.uset a₁ (ts + j) q.1 ((ht.of_uset ..).uset_bound h)) i =
        if i = ts.toNat + j.toNat then q.1 else if i = rs.toNat + j.toNat then p.1 else
          LA.get arr i := by
      intro i
      simp only [a₁, R.get_uset, hri, hti]
      by_cases e₁ : i = ts.toNat + j.toNat
      · simp [e₁]
      · by_cases e₂ : i = rs.toNat + j.toNat
        · simp [e₂, show ¬ ts.toNat = rs.toNat by lia, show ¬ rs.toNat = ts.toNat by lia]
        · simp [e₁, e₂, show ¬ ts.toNat + j.toNat = i by lia,
            show ¬ rs.toNat + j.toNat = i by lia]
    have hv₁ : LA.get F.1 (rs.toNat + j.toNat) = p.1 := by
      rw [ih₂ _ (.inl (by lia)) (by lia), hget]
      simp only [show ¬ rs.toNat + j.toNat = ts.toNat + j.toNat by lia, ↓reduceIte]
    have hv₂ : LA.get F.1 (ts.toNat + j.toNat) = q.1 := by
      rw [ih₂ _ (by lia) (.inl (by lia)), hget]
      simp only [↓reduceIte]
    have hX : LimbArray.valAt (R.uset a₁ (ts + j) q.1 ((ht.of_uset ..).uset_bound h))
        (xs.toNat + (j.toNat + 1)) (n.toNat - (j.toNat + 1)) =
          LimbArray.valAt arr (xs.toNat + (j.toNat + 1)) (n.toNat - (j.toNat + 1)) :=
      LimbArray.valAt_congr _ fun i _ _ => by
        rw [hget]
        simp only [show ¬ i = ts.toNat + j.toNat by lia, show ¬ i = rs.toNat + j.toNat by lia,
          ↓reduceIte]
    have hY : LimbArray.valAt (R.uset a₁ (ts + j) q.1 ((ht.of_uset ..).uset_bound h))
        (ys.toNat + (j.toNat + 1)) (n.toNat - (j.toNat + 1)) =
          LimbArray.valAt arr (ys.toNat + (j.toNat + 1)) (n.toNat - (j.toNat + 1)) :=
      LimbArray.valAt_congr _ fun i _ _ => by
        rw [hget]
        simp only [show ¬ i = ts.toNat + j.toNat by lia, show ¬ i = rs.toNat + j.toNat by lia,
          ↓reduceIte]
    have hx' : x = LA.get arr (xs.toNat + j.toNat) := by simp only [x]; rw [R.uget_eq, hxi]
    have hy' : y = LA.get arr (ys.toNat + j.toNat) := by simp only [y]; rw [R.uget_eq, hyi]
    rw [hX, hY] at ih₃ ih₄
    obtain ⟨k, hk⟩ : ∃ k, n.toNat - j.toNat = k + 1 := ⟨n.toNat - j.toNat - 1, by lia⟩
    rw [show n.toNat - (j.toNat + 1) = k by lia] at ih₃ ih₄
    simp only [← Nat.add_assoc] at ih₃ ih₄
    have hl₁ := law₁ j h x y b₁ hb₁
    have hl₂ := law₂ j h x y b₂ hb₂
    refine ⟨ih₁, ih₀₁, ih₀₂, fun i hi₁ hi₂ => ?_, ?_, ?_⟩
    · rw [ih₂ i (by lia) (by lia), hget]
      simp only [show ¬ i = ts.toNat + j.toNat by lia, show ¬ i = rs.toNat + j.toNat by lia,
        ↓reduceIte]
    · rw [hk, LimbArray.valAt_succ, LimbArray.valAt_succ, LimbArray.valAt_succ, hv₁, Nat.mul_succ,
        Nat.pow_add, ← hx', ← hy']
      exact law_step ih₃ hl₁
    · rw [hk, LimbArray.valAt_succ, LimbArray.valAt_succ, LimbArray.valAt_succ, hv₂, Nat.mul_succ,
        Nat.pow_add, ← hx', ← hy']
      exact law_step ih₄ hl₂
  | case2 arr hr ht hx hy j b₁ b₂ h =>
    rw [foldUInPlace2x2]
    have : n.toNat - j.toNat = 0 := by have := USize.lt_iff_toNat_lt (a := j) (b := n); lia
    simp [h, this, Nat.add_comm, hb₁, hb₂]

/--
Three passes of `foldUInPlace` over three windows in one: each step reads the limbs at `rs + j`,
`ts + j` and `us + j`, then writes `(f₁ j hj x b₁).1`, `(f₂ j hj y b₂).1` and `(f₃ j hj z b₃).1`
back, and threads the three accumulators apart, like the first stage of Toom-3's interpolation.
-/
@[expose] public def foldUInPlace3 {β₁ β₂ β₃ : Type} (n : USize)
    (f₁ : (j : USize) → j < n → L → β₁ → L × β₁)
    (f₂ : (j : USize) → j < n → L → β₂ → L × β₂)
    (f₃ : (j : USize) → j < n → L → β₃ → L × β₃)
    (arr : A) (rs ts us : USize) (hr : LoopBound arr rs n) (ht : LoopBound arr ts n)
    (hu : LoopBound arr us n) (j : USize) (b₁ : β₁) (b₂ : β₂) (b₃ : β₃) :
    A × β₁ × β₂ × β₃ :=
  if h : j < n then
    let x := R.uget arr (rs + j) (hr.uset_bound h)
    let y := R.uget arr (ts + j) (ht.uset_bound h)
    let z := R.uget arr (us + j) (hu.uset_bound h)
    let p := f₁ j h x b₁
    let q := f₂ j h y b₂
    let r := f₃ j h z b₃
    let a₁ := R.uset arr (rs + j) p.1 (hr.uset_bound h)
    let a₂ := R.uset a₁ (ts + j) q.1 ((ht.of_uset ..).uset_bound h)
    foldUInPlace3 n f₁ f₂ f₃ (R.uset a₂ (us + j) r.1 (((hu.of_uset ..).of_uset ..).uset_bound h))
      rs ts us (((hr.of_uset ..).of_uset ..).of_uset ..) (((ht.of_uset ..).of_uset ..).of_uset ..)
      (((hu.of_uset ..).of_uset ..).of_uset ..) (j + 1) p.2 q.2 r.2
  else
    (arr, b₁, b₂, b₃)
termination_by n.toNat - j.toNat
decreasing_by
  have := USize.lt_iff_toNat_lt.1 h
  rw [USize.toNat_add_one_of_lt h]
  lia

public theorem size_foldUInPlace3 {β₁ β₂ β₃ : Type} (n : USize)
    (f₁ : (j : USize) → j < n → L → β₁ → L × β₁)
    (f₂ : (j : USize) → j < n → L → β₂ → L × β₂)
    (f₃ : (j : USize) → j < n → L → β₃ → L × β₃)
    (arr : A) (rs ts us : USize) (hr : LoopBound arr rs n) (ht : LoopBound arr ts n)
    (hu : LoopBound arr us n) (j : USize) (b₁ : β₁) (b₂ : β₂) (b₃ : β₃) :
    LA.size (foldUInPlace3 n f₁ f₂ f₃ arr rs ts us hr ht hu j b₁ b₂ b₃).1 = LA.size arr := by
  induction arr, hr, ht, hu, j, b₁, b₂, b₃ using foldUInPlace3.induct (R := R) n f₁ f₂ f₃ rs ts us
    with
  | case1 arr hr ht hu j b₁ b₂ b₃ h x y z p q r a₁ a₂ ih =>
    rw [foldUInPlace3]
    simp only [h, ↓reduceDIte]
    exact ih.trans (((R.size_uset ..).trans (R.size_uset ..)).trans (R.size_uset ..))
  | case2 arr hr ht hu j b₁ b₂ b₃ h =>
    rw [foldUInPlace3]
    simp only [h, ↓reduceDIte]

/-- `g j + 2ʷ g (j + 1) + ⋯`, `m` terms: the value of the digits `g j, …, g (j + m - 1)`. -/
@[expose] public def wsum (w : Nat) (g : Nat → Nat) (j : Nat) : Nat → Nat
  | 0 => 0
  | m + 1 => g j + 2 ^ w * wsum w g (j + 1) m

public theorem wsum_succ (w : Nat) (g : Nat → Nat) (j m : Nat) :
    wsum w g j (m + 1) = g j + 2 ^ w * wsum w g (j + 1) m := by
  rw [wsum]

public theorem wsum_zero (w j m : Nat) : wsum w (fun _ => 0) j m = 0 := by
  induction m generalizing j with
  | zero => rfl
  | succ m ih => rw [wsum_succ, ih]; simp

/-- `wsum` is linear in its digits. -/
public theorem wsum_add_mul (w : Nat) (g h : Nat → Nat) (v : Nat) :
    ∀ m j, wsum w (fun i => g i + v * h i) j m = wsum w g j m + v * wsum w h j m
  | 0, _ => by simp [wsum]
  | m + 1, j => by
    rw [wsum_succ, wsum_succ, wsum_succ, wsum_add_mul w g h v m (j + 1)]
    simp only [Nat.mul_add]
    grind

/-- One step of a carry law of a fold over one window with amounts, from the law of the rest. -/
private theorem law3_step {o ea eb q p x V Wa Wb Pp Qp P' Q' X B W : Nat}
    (ih : V + B * P' + Wa + Qp = X + Wb + B * Q' + Pp)
    (hl : o + W * Pp + ea + q = x + eb + W * Qp + p) :
    o + W * V + B * W * P' + (ea + W * Wa) + q = x + W * X + (eb + W * Wb) + B * W * Q' + p := by
  have := congrArg (W * ·) ih
  simp only [Nat.mul_add] at this
  grind

/--
The values of `foldUInPlace3`, for steps with linear carry laws: if every step of `fᵢ` turns a limb
`z` and an accumulator `c` into a limb `out` and an accumulator `c'` with
`out + 2ʷ Pᵢ c' + Eᵢ j + Qᵢ c = z + Gᵢ j + 2ʷ Qᵢ c' + Pᵢ c`, then the windows satisfy the same law
with the sums of the amounts `Eᵢ` and `Gᵢ`, as long as the three windows are disjoint. `Pᵢ` is a
carry and `Qᵢ` a borrow.
-/
public theorem foldUInPlace3_spec {β₁ β₂ β₃ : Type} (n : USize)
    (f₁ : (j : USize) → j < n → L → β₁ → L × β₁)
    (f₂ : (j : USize) → j < n → L → β₂ → L × β₂)
    (f₃ : (j : USize) → j < n → L → β₃ → L × β₃)
    (E₁ E₂ E₃ G₁ G₂ G₃ : Nat → Nat) (P₁ Q₁ : β₁ → Nat) (P₂ Q₂ : β₂ → Nat) (P₃ Q₃ : β₃ → Nat)
    (I₁ : β₁ → Prop) (I₂ : β₂ → Prop) (I₃ : β₃ → Prop)
    (inv₁ : ∀ j h z c, I₁ c → I₁ (f₁ j h z c).2)
    (inv₂ : ∀ j h z c, I₂ c → I₂ (f₂ j h z c).2)
    (inv₃ : ∀ j h z c, I₃ c → I₃ (f₃ j h z c).2)
    (law₁ : ∀ j h z c, I₁ c → LA.val (f₁ j h z c).1 + 2 ^ LA.w * P₁ (f₁ j h z c).2 +
      E₁ j.toNat + Q₁ c = LA.val z + G₁ j.toNat + 2 ^ LA.w * Q₁ (f₁ j h z c).2 + P₁ c)
    (law₂ : ∀ j h z c, I₂ c → LA.val (f₂ j h z c).1 + 2 ^ LA.w * P₂ (f₂ j h z c).2 +
      E₂ j.toNat + Q₂ c = LA.val z + G₂ j.toNat + 2 ^ LA.w * Q₂ (f₂ j h z c).2 + P₂ c)
    (law₃ : ∀ j h z c, I₃ c → LA.val (f₃ j h z c).1 + 2 ^ LA.w * P₃ (f₃ j h z c).2 +
      E₃ j.toNat + Q₃ c = LA.val z + G₃ j.toNat + 2 ^ LA.w * Q₃ (f₃ j h z c).2 + P₃ c)
    (arr : A) (rs ts us : USize) (hr : LoopBound arr rs n) (ht : LoopBound arr ts n)
    (hu : LoopBound arr us n)
    (hrt : rs.toNat + n.toNat ≤ ts.toNat ∨ ts.toNat + n.toNat ≤ rs.toNat)
    (hru : rs.toNat + n.toNat ≤ us.toNat ∨ us.toNat + n.toNat ≤ rs.toNat)
    (htu : ts.toNat + n.toNat ≤ us.toNat ∨ us.toNat + n.toNat ≤ ts.toNat)
    (j : USize) (b₁ : β₁) (b₂ : β₂) (b₃ : β₃) (hb₁ : I₁ b₁) (hb₂ : I₂ b₂) (hb₃ : I₃ b₃) :
    LA.size (foldUInPlace3 n f₁ f₂ f₃ arr rs ts us hr ht hu j b₁ b₂ b₃).1 = LA.size arr ∧
      I₁ (foldUInPlace3 n f₁ f₂ f₃ arr rs ts us hr ht hu j b₁ b₂ b₃).2.1 ∧ I₂ (foldUInPlace3 n f₁ f₂ f₃ arr rs ts us hr ht hu j b₁ b₂ b₃).2.2.1 ∧ I₃ (foldUInPlace3 n f₁ f₂ f₃ arr rs ts us hr ht hu j b₁ b₂ b₃).2.2.2 ∧
      (∀ i, (i < rs.toNat + j.toNat ∨ rs.toNat + n.toNat ≤ i) →
        (i < ts.toNat + j.toNat ∨ ts.toNat + n.toNat ≤ i) →
        (i < us.toNat + j.toNat ∨ us.toNat + n.toNat ≤ i) →
        LA.get (foldUInPlace3 n f₁ f₂ f₃ arr rs ts us hr ht hu j b₁ b₂ b₃).1 i = LA.get arr i) ∧
      LimbArray.valAt (foldUInPlace3 n f₁ f₂ f₃ arr rs ts us hr ht hu j b₁ b₂ b₃).1 (rs.toNat + j.toNat) (n.toNat - j.toNat) +
        2 ^ (LA.w * (n.toNat - j.toNat)) * P₁ (foldUInPlace3 n f₁ f₂ f₃ arr rs ts us hr ht hu j b₁ b₂ b₃).2.1 +
        wsum LA.w E₁ j.toNat (n.toNat - j.toNat) + Q₁ b₁ =
      LimbArray.valAt arr (rs.toNat + j.toNat) (n.toNat - j.toNat) +
        wsum LA.w G₁ j.toNat (n.toNat - j.toNat) +
        2 ^ (LA.w * (n.toNat - j.toNat)) * Q₁ (foldUInPlace3 n f₁ f₂ f₃ arr rs ts us hr ht hu j b₁ b₂ b₃).2.1 + P₁ b₁ ∧
      LimbArray.valAt (foldUInPlace3 n f₁ f₂ f₃ arr rs ts us hr ht hu j b₁ b₂ b₃).1 (ts.toNat + j.toNat) (n.toNat - j.toNat) +
        2 ^ (LA.w * (n.toNat - j.toNat)) * P₂ (foldUInPlace3 n f₁ f₂ f₃ arr rs ts us hr ht hu j b₁ b₂ b₃).2.2.1 +
        wsum LA.w E₂ j.toNat (n.toNat - j.toNat) + Q₂ b₂ =
      LimbArray.valAt arr (ts.toNat + j.toNat) (n.toNat - j.toNat) +
        wsum LA.w G₂ j.toNat (n.toNat - j.toNat) +
        2 ^ (LA.w * (n.toNat - j.toNat)) * Q₂ (foldUInPlace3 n f₁ f₂ f₃ arr rs ts us hr ht hu j b₁ b₂ b₃).2.2.1 + P₂ b₂ ∧
      LimbArray.valAt (foldUInPlace3 n f₁ f₂ f₃ arr rs ts us hr ht hu j b₁ b₂ b₃).1 (us.toNat + j.toNat) (n.toNat - j.toNat) +
        2 ^ (LA.w * (n.toNat - j.toNat)) * P₃ (foldUInPlace3 n f₁ f₂ f₃ arr rs ts us hr ht hu j b₁ b₂ b₃).2.2.2 +
        wsum LA.w E₃ j.toNat (n.toNat - j.toNat) + Q₃ b₃ =
      LimbArray.valAt arr (us.toNat + j.toNat) (n.toNat - j.toNat) +
        wsum LA.w G₃ j.toNat (n.toNat - j.toNat) +
        2 ^ (LA.w * (n.toNat - j.toNat)) * Q₃ (foldUInPlace3 n f₁ f₂ f₃ arr rs ts us hr ht hu j b₁ b₂ b₃).2.2.2 + P₃ b₃ := by
  induction arr, hr, ht, hu, j, b₁, b₂, b₃ using foldUInPlace3.induct (R := R) n f₁ f₂ f₃ rs ts us
    with
  | case1 arr hr ht hu j b₁ b₂ b₃ h x y z p q r a₁ a₂ ih =>
    rw [foldUInPlace3]
    simp only [h, ↓reduceDIte]
    have hj := USize.lt_iff_toNat_lt.1 h
    have hj₁ := USize.toNat_add_one_of_lt h
    have hri := hr.toNat_add h
    have hti := ht.toNat_add h
    have hui := hu.toNat_add h
    obtain ⟨ih₁, ih₀₁, ih₀₂, ih₀₃, ih₂, ih₃, ih₄, ih₅⟩ :=
      ih (inv₁ j h x b₁ hb₁) (inv₂ j h y b₂ hb₂) (inv₃ j h z b₃ hb₃)
    rw [hj₁] at ih₂ ih₃ ih₄ ih₅
    rw [R.size_uset, R.size_uset, R.size_uset] at ih₁
    generalize foldUInPlace3 (A := A) n f₁ f₂ f₃ _ rs ts us _ _ _ (j + 1) p.2 q.2 r.2 = F at *
    have hget : ∀ i, LA.get (R.uset a₂ (us + j) r.1 (((hu.of_uset ..).of_uset ..).uset_bound h)) i =
        if i = us.toNat + j.toNat then r.1 else if i = ts.toNat + j.toNat then q.1 else
          if i = rs.toNat + j.toNat then p.1 else LA.get arr i := by
      intro i
      simp only [a₂, a₁, R.get_uset, hri, hti, hui]
      by_cases e₁ : i = us.toNat + j.toNat
      · simp [e₁]
      · by_cases e₂ : i = ts.toNat + j.toNat
        · simp [e₂, show ¬ us.toNat = ts.toNat by lia, show ¬ ts.toNat = us.toNat by lia]
        · by_cases e₃ : i = rs.toNat + j.toNat
          · simp [e₃, show ¬ us.toNat = rs.toNat by lia, show ¬ rs.toNat = us.toNat by lia,
              show ¬ ts.toNat = rs.toNat by lia, show ¬ rs.toNat = ts.toNat by lia]
          · simp [e₁, e₂, e₃, show ¬ us.toNat + j.toNat = i by lia,
              show ¬ ts.toNat + j.toNat = i by lia, show ¬ rs.toNat + j.toNat = i by lia]
    have hv₁ : LA.get F.1 (rs.toNat + j.toNat) = p.1 := by
      rw [ih₂ _ (.inl (by lia)) (by lia) (by lia), hget]
      simp only [show ¬ rs.toNat + j.toNat = us.toNat + j.toNat by lia,
        show ¬ rs.toNat + j.toNat = ts.toNat + j.toNat by lia, ↓reduceIte]
    have hv₂ : LA.get F.1 (ts.toNat + j.toNat) = q.1 := by
      rw [ih₂ _ (by lia) (.inl (by lia)) (by lia), hget]
      simp only [show ¬ ts.toNat + j.toNat = us.toNat + j.toNat by lia, ↓reduceIte]
    have hv₃ : LA.get F.1 (us.toNat + j.toNat) = r.1 := by
      rw [ih₂ _ (by lia) (by lia) (.inl (by lia)), hget]
      simp only [↓reduceIte]
    have hWr : LimbArray.valAt
        (R.uset a₂ (us + j) r.1 (((hu.of_uset ..).of_uset ..).uset_bound h))
          (rs.toNat + (j.toNat + 1)) (n.toNat - (j.toNat + 1)) =
        LimbArray.valAt arr (rs.toNat + (j.toNat + 1)) (n.toNat - (j.toNat + 1)) :=
      LimbArray.valAt_congr _ fun i _ _ => by
        rw [hget]
        simp only [show ¬ i = us.toNat + j.toNat by lia, show ¬ i = ts.toNat + j.toNat by lia,
          show ¬ i = rs.toNat + j.toNat by lia, ↓reduceIte]
    have hWt : LimbArray.valAt
        (R.uset a₂ (us + j) r.1 (((hu.of_uset ..).of_uset ..).uset_bound h))
          (ts.toNat + (j.toNat + 1)) (n.toNat - (j.toNat + 1)) =
        LimbArray.valAt arr (ts.toNat + (j.toNat + 1)) (n.toNat - (j.toNat + 1)) :=
      LimbArray.valAt_congr _ fun i _ _ => by
        rw [hget]
        simp only [show ¬ i = us.toNat + j.toNat by lia, show ¬ i = ts.toNat + j.toNat by lia,
          show ¬ i = rs.toNat + j.toNat by lia, ↓reduceIte]
    have hWu : LimbArray.valAt
        (R.uset a₂ (us + j) r.1 (((hu.of_uset ..).of_uset ..).uset_bound h))
          (us.toNat + (j.toNat + 1)) (n.toNat - (j.toNat + 1)) =
        LimbArray.valAt arr (us.toNat + (j.toNat + 1)) (n.toNat - (j.toNat + 1)) :=
      LimbArray.valAt_congr _ fun i _ _ => by
        rw [hget]
        simp only [show ¬ i = us.toNat + j.toNat by lia, show ¬ i = ts.toNat + j.toNat by lia,
          show ¬ i = rs.toNat + j.toNat by lia, ↓reduceIte]
    have hx' : x = LA.get arr (rs.toNat + j.toNat) := by simp only [x]; rw [R.uget_eq, hri]
    have hy' : y = LA.get arr (ts.toNat + j.toNat) := by simp only [y]; rw [R.uget_eq, hti]
    have hz' : z = LA.get arr (us.toNat + j.toNat) := by simp only [z]; rw [R.uget_eq, hui]
    rw [hWr] at ih₃
    rw [hWt] at ih₄
    rw [hWu] at ih₅
    obtain ⟨k, hk⟩ : ∃ k, n.toNat - j.toNat = k + 1 := ⟨n.toNat - j.toNat - 1, by lia⟩
    rw [show n.toNat - (j.toNat + 1) = k by lia] at ih₃ ih₄ ih₅
    simp only [← Nat.add_assoc] at ih₃ ih₄ ih₅
    have hl₁ := law₁ j h x b₁ hb₁
    have hl₂ := law₂ j h y b₂ hb₂
    have hl₃ := law₃ j h z b₃ hb₃
    refine ⟨ih₁, ih₀₁, ih₀₂, ih₀₃, fun i hi₁ hi₂ hi₃ => ?_, ?_, ?_, ?_⟩
    · rw [ih₂ i (by lia) (by lia) (by lia), hget]
      simp only [show ¬ i = us.toNat + j.toNat by lia, show ¬ i = ts.toNat + j.toNat by lia,
        show ¬ i = rs.toNat + j.toNat by lia, ↓reduceIte]
    · rw [hk, LimbArray.valAt_succ, LimbArray.valAt_succ, wsum_succ, hv₁, Nat.mul_succ,
        Nat.pow_add, ← hx', wsum_succ]
      exact law3_step ih₃ hl₁
    · rw [hk, LimbArray.valAt_succ, LimbArray.valAt_succ, wsum_succ, hv₂, Nat.mul_succ,
        Nat.pow_add, ← hy', wsum_succ]
      exact law3_step ih₄ hl₂
    · rw [hk, LimbArray.valAt_succ, LimbArray.valAt_succ, wsum_succ, hv₃, Nat.mul_succ,
        Nat.pow_add, ← hz', wsum_succ]
      exact law3_step ih₅ hl₃
  | case2 arr hr ht hu j b₁ b₂ b₃ h =>
    rw [foldUInPlace3]
    have : n.toNat - j.toNat = 0 := by have := USize.lt_iff_toNat_lt (a := j) (b := n); lia
    simp [h, this, wsum, hb₁, hb₂, hb₃, Nat.add_comm]

/-- `foldUInPlace3` followed by `g` on the new array and the last accumulators. -/
@[expose]
public def foldUInPlace3Then {β₁ β₂ β₃ γ : Type} (n : USize)
    (f₁ : (j : USize) → j < n → L → β₁ → L × β₁)
    (f₂ : (j : USize) → j < n → L → β₂ → L × β₂)
    (f₃ : (j : USize) → j < n → L → β₃ → L × β₃)
    (arr : A) (rs ts us : USize) (hr : LoopBound arr rs n) (ht : LoopBound arr ts n)
    (hu : LoopBound arr us n) (j : USize) (b₁ : β₁) (b₂ : β₂) (b₃ : β₃)
    (g : (arr' : A) → LA.size arr' = LA.size arr → β₁ → β₂ → β₃ → γ) : γ :=
  g (foldUInPlace3 n f₁ f₂ f₃ arr rs ts us hr ht hu j b₁ b₂ b₃).1 (size_foldUInPlace3 ..)
    (foldUInPlace3 n f₁ f₂ f₃ arr rs ts us hr ht hu j b₁ b₂ b₃).2.1
    (foldUInPlace3 n f₁ f₂ f₃ arr rs ts us hr ht hu j b₁ b₂ b₃).2.2.1
    (foldUInPlace3 n f₁ f₂ f₃ arr rs ts us hr ht hu j b₁ b₂ b₃).2.2.2

end WordArray

open WordArray in
/--
The in-place folds of lean4-scalar-arrays on arrays of words, over one window and over one window
while reading two others of the same array, which run in place of `foldUInPlaceThen` and
`foldUInPlace2Then`, over one window with an accumulator of two parts kept apart, and over two
windows written while reading two others, with two accumulators.
-/
public class WordFolds (A : Type) (L : outParam Type) [LA : LimbArray A L] [WordArray A L] where
  /-- `foldUInPlace2Then`, compiled. -/
  fold2Then : {β γ : Type} → (n : USize) → ((j : USize) → j < n → L → L → β → L × β) →
    (arr : A) → (rs xs ys : USize) → LoopBound arr rs n → LoopBound arr xs n →
    LoopBound arr ys n → USize → β → ((arr' : A) → LA.size arr' = LA.size arr → β → γ) → γ
  fold2Then_eq : ∀ {β γ : Type} n f arr rs xs ys hr hx hy j b g,
    @fold2Then β γ n f arr rs xs ys hr hx hy j b g =
      foldUInPlace2Then n f arr rs xs ys hr hx hy j b g
  /-- `foldUInPlaceThen`, compiled. -/
  foldThen : {β γ : Type} → (n : USize) → ((j : USize) → j < n → L → β → L × β) → (arr : A) →
    (rs : USize) → LoopBound arr rs n → USize → β →
    ((arr' : A) → LA.size arr' = LA.size arr → β → γ) → γ
  foldThen_eq : ∀ {β γ : Type} n f arr rs hr j b g,
    @foldThen β γ n f arr rs hr j b g = foldUInPlaceThen n f arr rs hr j b g
  /--
  `foldUInPlaceThen` with an accumulator of two parts, compiled so that the parts stay apart, and
  unboxed when they are words.
  -/
  foldThen2 : {β₁ β₂ γ : Type} → (n : USize) →
    ((j : USize) → j < n → L → β₁ → β₂ → L × β₁ × β₂) → (arr : A) → (rs : USize) →
    LoopBound arr rs n → USize → β₁ → β₂ →
    ((arr' : A) → LA.size arr' = LA.size arr → β₁ → β₂ → γ) → γ
  foldThen2_eq : ∀ {β₁ β₂ γ : Type} n f arr rs hr j b₁ b₂ g,
    @foldThen2 β₁ β₂ γ n f arr rs hr j b₁ b₂ g =
      foldUInPlaceThen n (fun j h z c => f j h z c.1 c.2) arr rs hr j (b₁, b₂)
        (fun arr' h c => g arr' h c.1 c.2)
  /--
  `foldUInPlace2x2Then`, compiled: one pass that reads two windows and writes two, with the two
  accumulators kept apart, and unboxed when they are words.
  -/
  fold2x2Then : {β₁ β₂ γ : Type} → (n : USize) → ((j : USize) → j < n → L → L → β₁ → L × β₁) →
    ((j : USize) → j < n → L → L → β₂ → L × β₂) → (arr : A) → (rs ts xs ys : USize) →
    LoopBound arr rs n → LoopBound arr ts n → LoopBound arr xs n → LoopBound arr ys n → USize →
    β₁ → β₂ → ((arr' : A) → LA.size arr' = LA.size arr → β₁ → β₂ → γ) → γ
  fold2x2Then_eq : ∀ {β₁ β₂ γ : Type} n f₁ f₂ arr rs ts xs ys hr ht hx hy j b₁ b₂ g,
    @fold2x2Then β₁ β₂ γ n f₁ f₂ arr rs ts xs ys hr ht hx hy j b₁ b₂ g =
      foldUInPlace2x2Then n f₁ f₂ arr rs ts xs ys hr ht hx hy j b₁ b₂ g
  /--
  `foldUInPlace3Then`, compiled: one pass that updates three windows, with the three accumulators
  kept apart, and unboxed when they are words.
  -/
  fold3Then : {β₁ β₂ β₃ γ : Type} → (n : USize) → ((j : USize) → j < n → L → β₁ → L × β₁) →
    ((j : USize) → j < n → L → β₂ → L × β₂) → ((j : USize) → j < n → L → β₃ → L × β₃) →
    (arr : A) → (rs ts us : USize) → LoopBound arr rs n → LoopBound arr ts n →
    LoopBound arr us n → USize → β₁ → β₂ → β₃ →
    ((arr' : A) → LA.size arr' = LA.size arr → β₁ → β₂ → β₃ → γ) → γ
  fold3Then_eq : ∀ {β₁ β₂ β₃ γ : Type} n f₁ f₂ f₃ arr rs ts us hr ht hu j b₁ b₂ b₃ g,
    @fold3Then β₁ β₂ β₃ γ n f₁ f₂ f₃ arr rs ts us hr ht hu j b₁ b₂ b₃ g =
      foldUInPlace3Then n f₁ f₂ f₃ arr rs ts us hr ht hu j b₁ b₂ b₃ g

namespace WordArray

variable {A L : Type} [LA : LimbArray A L] [R : WordArray A L] [F : WordFolds A L]

/--
`fold2Then` as an intermediate result: the array and the accumulator of `foldUInPlace2`, and the
size proof that `g` receives, as variables. Proofs about a chain of loops go through this, so
that the later loops mention variables, not the earlier loops.
-/
public theorem fold2Then_cases {β γ : Type} {n : USize}
    {f : (j : USize) → j < n → L → L → β → L × β} {arr : A}
    {rs xs ys : USize} {hr : LoopBound arr rs n} {hx : LoopBound arr xs n}
    {hy : LoopBound arr ys n} {j : USize} {b : β}
    {g : (arr' : A) → LA.size arr' = LA.size arr → β → γ} {G : γ}
    (h : F.fold2Then n f arr rs xs ys hr hx hy j b g = G) :
    ∃ a, ∃ ha : LA.size a = LA.size arr, ∃ c,
      foldUInPlace2 n f arr rs xs ys hr hx hy j b = (a, c) ∧ g a ha c = G := by
  rw [F.fold2Then_eq, foldUInPlace2Then] at h
  exact ⟨_, _, _, rfl, h⟩

/-- `foldThen` as an intermediate result, like `fold2Then_cases`. -/
public theorem foldThen_cases {β γ : Type} {n : USize} {f : (j : USize) → j < n → L → β → L × β}
    {arr : A} {rs : USize} {hr : LoopBound arr rs n} {j : USize} {b : β}
    {g : (arr' : A) → LA.size arr' = LA.size arr → β → γ} {G : γ}
    (h : F.foldThen n f arr rs hr j b g = G) :
    ∃ a, ∃ ha : LA.size a = LA.size arr, ∃ c,
      foldUInPlace n f arr rs hr j b = (a, c) ∧ g a ha c = G := by
  rw [F.foldThen_eq, foldUInPlaceThen] at h
  exact ⟨_, _, _, rfl, h⟩

/-- `foldThen2` as an intermediate result, like `foldThen_cases`. -/
public theorem foldThen2_cases {β₁ β₂ γ : Type} {n : USize}
    {f : (j : USize) → j < n → L → β₁ → β₂ → L × β₁ × β₂} {arr : A} {rs : USize}
    {hr : LoopBound arr rs n} {j : USize} {b₁ : β₁} {b₂ : β₂}
    {g : (arr' : A) → LA.size arr' = LA.size arr → β₁ → β₂ → γ} {G : γ}
    (h : F.foldThen2 n f arr rs hr j b₁ b₂ g = G) :
    ∃ a, ∃ ha : LA.size a = LA.size arr, ∃ c₁ c₂,
      foldUInPlace n (fun j h z c => f j h z c.1 c.2) arr rs hr j (b₁, b₂) = (a, c₁, c₂) ∧
        g a ha c₁ c₂ = G := by
  rw [F.foldThen2_eq, foldUInPlaceThen] at h
  exact ⟨_, _, _, _, rfl, h⟩

public theorem foldThen_eq' {β γ : Type} (n : USize) (f : (j : USize) → j < n → L → β → L × β)
    (arr : A) (rs : USize) (hr : LoopBound arr rs n) (j : USize) (b : β)
    (g : (arr' : A) → LA.size arr' = LA.size arr → β → γ) :
    F.foldThen n f arr rs hr j b g =
      g (foldUInPlace n f arr rs hr j b).1 (size_foldUInPlace ..) (foldUInPlace n f arr rs hr j b).2 := by
  rw [F.foldThen_eq, foldUInPlaceThen]

public theorem fold2Then_eq' {β γ : Type} (n : USize)
    (f : (j : USize) → j < n → L → L → β → L × β) (arr : A)
    (rs xs ys : USize) (hr : LoopBound arr rs n) (hx : LoopBound arr xs n)
    (hy : LoopBound arr ys n) (j : USize) (b : β)
    (g : (arr' : A) → LA.size arr' = LA.size arr → β → γ) :
    F.fold2Then n f arr rs xs ys hr hx hy j b g =
      g (foldUInPlace2 n f arr rs xs ys hr hx hy j b).1 (size_foldUInPlace2 ..)
        (foldUInPlace2 n f arr rs xs ys hr hx hy j b).2 := by
  rw [F.fold2Then_eq, foldUInPlace2Then]

end WordArray

end MPN
