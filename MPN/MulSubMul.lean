/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import MPN.Basic
public import MPN.UInt

/-!
# A difference of two multiples

`mulSubMul x y a b` computes `a x - b y` for words `a, b < 2³¹` in one pass over the limbs of `x`
and `y`, and tells whether it is negative. Lehmer's `gcd` applies its cofactors to the two numbers
this way, where two products by a word and a subtraction took three passes and three arrays.

The value of a limb, `x a - y b` plus the carry, lies in `(-2⁶³, 2⁶³)`. The loop adds `2⁶³ - 2³¹`
to make it a word, whose low half is the limb and whose high half is the next carry plus `2³¹`,
and carries that word, as `subMulBiased` does: each step is a sum and a difference of natural
numbers, and the chain from one carry to the next is an addition and a shift.
-/

open ScalarArray

namespace MPN

/-! ## The step -/

/--
`v + x a - y b + (h - 2³¹)`, with `h` the carry in plus `2³¹`, as its low word and the carry out
plus `2³¹`, for `a, b < 2³¹`.
-/
@[inline, expose] public def mulSubMulStep (v x y a b h : UInt32) : UInt32 × UInt32 :=
  let t := v.toUInt64 + x.toUInt64 * a.toUInt64 + h.toUInt64 + 0x7FFFFFFF80000000 -
    y.toUInt64 * b.toUInt64
  (t.toUInt32, (t >>> 32).toUInt32)

public theorem mulSubMulStep_spec (v x y a b h : UInt32) (ha : a.toNat < 2 ^ 31)
    (hb : b.toNat < 2 ^ 31) :
    (mulSubMulStep v x y a b h).1.toNat + 2 ^ 32 * (mulSubMulStep v x y a b h).2.toNat +
        y.toNat * b.toNat = v.toNat + x.toNat * a.toNat + h.toNat + (2 ^ 63 - 2 ^ 31) := by
  have := v.toNat_lt
  have := x.toNat_lt
  have := y.toNat_lt
  have := h.toNat_lt
  have hxa : x.toNat * a.toNat ≤ (2 ^ 32 - 1) * (2 ^ 31 - 1) := Nat.mul_le_mul (by omega) (by omega)
  have hyb : y.toNat * b.toNat ≤ (2 ^ 32 - 1) * (2 ^ 31 - 1) := Nat.mul_le_mul (by omega) (by omega)
  simp only [mulSubMulStep, UInt64.toNat_sub, UInt64.toNat_add, UInt64.toNat_mul,
    UInt64.toNat_toUInt32, UInt32.toNat_toUInt64, UInt64.toNat_shiftRight,
    Nat.shiftRight_eq_div_pow, UInt64.toNat_ofNat, Nat.reduceMod, Nat.reducePow] at *
  generalize x.toNat * a.toNat = p at *
  generalize y.toNat * b.toNat = q at *
  rw [Nat.mod_eq_of_lt (show p < 18446744073709551616 by omega),
    Nat.mod_eq_of_lt (show q < 18446744073709551616 by omega)]
  omega

/-! ## The loop -/

/--
Adds `x[j...] a - y[j...] b` and the carry `h - 2³¹` to `r` from limb `j` up to limb `m`, with
`x` and `y` read as `0` past their ends, and returns the carry out plus `2³¹`.
-/
def mulSubMulLoop (r x y : UInt32Array) (a b : UInt32) (m j : Nat) (h : UInt32) :
    UInt32Array × UInt32 :=
  if hj : j < m ∧ j < r.size then
    let p := mulSubMulStep r[j] (x.getD j 0) (y.getD j 0) a b h
    mulSubMulLoop (r.set j p.1 hj.2) x y a b m (j + 1) p.2
  else
    (r, h)
termination_by m - j

private theorem mulSubMulLoop_spec (r x y : UInt32Array) (a b : UInt32) (m j : Nat) (h : UInt32)
    (ha : a.toNat < 2 ^ 31) (hb : b.toNat < 2 ^ 31) (hm : m ≤ r.size) (hx : x.size ≤ m)
    (hy : y.size ≤ m) (hj : j ≤ m) :
    (mulSubMulLoop r x y a b m j h).1.size = r.size ∧
      (mulSubMulLoop r x y a b m j h).1.toList.drop m = r.toList.drop m ∧
      ofLimbs (mulSubMulLoop r x y a b m j h).1.toList +
          2 ^ (32 * m) * (mulSubMulLoop r x y a b m j h).2.toNat +
          2 ^ (32 * j) * (ofLimbs (y.toList.drop j) * b.toNat + 2 ^ 31) =
        ofLimbs r.toList + 2 ^ (32 * j) * (ofLimbs (x.toList.drop j) * a.toNat + h.toNat) +
          2 ^ 31 * 2 ^ (32 * m) := by
  induction r, j, h using mulSubMulLoop.induct x y a b m with
  | case1 r j h hj' p ih =>
    rw [mulSubMulLoop]
    simp only [hj', and_self, ↓reduceDIte]
    have hs := mulSubMulStep_spec r[j] (x.getD j 0) (y.getD j 0) a b h ha hb
    obtain ⟨ih₁, ih₂, ih₃⟩ := ih (by simpa using hm) (by omega)
    simp only [UInt32Array.size_set] at ih₁ ih₂ ih₃
    refine ⟨ih₁, ?_, ?_⟩
    · rw [ih₂, UInt32Array.toList_set, List.drop_set]
      simp only [show j < m by omega, ↓reduceIte]
    have hk : j < r.toList.length := by simp; omega
    have hset := ofLimbs_set r.toList j p.1 hk
    simp only [UInt32Array.getElem_toList] at hset
    have hX := ofLimbs_drop x.toList j
    have hY := ofLimbs_drop y.toList j
    have hxj : x.toList.getD j 0 = x.getD j 0 := by simp [List.getD_eq_getElem?_getD]
    have hyj : y.toList.getD j 0 = y.getD j 0 := by simp [List.getD_eq_getElem?_getD]
    rw [hxj] at hX
    rw [hyj] at hY
    rw [UInt32Array.toList_set] at ih₃
    rw [Nat.mul_add 32 j 1, Nat.mul_one, Nat.pow_add] at ih₃
    generalize ofLimbs (r.toList.set j p.1) = R₁ at *
    generalize ofLimbs r.toList = R at *
    generalize ofLimbs (x.toList.drop j) = X at *
    generalize ofLimbs (y.toList.drop j) = Y at *
    generalize ofLimbs (x.toList.drop (j + 1)) = X' at *
    generalize ofLimbs (y.toList.drop (j + 1)) = Y' at *
    generalize ofLimbs (mulSubMulLoop (r.set j p.1 hj'.2) x y a b m (j + 1) p.2).1.toList =
      R₂ at *
    generalize (mulSubMulLoop (r.set j p.1 hj'.2) x y a b m (j + 1) p.2).2.toNat = C₂ at *
    generalize 2 ^ (32 * j) = P at *
    generalize 2 ^ (32 * m) = Q at *
    simp only [p] at *
    generalize (mulSubMulStep r[j] (x.getD j 0) (y.getD j 0) a b h).1.toNat = lo at *
    generalize (mulSubMulStep r[j] (x.getD j 0) (y.getD j 0) a b h).2.toNat = hi at *
    generalize r[j].toNat = v at *
    generalize (x.getD j 0).toNat = xj at *
    generalize (y.getD j 0).toNat = yj at *
    generalize a.toNat = A at *
    generalize b.toNat = B at *
    generalize h.toNat = c at *
    subst hX hY
    grind
  | case2 r j h hj' =>
    rw [mulSubMulLoop]
    simp only [hj', ↓reduceDIte]
    have hjm : j = m := by omega
    subst hjm
    have hy' : y.toList.drop j = [] := List.drop_of_length_le (by simp; omega)
    have hx' : x.toList.drop j = [] := List.drop_of_length_le (by simp; omega)
    simp only [hy', hx', ofLimbs_nil, Nat.zero_mul, Nat.zero_add]
    refine ⟨by simp, by simp, ?_⟩
    rw [Nat.mul_comm (2 ^ 31) (2 ^ (32 * j))]

/-! ## The compiled loop

`mulSubMulFast` runs the loop as a `foldInPlaceThen` over the result, reading `x` and `y` with
`uget`, as `0` past their ends. `@[csimp]` makes the compiler use it in place of `mulSubMul`.
-/

/-- A limb of `w`, or `0` past its end. -/
@[inline] def limbOrZero (w : UInt32Array) (nw : USize) (hnw : nw.toNat = w.size) (k : USize) :
    UInt32 :=
  if h : k < nw then w.uget k (by rw [← hnw]; exact USize.lt_iff_toNat_lt.1 h) else 0

private theorem limbOrZero_eq (w : UInt32Array) (nw : USize) (hnw : nw.toNat = w.size) (k : USize)
    (j : Nat) (hj : k.toNat = j) : limbOrZero w nw hnw k = w.getD j 0 := by
  unfold limbOrZero
  by_cases h : j < w.size
  · have h' : k < nw := USize.lt_iff_toNat_lt.2 (by omega)
    simp [h', h, hj, UInt32Array.getD_eq_getD_getElem?]
  · have h' : ¬ k < nw := fun h' => h (by have := USize.lt_iff_toNat_lt.1 h'; omega)
    simp [h', h, UInt32Array.getD_eq_getD_getElem?]

/-- The step of the fold of `mulSubMulFast`. -/
@[inline] def mulSubMulStepU (x y : UInt32Array) (nx ny : USize) (hnx : nx.toNat = x.size)
    (hny : ny.toNat = y.size) (a b : UInt32) (len : USize) (k : USize) (_ : k.toNat < len.toNat)
    (v h : UInt32) : UInt32 × UInt32 :=
  mulSubMulStep v (limbOrZero x nx hnx k) (limbOrZero y ny hny k) a b h

/-- The fold of `mulSubMulFast` from limb `j` on is `mulSubMulLoop` from limb `j` on. -/
private theorem foldInPlace_loop_mulSubMul (r x y : UInt32Array) (nx ny : USize)
    (hnx : nx.toNat = x.size) (hny : ny.toNat = y.size) (a b : UInt32) (len : USize) (m : Nat)
    (hlen' : len.toNat = m) (hm : m ≤ r.size) (s n : Nat) (hs : s = 0) (hn : n = m) (j : Nat)
    (h : UInt32) (h' hlen) :
    UInt32Array.foldInPlace.loop len (mulSubMulStepU x y nx ny hnx hny a b len) s n r h' hlen j h =
      mulSubMulLoop r x y a b m j h := by
  subst s n
  induction r, j, h using mulSubMulLoop.induct x y a b m with
  | case1 r j h hj' p ih =>
    rw [UInt32Array.foldInPlace.loop]
    conv => rhs; rw [mulSubMulLoop]
    simp only [hj', and_self, ↓reduceDIte, Nat.zero_add]
    have hjU : j.toUSize.toNat = j := toNat_toUSize (by have := len.toNat_lt_size; omega)
    simp only [mulSubMulStepU, limbOrZero_eq x nx hnx _ j hjU, limbOrZero_eq y ny hny _ j hjU]
    exact ih (by simpa using hm) _
  | case2 r j h hj' =>
    rw [UInt32Array.foldInPlace.loop, mulSubMulLoop]
    have : ¬ j < m := by omega
    simp [this]

/-! ## The difference -/

/--
`a x - b y` for `a, b < 2³¹`, as `max x.size y.size + 1` limbs, untrimmed, and whether it is
negative, in which case the limbs mean nothing.
-/
public def mulSubMul (x y : UInt32Array) (a b : UInt32) : UInt32Array × Bool :=
  let m := max x.size y.size
  let p := mulSubMulLoop (.replicate (m + 1) 0) x y a b m 0 0x80000000
  (p.1.set! m (p.2 - 0x80000000), decide (p.2 < 0x80000000))

public theorem mulSubMul_spec (x y : UInt32Array) (a b : UInt32) (ha : a.toNat < 2 ^ 31)
    (hb : b.toNat < 2 ^ 31) :
    ((mulSubMul x y a b).2 = false →
        toNat (mulSubMul x y a b).1 + toNat y * b.toNat = toNat x * a.toNat) ∧
      ((mulSubMul x y a b).2 = true → toNat x * a.toNat < toNat y * b.toNat) := by
  have hrs : (UInt32Array.replicate (max x.size y.size + 1) 0).size = max x.size y.size + 1 := by
    simp
  obtain ⟨h₁, h₂, h₃⟩ := mulSubMulLoop_spec (.replicate (max x.size y.size + 1) 0) x y a b
    (max x.size y.size) 0 0x80000000 ha hb (by omega) (by omega) (by omega) (by omega)
  simp only [mulSubMul, toNat_toSlice]
  generalize hp : mulSubMulLoop (.replicate (max x.size y.size + 1) 0) x y a b
    (max x.size y.size) 0 0x80000000 = p at h₁ h₂ h₃
  generalize max x.size y.size = m at *
  simp only [Nat.mul_zero, Nat.pow_zero, Nat.one_mul, List.drop_zero, UInt32.reduceToNat,
    UInt32Array.toList_replicate, ofLimbs_replicate_zero, Nat.zero_add] at h₃
  -- The top limb of `p.1` is still zero, so the limbs below it are below `βᵐ`.
  have hsplit := ofLimbs_append (p.1.toList.take m) (p.1.toList.drop m)
  rw [List.take_append_drop, h₂, UInt32Array.toList_replicate, List.drop_replicate,
    show m + 1 - m = 1 by omega, List.length_take, UInt32Array.length_toList, h₁, hrs,
    Nat.min_eq_left (by omega)] at hsplit
  simp only [List.replicate_one, ofLimbs_cons, ofLimbs_nil, UInt32.toNat_zero, Nat.mul_zero,
    Nat.add_zero] at hsplit
  have hlo := ofLimbs_take_lt p.1.toList m
  rw [hsplit] at h₃
  -- Writing `h - 2³¹` into the top limb, which is zero.
  have hk : m < p.1.toList.length := by simp [h₁, hrs]
  have hold : p.1.toList[m] = 0 := by
    have := congrArg (·[0]?) h₂
    simp only [List.getElem?_drop, Nat.add_zero, UInt32Array.toList_replicate] at this
    rw [List.getElem?_replicate, ite_eq_left (by omega), List.getElem?_eq_getElem hk] at this
    exact Option.some.inj this
  have hset := ofLimbs_set p.1.toList m (p.2 - 0x80000000) hk
  rw [hold, UInt32.toNat_zero, Nat.mul_zero, Nat.add_zero, hsplit] at hset
  rw [UInt32Array.toList_set!]
  rw [Nat.mul_comm (ofLimbs y.toList), Nat.mul_comm (ofLimbs x.toList)] at *
  generalize ofLimbs (p.1.toList.set m (p.2 - 0x80000000)) = V at *
  generalize ofLimbs (p.1.toList.take m) = L at *
  generalize 2 ^ (32 * m) = Q at *
  refine ⟨fun hn => ?_, fun hn => ?_⟩
  · have hge : 2 ^ 31 ≤ p.2.toNat := by
      simp only [decide_eq_false_iff_not, UInt32.lt_iff_toNat_lt, UInt32.reduceToNat] at hn
      omega
    have hsub : (p.2 - 0x80000000).toNat = p.2.toNat - 2 ^ 31 := by
      rw [UInt32.toNat_sub_of_le _ _ (by rw [UInt32.le_iff_toNat_le]; simpa using hge)]
      rfl
    rw [hsub] at hset
    have : Q * (p.2.toNat - 2 ^ 31) + Q * 2 ^ 31 = Q * p.2.toNat := by
      rw [← Nat.mul_add, Nat.sub_add_cancel hge]
    omega
  · have hlt : p.2.toNat + 1 ≤ 2 ^ 31 := by
      simp only [decide_eq_true_eq, UInt32.lt_iff_toNat_lt, UInt32.reduceToNat] at hn
      omega
    have := Nat.mul_le_mul_left Q hlt
    rw [Nat.mul_add, Nat.mul_one] at this
    omega

/-- `mulSubMul` with `foldInPlaceThen`, which the compiler uses in its place. -/
public def mulSubMulFast (x y : UInt32Array) (a b : UInt32) : UInt32Array × Bool :=
  if hs : max x.size y.size + 1 < 4294967295 then
    let m := max x.size y.size
    (UInt32Array.replicate (m + 1) 0).foldInPlaceThen 0 m.toUSize 0x80000000
      (mulSubMulStepU x y x.size.toUSize y.size.toUSize (toNat_toUSize (lt_usizeSize (by omega)))
        (toNat_toUSize (lt_usizeSize (by omega))) a b m.toUSize)
      (fun r h => (r.set! m (h - 0x80000000), decide (h < 0x80000000)))
      (by
        rw [toNat_toUSize (lt_usizeSize (by omega)), UInt32Array.size_replicate]
        simp)
  else
    let m := max x.size y.size
    let p := mulSubMulLoop (.replicate (m + 1) 0) x y a b m 0 0x80000000
    (p.1.set! m (p.2 - 0x80000000), decide (p.2 < 0x80000000))

@[csimp] public theorem mulSubMul_eq_mulSubMulFast : @mulSubMul = @mulSubMulFast := by
  funext x y a b
  rw [mulSubMulFast]
  split
  · rename_i hs
    rw [UInt32Array.foldInPlaceThen_eq, UInt32Array.foldInPlace,
      foldInPlace_loop_mulSubMul _ x y _ _ _ _ a b _ (max x.size y.size)
        (toNat_toUSize (lt_usizeSize (by omega))) (by simp) _ _ (by simp)
        (toNat_toUSize (lt_usizeSize (by omega))) 0 0x80000000]
    rfl
  · rfl

/-! ## Both differences of a Lehmer step

Lehmer's `gcd` needs `a x - b y` and `d y - c x` from the same `x` and `y`. `mulSubMul₂` computes
both in one pass, which reads each limb of `x` and `y` once and keeps the two carries apart; it is
the pair of the two `mulSubMul`s, so their specification applies. A fold runs over one array, so
the compiled loop is a tail-recursive function over both.
-/

/-- `mulSubMulLoop` on `r` with `x`, `y`, `a`, `b` and on `s` with `y`, `x`, `d`, `c` at once. -/
def mulSubMul₂Loop (r s x y : UInt32Array) (a b c d : UInt32) (m j : Nat) (hr hs : UInt32) :
    (UInt32Array × UInt32) × (UInt32Array × UInt32) :=
  if hj : j < m ∧ j < r.size ∧ j < s.size then
    let p := mulSubMulStep r[j] (x.getD j 0) (y.getD j 0) a b hr
    let q := mulSubMulStep s[j] (y.getD j 0) (x.getD j 0) d c hs
    mulSubMul₂Loop (r.set j p.1 hj.2.1) (s.set j q.1 hj.2.2) x y a b c d m (j + 1) p.2 q.2
  else
    ((r, hr), (s, hs))
termination_by m - j

private theorem mulSubMul₂Loop_eq (r s x y : UInt32Array) (a b c d : UInt32) (m j : Nat)
    (hr hs : UInt32) (hrs : r.size = s.size) :
    mulSubMul₂Loop r s x y a b c d m j hr hs =
      (mulSubMulLoop r x y a b m j hr, mulSubMulLoop s y x d c m j hs) := by
  induction r, s, j, hr, hs using mulSubMul₂Loop.induct x y a b c d m with
  | case1 r s j hr hs hj p q ih =>
    rw [mulSubMul₂Loop, mulSubMulLoop, mulSubMulLoop]
    simp only [hj, and_self, ↓reduceDIte]
    exact ih (by simp [hrs])
  | case2 r s j hr hs hj =>
    rw [mulSubMul₂Loop, mulSubMulLoop, mulSubMulLoop]
    have h₁ : ¬ (j < m ∧ j < r.size) := fun h => hj ⟨h.1, h.2, hrs ▸ h.2⟩
    have h₂ : ¬ (j < m ∧ j < s.size) := fun h => hj ⟨h.1, hrs ▸ h.2, h.2⟩
    simp only [hj, h₁, h₂, ↓reduceDIte]

/--
`(mulSubMul x y a b, mulSubMul y x d c)`, `a x - b y` and `d y - c x` with their signs, in one
pass, for words below `2³¹`.
-/
public def mulSubMul₂ (x y : UInt32Array) (a b c d : UInt32) :
    (UInt32Array × Bool) × (UInt32Array × Bool) :=
  let m := max x.size y.size
  let p := mulSubMul₂Loop (.replicate (m + 1) 0) (.replicate (m + 1) 0) x y a b c d m 0
    0x80000000 0x80000000
  ((p.1.1.set! m (p.1.2 - 0x80000000), decide (p.1.2 < 0x80000000)),
    (p.2.1.set! m (p.2.2 - 0x80000000), decide (p.2.2 < 0x80000000)))

public theorem mulSubMul₂_eq (x y : UInt32Array) (a b c d : UInt32) :
    mulSubMul₂ x y a b c d = (mulSubMul x y a b, mulSubMul y x d c) := by
  simp only [mulSubMul₂, mulSubMul, Nat.max_comm y.size x.size]
  rw [mulSubMul₂Loop_eq _ _ _ _ _ _ _ _ _ _ _ _ rfl]

/-- The compiled loop of `mulSubMul₂Fast`, which finishes both differences at the end. -/
def mulSubMul₂LoopU (x y : UInt32Array) (nx ny : USize) (hnx : nx.toNat = x.size)
    (hny : ny.toNat = y.size) (a b c d : UInt32) (m : USize) (r s : UInt32Array)
    (hr : m.toNat ≤ r.size) (hs : m.toNat ≤ s.size) (k : USize) (cr cs : UInt32) :
    (UInt32Array × Bool) × (UInt32Array × Bool) :=
  if h : k < m then
    have hk : k.toNat < m.toNat := USize.lt_iff_toNat_lt.1 h
    let xk := limbOrZero x nx hnx k
    let yk := limbOrZero y ny hny k
    let p := mulSubMulStep (r.uget k (by lia)) xk yk a b cr
    let q := mulSubMulStep (s.uget k (by lia)) yk xk d c cs
    mulSubMul₂LoopU x y nx ny hnx hny a b c d m (r.uset k p.1 (by lia)) (s.uset k q.1 (by lia))
      (by simp only [UInt32Array.size_uset]; lia) (by simp only [UInt32Array.size_uset]; lia)
      (k + 1) p.2 q.2
  else
    ((r.set! m.toNat (cr - 0x80000000), decide (cr < 0x80000000)),
      (s.set! m.toNat (cs - 0x80000000), decide (cs < 0x80000000)))
termination_by m.toNat - k.toNat
decreasing_by
  have : k.toNat < m.toNat := USize.lt_iff_toNat_lt.1 h
  rw [toNat_add_usize (by have := m.toNat_lt_size; simp; lia)]
  simp
  lia

private theorem mulSubMul₂LoopU_eq (x y : UInt32Array) (nx ny : USize) (hnx : nx.toNat = x.size)
    (hny : ny.toNat = y.size) (a b c d : UInt32) (m : USize) (r s : UInt32Array)
    (hr : m.toNat ≤ r.size) (hs : m.toNat ≤ s.size) (k : USize) (j : Nat) (hkj : k.toNat = j)
    (cr cs : UInt32) :
    mulSubMul₂LoopU x y nx ny hnx hny a b c d m r s hr hs k cr cs =
      let p := mulSubMul₂Loop r s x y a b c d m.toNat j cr cs
      ((p.1.1.set! m.toNat (p.1.2 - 0x80000000), decide (p.1.2 < 0x80000000)),
        (p.2.1.set! m.toNat (p.2.2 - 0x80000000), decide (p.2.2 < 0x80000000))) := by
  induction r, s, j, cr, cs using mulSubMul₂Loop.induct x y a b c d m.toNat generalizing k with
  | case1 r s j cr cs hj p q ih =>
    rw [mulSubMul₂LoopU, mulSubMul₂Loop]
    have h : k < m := USize.lt_iff_toNat_lt.2 (by lia)
    simp only [h, hj, and_self, ↓reduceDIte]
    simp only [limbOrZero_eq x nx hnx k j hkj, limbOrZero_eq y ny hny k j hkj,
      uget_eq_getElem r k j hkj, uget_eq_getElem s k j hkj]
    simp only [uset_eq_set _ k j hkj]
    exact ih _ _ _ (by rw [toNat_add_usize (by have := m.toNat_lt_size; simp; lia)]; simp; lia)
  | case2 r s j cr cs hj =>
    rw [mulSubMul₂LoopU, mulSubMul₂Loop]
    have h : ¬ k < m := fun h => hj ⟨by have := USize.lt_iff_toNat_lt.1 h; lia, by
      have := USize.lt_iff_toNat_lt.1 h; lia, by have := USize.lt_iff_toNat_lt.1 h; lia⟩
    simp only [h, hj, ↓reduceDIte]

/--
`mulSubMul₂` with `mulSubMul₂LoopU`, which the compiler uses in its place. Below 32 limbs it runs
the two folds of `mulSubMul` instead: the loop checks that both arrays are unshared at each step and
allocates one more pair, which costs more than the second pass saves on short numbers (`gcd` 4–6%
slower from 4 to 16 limbs).
-/
@[inline] public def mulSubMul₂Fast (x y : UInt32Array) (a b c d : UInt32) :
    (UInt32Array × Bool) × (UInt32Array × Bool) :=
  if max x.size y.size < 32 then
    (mulSubMul x y a b, mulSubMul y x d c)
  else if hs : max x.size y.size + 1 < 4294967295 then
    let m := max x.size y.size
    mulSubMul₂LoopU x y x.size.toUSize y.size.toUSize (toNat_toUSize (lt_usizeSize (by lia)))
      (toNat_toUSize (lt_usizeSize (by lia))) a b c d m.toUSize (.replicate (m + 1) 0)
      (.replicate (m + 1) 0) (by rw [toNat_toUSize (lt_usizeSize (by lia))]; simp)
      (by rw [toNat_toUSize (lt_usizeSize (by lia))]; simp) 0 0x80000000 0x80000000
  else
    mulSubMul₂ x y a b c d

@[csimp] public theorem mulSubMul₂_eq_mulSubMul₂Fast : @mulSubMul₂ = @mulSubMul₂Fast := by
  funext x y a b c d
  rw [mulSubMul₂Fast]
  split
  · exact mulSubMul₂_eq x y a b c d
  split
  · rename_i hs
    rw [mulSubMul₂LoopU_eq _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ 0 rfl,
      toNat_toUSize (lt_usizeSize (by lia))]
    rfl
  · rfl

end MPN
