/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import MPN.UIntArray

/-!
# Schoolbook multiplication

Like GMP's `mpn` functions, these write their result into the limbs of `r` from limb `off` on,
in place when `r` is not shared:

* `mul1 r off a x c` writes the low limbs of `a * x + c` and returns the high limb, like
  `mpn_mul_1`;
* `addMul1 r off a x c` adds `a * x + c` to the limbs of `r` and returns the carry out, like
  `mpn_addmul_1`;
* `mulBasecase r off a b` writes the `a.size + b.size` limbs of `a * b`, for `0 < b.size`, like
  `mpn_mul_basecase`.
-/

open ScalarArray

namespace MPN

/-! ## Multiplication by a limb -/

/-- One limb of `mul1`: the low word of `y * x + c` and the high word. -/
private theorem mul1_step (y x c : UInt64) :
    (y * x + c).toNat + 2 ^ 64 * (UInt64.addh (y.mulh x) (y * x) c).toNat =
      y.toNat * x.toNat + c.toNat := by
  have : y.toNat * x.toNat ≤ (2 ^ 64 - 1) * (2 ^ 64 - 1) :=
    Nat.mul_le_mul (by have := y.toNat_lt; lia) (by have := x.toNat_lt; lia)
  have := c.toNat_lt
  simp only [UInt64.toNat_addh, UInt64.toNat_mulh, UInt64.toNat_add, UInt64.toNat_mul]
  generalize y.toNat * x.toNat = p at *
  generalize c.toNat = c at *
  lia

/--
Writes limbs `j` to `a.size - 1` of `a * x`, plus the carry `c`, into `r` from limb `off + j` on.
-/
def mul1Loop (r : UInt64Array) (off : Nat) (a : UInt64Array.Slice) (x : UInt64) (j : Nat)
    (c : UInt64) : UInt64Array × UInt64 :=
  if h : j < a.size then
    let y := a[j]
    let p := y * x
    mul1Loop (r.set! (off + j) (p + c)) off a x (j + 1) (UInt64.addh (y.mulh x) p c)
  else
    (r, c)

/--
Writes the low limbs of `a * x + c` into `r` from limb `off` on and returns the high limb, like
GMP's `mpn_mul_1`.
-/
public def mul1 (r : UInt64Array) (off : Nat) (a : UInt64Array.Slice) (x : UInt64)
    (c : UInt64 := 0) : UInt64Array × UInt64 :=
  mul1Loop r off a x 0 c

private theorem mul1Loop_spec (r : UInt64Array) (off : Nat) (a : UInt64Array.Slice) (x : UInt64)
    (j : Nat) (c : UInt64) (hr : off + a.size ≤ r.size) :
    (mul1Loop r off a x j c).1.size = r.size ∧
      (∀ i, (i < off + j ∨ off + a.size ≤ i) → (mul1Loop r off a x j c).1[i]! = r[i]!) ∧
      (mul1Loop r off a x j c).1.valAt (off + j) (a.size - j) +
          2 ^ (64 * (a.size - j)) * (mul1Loop r off a x j c).2.toNat =
        a.array.valAt (a.start + j) (a.size - j) * x.toNat + c.toNat := by
  induction r, j, c using mul1Loop.induct off a x with
  | case1 r j c h y p ih =>
    rw [mul1Loop]
    simp only [h, ↓reduceDIte]
    obtain ⟨ih₁, ih₂, ih₃⟩ := ih (by simpa using hr)
    simp only [UInt64Array.size_set!] at ih₁
    have hv : (mul1Loop (r.set! (off + j) (p + c)) off a x (j + 1)
        (UInt64.addh (y.mulh x) p c)).1[off + j]! = p + c := by
      rw [ih₂ (off + j) (.inl (by lia)), UInt64Array.getElem!_set!]
      simp; lia
    refine ⟨ih₁, fun i hi => ?_, ?_⟩
    · rw [ih₂ i (by lia), UInt64Array.getElem!_set!]
      grind
    · obtain ⟨k, hk⟩ : ∃ k, a.size - j = k + 1 := ⟨a.size - j - 1, by lia⟩
      have hk' : a.size - (j + 1) = k := by lia
      rw [hk', ← Nat.add_assoc, ← Nat.add_assoc] at ih₃
      rw [hk, UInt64Array.valAt_succ, UInt64Array.valAt_succ, hv,
        ← UInt64Array.Slice.getElem_eq_getElem! a j (by lia), Nat.mul_succ, Nat.pow_add]
      have := mul1_step y x c
      generalize (mul1Loop _ _ _ _ _ _).1.valAt _ _ = R at *
      generalize (mul1Loop _ _ _ _ _ _).2.toNat = c' at *
      generalize (UInt64.addh _ _ _).toNat = c₁ at *
      generalize a.array.valAt _ k = A at *
      generalize 2 ^ (64 * k) = P at *
      grind
  | case2 r j c h =>
    rw [mul1Loop]
    simp [h, show a.size - j = 0 by lia]

@[simp] public theorem size_mul1 (r : UInt64Array) (off : Nat) (a : UInt64Array.Slice)
    (x c : UInt64) (hr : off + a.size ≤ r.size) : (mul1 r off a x c).1.size = r.size :=
  (mul1Loop_spec r off a x 0 c hr).1

/-- `mul1` leaves the limbs of `r` outside the ones it writes unchanged. -/
public theorem getElem!_mul1 (r : UInt64Array) (off : Nat) (a : UInt64Array.Slice) (x c : UInt64)
    (hr : off + a.size ≤ r.size) (i : Nat) (hi : i < off ∨ off + a.size ≤ i) :
    (mul1 r off a x c).1[i]! = r[i]! :=
  (mul1Loop_spec r off a x 0 c hr).2.1 i (by lia)

public theorem valAt_mul1 (r : UInt64Array) (off : Nat) (a : UInt64Array.Slice) (x c : UInt64)
    (hr : off + a.size ≤ r.size) :
    (mul1 r off a x c).1.valAt off a.size + 2 ^ (64 * a.size) * (mul1 r off a x c).2.toNat =
      a.toNat * x.toNat + c.toNat := by
  simpa [mul1, UInt64Array.Slice.toNat_eq_valAt] using (mul1Loop_spec r off a x 0 c hr).2.2

/-! ## Adding a product by a limb -/

/-- One limb of `addMul1`: the low word of `z + y * x + c` and the high word. -/
private theorem addMul1_step (z y x c : UInt64) :
    (y * x + c + z).toNat +
        2 ^ 64 * (UInt64.addh (UInt64.addh (y.mulh x) (y * x) c) (y * x + c) z).toNat =
      z.toNat + y.toNat * x.toNat + c.toNat := by
  have : y.toNat * x.toNat ≤ (2 ^ 64 - 1) * (2 ^ 64 - 1) :=
    Nat.mul_le_mul (by have := y.toNat_lt; lia) (by have := x.toNat_lt; lia)
  have := c.toNat_lt; have := z.toNat_lt
  simp only [UInt64.toNat_addh, UInt64.toNat_mulh, UInt64.toNat_add, UInt64.toNat_mul]
  generalize y.toNat * x.toNat = p at *
  generalize c.toNat = c at *
  generalize z.toNat = z at *
  lia

/--
Adds limbs `j` to `a.size - 1` of `a * x`, plus the carry `c`, to the limbs of `r` from limb
`off + j` on.
-/
def addMul1Loop (r : UInt64Array) (off : Nat) (a : UInt64Array.Slice) (x : UInt64) (j : Nat)
    (c : UInt64) : UInt64Array × UInt64 :=
  if h : j < a.size then
    let y := a[j]
    let z := r[off + j]!
    let p := y * x
    let t := p + c
    addMul1Loop (r.set! (off + j) (t + z)) off a x (j + 1)
      (UInt64.addh (UInt64.addh (y.mulh x) p c) t z)
  else
    (r, c)

/--
Adds `a * x + c` to the limbs of `r` from limb `off` on and returns the carry out, like GMP's
`mpn_addmul_1`.
-/
public def addMul1 (r : UInt64Array) (off : Nat) (a : UInt64Array.Slice) (x : UInt64)
    (c : UInt64 := 0) : UInt64Array × UInt64 :=
  addMul1Loop r off a x 0 c

private theorem addMul1Loop_spec (r : UInt64Array) (off : Nat) (a : UInt64Array.Slice)
    (x : UInt64) (j : Nat) (c : UInt64) (hr : off + a.size ≤ r.size) :
    (addMul1Loop r off a x j c).1.size = r.size ∧
      (∀ i, (i < off + j ∨ off + a.size ≤ i) →
        (addMul1Loop r off a x j c).1[i]! = r[i]!) ∧
      (addMul1Loop r off a x j c).1.valAt (off + j) (a.size - j) +
          2 ^ (64 * (a.size - j)) * (addMul1Loop r off a x j c).2.toNat =
        r.valAt (off + j) (a.size - j) + a.array.valAt (a.start + j) (a.size - j) * x.toNat +
          c.toNat := by
  induction r, j, c using addMul1Loop.induct off a x with
  | case1 r j c h y z p t ih =>
    rw [addMul1Loop]
    simp only [h, ↓reduceDIte]
    obtain ⟨ih₁, ih₂, ih₃⟩ := ih (by simpa using hr)
    simp only [UInt64Array.size_set!] at ih₁
    have hv : (addMul1Loop (r.set! (off + j) (t + z)) off a x (j + 1)
        (UInt64.addh (UInt64.addh (y.mulh x) p c) t z)).1[off + j]! = t + z := by
      rw [ih₂ (off + j) (.inl (by lia)), UInt64Array.getElem!_set!]
      simp; lia
    have hr' : (r.set! (off + j) (t + z)).valAt (off + (j + 1)) (a.size - (j + 1)) =
        r.valAt (off + (j + 1)) (a.size - (j + 1)) :=
      UInt64Array.valAt_congr _ fun i hi _ => by rw [UInt64Array.getElem!_set!]; grind
    refine ⟨ih₁, fun i hi => ?_, ?_⟩
    · rw [ih₂ i (by lia), UInt64Array.getElem!_set!]
      grind
    · rw [hr'] at ih₃
      obtain ⟨k, hk⟩ : ∃ k, a.size - j = k + 1 := ⟨a.size - j - 1, by lia⟩
      have hk' : a.size - (j + 1) = k := by lia
      rw [hk', ← Nat.add_assoc, ← Nat.add_assoc] at ih₃
      rw [hk, UInt64Array.valAt_succ, UInt64Array.valAt_succ, UInt64Array.valAt_succ, hv,
        ← UInt64Array.Slice.getElem_eq_getElem! a j (by lia), Nat.mul_succ, Nat.pow_add]
      have := addMul1_step z y x c
      generalize (addMul1Loop _ _ _ _ _ _).1.valAt _ _ = R at *
      generalize (addMul1Loop _ _ _ _ _ _).2.toNat = c' at *
      generalize (UInt64.addh _ _ _).toNat = c₁ at *
      generalize r.valAt _ k = R₀ at *
      generalize a.array.valAt _ k = A at *
      generalize 2 ^ (64 * k) = P at *
      grind
  | case2 r j c h =>
    rw [addMul1Loop]
    simp [h, show a.size - j = 0 by lia]

@[simp] public theorem size_addMul1 (r : UInt64Array) (off : Nat) (a : UInt64Array.Slice)
    (x c : UInt64) (hr : off + a.size ≤ r.size) : (addMul1 r off a x c).1.size = r.size :=
  (addMul1Loop_spec r off a x 0 c hr).1

/-- `addMul1` leaves the limbs of `r` outside the ones it writes unchanged. -/
public theorem getElem!_addMul1 (r : UInt64Array) (off : Nat) (a : UInt64Array.Slice)
    (x c : UInt64) (hr : off + a.size ≤ r.size) (i : Nat) (hi : i < off ∨ off + a.size ≤ i) :
    (addMul1 r off a x c).1[i]! = r[i]! :=
  (addMul1Loop_spec r off a x 0 c hr).2.1 i (by lia)

public theorem valAt_addMul1 (r : UInt64Array) (off : Nat) (a : UInt64Array.Slice)
    (x c : UInt64) (hr : off + a.size ≤ r.size) :
    (addMul1 r off a x c).1.valAt off a.size + 2 ^ (64 * a.size) * (addMul1 r off a x c).2.toNat =
      r.valAt off a.size + a.toNat * x.toNat + c.toNat := by
  simpa [addMul1, UInt64Array.Slice.toNat_eq_valAt] using (addMul1Loop_spec r off a x 0 c hr).2.2

/-! ## Schoolbook multiplication -/

/--
Adds rows `i` to `b.size - 1` of `a * b` to the limbs of `r`, row `i` from limb `off + i` on, and
stores the carry out of each row in the limb above it.
-/
def mulBasecaseLoop (r : UInt64Array) (off : Nat) (a b : UInt64Array.Slice) (i : Nat) :
    UInt64Array :=
  if h : i < b.size then
    let p := addMul1 r (off + i) a b[i]
    mulBasecaseLoop (p.1.set! (off + i + a.size) p.2) off a b (i + 1)
  else
    r

/--
Writes the `a.size + b.size` limbs of `a * b` into `r` from limb `off` on, like GMP's
`mpn_mul_basecase`. It requires `0 < b.size`, and leaves `r` unchanged otherwise.
-/
public def mulBasecase (r : UInt64Array) (off : Nat) (a b : UInt64Array.Slice) : UInt64Array :=
  if h : 0 < b.size then
    let p := mul1 r off a b[0]
    mulBasecaseLoop (p.1.set! (off + a.size) p.2) off a b 1
  else
    r

private theorem mulBasecaseLoop_spec (r : UInt64Array) (off : Nat) (a b : UInt64Array.Slice)
    (i : Nat) (hr : off + a.size + b.size ≤ r.size) :
    (mulBasecaseLoop r off a b i).size = r.size ∧
      (∀ k, (k < off + i ∨ off + a.size + b.size ≤ k) →
        (mulBasecaseLoop r off a b i)[k]! = r[k]!) ∧
      (i ≤ b.size → (mulBasecaseLoop r off a b i).valAt off (a.size + b.size) =
        r.valAt off (a.size + i) +
          2 ^ (64 * i) * (a.toNat * b.array.valAt (b.start + i) (b.size - i))) := by
  induction r, i using mulBasecaseLoop.induct off a b with
  | case1 r i h p ih =>
    rw [mulBasecaseLoop]
    simp only [h, ↓reduceDIte]
    have hp₁ : p.1.size = r.size := size_addMul1 r (off + i) a b[i] 0 (by lia)
    have hp₂ : ∀ k, (k < off + i ∨ off + i + a.size ≤ k) → p.1[k]! = r[k]! :=
      getElem!_addMul1 r (off + i) a b[i] 0 (by lia)
    have hp₃ := valAt_addMul1 r (off + i) a b[i] 0 (by lia)
    obtain ⟨ih₁, ih₂, ih₃⟩ := ih (by simpa [hp₁] using hr)
    simp only [UInt64Array.size_set!, hp₁] at ih₁
    refine ⟨ih₁, fun k hk => ?_, fun _ => ?_⟩
    · rw [ih₂ k (by lia), UInt64Array.getElem!_set!_of_ne _ _ (by lia), hp₂ k (by lia)]
    · rw [ih₃ (by lia)]
      -- The new row: the limbs below it, the row itself, and its carry.
      have hlow : (p.1.set! (off + i + a.size) p.2).valAt off i = r.valAt off i :=
        UInt64Array.valAt_congr _ fun k _ hk => by
          rw [UInt64Array.getElem!_set!_of_ne _ _ (by lia), hp₂ k (by lia)]
      have hrow : (p.1.set! (off + i + a.size) p.2).valAt (off + i) a.size =
          p.1.valAt (off + i) a.size :=
        UInt64Array.valAt_congr _ fun k _ hk => by
          rw [UInt64Array.getElem!_set!_of_ne _ _ (by lia)]
      have htop : (p.1.set! (off + i + a.size) p.2)[off + i + a.size]! = p.2 := by
        rw [UInt64Array.getElem!_set!_self _ _ _ (by lia)]
      rw [show a.size + (i + 1) = i + (a.size + 1) by lia, UInt64Array.valAt_add,
        UInt64Array.valAt_add _ _ a.size 1, UInt64Array.valAt_one, htop, hlow, hrow,
        Nat.add_comm a.size i, UInt64Array.valAt_add]
      obtain ⟨k, hk⟩ : ∃ k, b.size - i = k + 1 := ⟨b.size - i - 1, by lia⟩
      rw [show b.size - (i + 1) = k by lia, hk, UInt64Array.valAt_succ,
        ← UInt64Array.Slice.getElem_eq_getElem! b i (by lia), Nat.mul_succ, Nat.pow_add,
        ← Nat.add_assoc]
      simp only [UInt64.toNat_zero, Nat.add_zero] at hp₃
      generalize p.1.valAt _ _ = R at *
      generalize p.2.toNat = c at *
      generalize r.valAt _ a.size = R₀ at *
      generalize r.valAt _ i = L at *
      generalize b.array.valAt _ k = B at *
      generalize b[i].toNat = y at *
      generalize a.toNat = A at *
      generalize 2 ^ (64 * i) = P at *
      generalize 2 ^ (64 * a.size) = Q at *
      grind
  | case2 r i h =>
    rw [mulBasecaseLoop]
    simp only [h, ↓reduceDIte]
    refine ⟨by simp, by simp, fun hi => ?_⟩
    simp [show i = b.size by lia]

@[simp] public theorem size_mulBasecase (r : UInt64Array) (off : Nat) (a b : UInt64Array.Slice)
    (hr : off + a.size + b.size ≤ r.size) : (mulBasecase r off a b).size = r.size := by
  rw [mulBasecase]
  split
  · rw [(mulBasecaseLoop_spec _ off a b 1
      (by rw [UInt64Array.size_set!, size_mul1 _ _ _ _ _ (by lia)]; lia)).1,
      UInt64Array.size_set!, size_mul1 _ _ _ _ _ (by lia)]
  · rfl

/-- `mulBasecase` leaves the limbs of `r` outside the ones it writes unchanged. -/
public theorem getElem!_mulBasecase (r : UInt64Array) (off : Nat) (a b : UInt64Array.Slice)
    (hr : off + a.size + b.size ≤ r.size) (k : Nat)
    (hk : k < off ∨ off + a.size + b.size ≤ k) :
    (mulBasecase r off a b)[k]! = r[k]! := by
  rw [mulBasecase]
  split
  · rw [(mulBasecaseLoop_spec _ off a b 1
      (by rw [UInt64Array.size_set!, size_mul1 _ _ _ _ _ (by lia)]; lia)).2.1 k (by lia),
      UInt64Array.getElem!_set!_of_ne _ _ (by lia), getElem!_mul1 _ _ _ _ _ (by lia) k (by lia)]
  · rfl

public theorem valAt_mulBasecase (r : UInt64Array) (off : Nat) (a b : UInt64Array.Slice)
    (hb : 0 < b.size) (hr : off + a.size + b.size ≤ r.size) :
    (mulBasecase r off a b).valAt off (a.size + b.size) = a.toNat * b.toNat := by
  rw [mulBasecase]
  simp only [hb, ↓reduceDIte]
  have hp₁ := size_mul1 r off a b[0] 0 (by lia)
  have hp₃ := valAt_mul1 r off a b[0] 0 (by lia)
  rw [(mulBasecaseLoop_spec _ off a b 1 (by rw [UInt64Array.size_set!, hp₁]; lia)).2.2 hb,
    UInt64Array.valAt_add, UInt64Array.valAt_one, UInt64Array.getElem!_set!_self _ _ _ (by lia)]
  have hrow : ((mul1 r off a b[0]).1.set! (off + a.size) (mul1 r off a b[0]).2).valAt off a.size =
      (mul1 r off a b[0]).1.valAt off a.size :=
    UInt64Array.valAt_congr _ fun k _ hk => by
      rw [UInt64Array.getElem!_set!_of_ne _ _ (by lia)]
  have hb₀ := UInt64Array.Slice.getElem_eq_getElem! b 0 (by lia)
  rw [Nat.add_zero] at hb₀
  have hB : b.array.valAt b.start b.size =
      b[0].toNat + 2 ^ 64 * b.array.valAt (b.start + 1) (b.size - 1) := by
    obtain ⟨k, hk⟩ : ∃ k, b.size = k + 1 := ⟨b.size - 1, by lia⟩
    rw [hk, UInt64Array.valAt_succ, hb₀, Nat.add_sub_cancel]
  rw [hrow, UInt64Array.Slice.toNat_eq_valAt b, hB]
  simp only [UInt64.toNat_zero, Nat.add_zero] at hp₃
  generalize (mul1 _ _ _ _).1.valAt _ _ = R at *
  generalize (mul1 _ _ _ _).2.toNat = c at *
  generalize b.array.valAt _ (b.size - 1) = B at *
  generalize b[0].toNat = y at *
  generalize a.toNat = A at *
  generalize 2 ^ (64 * a.size) = Q at *
  grind

end MPN
