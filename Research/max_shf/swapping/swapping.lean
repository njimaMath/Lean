import Mathlib

open scoped BigOperators

set_option autoImplicit false

namespace Swapping

variable {kE : Nat → Type*}

/--
`Interior kE m` stores the `m` interior pairs
`(x_1, y_1), ..., (x_m, y_m)` from the blueprint.

The `i`-th pair has type `kE (i + 1) × kE (i + 1)`, so this encoding works
with separate spaces `kE_ell`.
-/
abbrev Interior (kE : Nat → Type*) (m : Nat) :=
  (i : Fin m) → kE (i.1 + 1) × kE (i.1 + 1)

/--
`ZStarFamily kE m` is the typed form of the blueprint assumption
`z_i^* ∈ kE_i` for `i = 1, ..., m`.

With Lean's zero-based `Fin m`, the component `zStar i` has type `kE (i.1 + 1)`.
-/
abbrev ZStarFamily (kE : Nat → Type*) (m : Nat) :=
  (i : Fin m) → kE (i.1 + 1)

/--
Swap the first `q + 1` pairs:

`swapUpTo q (x_1, y_1, ..., x_m, y_m) = (y_1, x_1, ..., y_{q+1}, x_{q+1}, x_{q+2}, y_{q+2}, ...)`.
-/
def swapUpTo {m : Nat} (q : Fin m) (U : Interior kE m) : Interior kE m :=
  fun i => if i ≤ q then (U i).swap else U i

@[simp] lemma swapUpTo_apply_of_le {m : Nat} {q i : Fin m} (h : i ≤ q)
    (U : Interior kE m) :
    swapUpTo q U i = (U i).swap := by
  simp [swapUpTo, h]

@[simp] lemma swapUpTo_apply_of_not_le {m : Nat} {q i : Fin m} (h : ¬ i ≤ q)
    (U : Interior kE m) :
    swapUpTo q U i = U i := by
  simp [swapUpTo, h]

lemma swapUpTo_involutive {m : Nat} (q : Fin m) :
    Function.Involutive (swapUpTo (kE := kE) q) := by
  intro U
  funext i
  by_cases h : i ≤ q
  · simp [swapUpTo, h]
  · simp [swapUpTo, h]

/-- The first `x`-coordinate after the entrance point `x_0`. -/
def headX {m : Nat} (xLast : kE (m + 1)) (U : Interior kE m) : kE 1 :=
  if h : 0 < m then
    (U ⟨0, h⟩).1
  else
    by
      have hm : m = 0 := by omega
      simpa [hm] using xLast

/-- The first `y`-coordinate after the entrance point `y_0`. -/
def headY {m : Nat} (yLast : kE (m + 1)) (U : Interior kE m) : kE 1 :=
  if h : 0 < m then
    (U ⟨0, h⟩).2
  else
    by
      have hm : m = 0 := by omega
      simpa [hm] using yLast

/-- The `x`-coordinate immediately after the pair indexed by `i`. -/
def nextX {m : Nat} (xLast : kE (m + 1)) (U : Interior kE m) (i : Fin m) :
    kE (i.1 + 2) :=
  if h : i.1 + 1 < m then
    (U ⟨i.1 + 1, h⟩).1
  else
    by
      have hm : i.1 + 2 = m + 1 := by omega
      simpa [hm] using xLast

/-- The `y`-coordinate immediately after the pair indexed by `i`. -/
def nextY {m : Nat} (yLast : kE (m + 1)) (U : Interior kE m) (i : Fin m) :
    kE (i.1 + 2) :=
  if h : i.1 + 1 < m then
    (U ⟨i.1 + 1, h⟩).2
  else
    by
      have hm : i.1 + 2 = m + 1 := by omega
      simpa [hm] using yLast

/-- The blueprint's `Delta_ell^c`. -/
def delta {α β : Type*} (g : α → β → ℝ) (zStar : α) (c : ℝ)
    (x y : α) (x' y' : β) : ℝ :=
  g x x' * g y y' - c * g zStar x' * g zStar y'

/-- Entrance factor for the `+`-sum. -/
def entryPlus {m : Nat} (f0 : kE 0 → kE 1 → ℝ)
    (x0 y0 : kE 0) (xLast : kE (m + 1)) (yLast : kE (m + 1))
    (U : Interior kE m) : ℝ :=
  f0 x0 (headX xLast U) * f0 y0 (headY yLast U)

/-- Entrance factor for the `-`-sum. -/
def entryMinus {m : Nat} (f0 : kE 0 → kE 1 → ℝ)
    (x0 y0 : kE 0) (xLast : kE (m + 1)) (yLast : kE (m + 1))
    (U : Interior kE m) : ℝ :=
  f0 y0 (headX xLast U) * f0 x0 (headY yLast U)

/-- The undecorated factor at level `i`. -/
def plainFactor {m : Nat}
    (f : (i : Fin m) → kE (i.1 + 1) → kE (i.1 + 2) → ℝ)
    (xLast : kE (m + 1)) (yLast : kE (m + 1))
    (U : Interior kE m) (i : Fin m) : ℝ :=
  f i (U i).1 (nextX xLast U i) * f i (U i).2 (nextY yLast U i)

/-- The factor `f_i(z_i^*, x_{i+1}) f_i(z_i^*, y_{i+1})` inside `Delta_i^c`. -/
def starFactor {m : Nat}
    (zStar : (i : Fin m) → kE (i.1 + 1))
    (f : (i : Fin m) → kE (i.1 + 1) → kE (i.1 + 2) → ℝ)
    (xLast : kE (m + 1)) (yLast : kE (m + 1))
    (U : Interior kE m) (i : Fin m) : ℝ :=
  f i (zStar i) (nextX xLast U i) * f i (zStar i) (nextY yLast U i)

/-- The decorated factor `Delta_i^c(...)`. -/
def deltaFactor {m : Nat}
    (zStar : (i : Fin m) → kE (i.1 + 1))
    (f : (i : Fin m) → kE (i.1 + 1) → kE (i.1 + 2) → ℝ)
    (c : ℝ) (xLast : kE (m + 1)) (yLast : kE (m + 1))
    (U : Interior kE m) (i : Fin m) : ℝ :=
  delta (f i) (zStar i) c (U i).1 (U i).2 (nextX xLast U i) (nextY yLast U i)

/--
The set `I_U^(q)` from the blueprint, written with zero-based indexing:
`tailSet I U n = { i ∈ I U | n ≤ i }`.

Thus:
- `tailSet I U 0 = I U`
- `tailSet I U m = ∅`.
-/
def tailSet {m : Nat} (I : Interior kE m → Finset (Fin m))
    (U : Interior kE m) (n : Nat) : Finset (Fin m) :=
  (I U).filter fun i => n ≤ i.1

@[simp] lemma mem_tailSet {m : Nat} (I : Interior kE m → Finset (Fin m))
    (U : Interior kE m) (n : Nat) (i : Fin m) :
    i ∈ tailSet I U n ↔ i ∈ I U ∧ n ≤ i.1 := by
  simp [tailSet]

@[simp] lemma tailSet_zero {m : Nat} (I : Interior kE m → Finset (Fin m))
    (U : Interior kE m) :
    tailSet I U 0 = I U := by
  ext i
  simp

@[simp] lemma tailSet_top {m : Nat} (I : Interior kE m → Finset (Fin m))
    (U : Interior kE m) :
    tailSet I U m = ∅ := by
  ext i
  simp

/--
The product in which indices inside `tailSet I U n` are decorated by `deltaFactor`,
and the other indices keep the plain factor.

This is the blueprint's product defining `F_{n+1}^+` and `F_{n+1}^-`.
-/
def bodyProd {m : Nat} (I : Interior kE m → Finset (Fin m))
    (f : (i : Fin m) → kE (i.1 + 1) → kE (i.1 + 2) → ℝ)
    (zStar : (i : Fin m) → kE (i.1 + 1))
    (c : ℝ) (xLast : kE (m + 1)) (yLast : kE (m + 1))
    (U : Interior kE m) (n : Nat) : ℝ :=
  Finset.prod Finset.univ fun i : Fin m =>
    if i ∈ tailSet I U n then
      deltaFactor zStar f c xLast yLast U i
    else
      plainFactor f xLast yLast U i

/-- The blueprint's `F_{n+1}^+`. -/
def partialPlus {m : Nat} (A : Finset (Interior kE m))
    (I : Interior kE m → Finset (Fin m))
    (f0 : kE 0 → kE 1 → ℝ)
    (f : (i : Fin m) → kE (i.1 + 1) → kE (i.1 + 2) → ℝ)
    (zStar : (i : Fin m) → kE (i.1 + 1))
    (x0 y0 : kE 0) (xLast : kE (m + 1)) (yLast : kE (m + 1))
    (c : ℝ) (n : Nat) : ℝ :=
  Finset.sum A fun U =>
    entryPlus f0 x0 y0 xLast yLast U * bodyProd I f zStar c xLast yLast U n

/-- The blueprint's `F_{n+1}^-`. -/
def partialMinus {m : Nat} (A : Finset (Interior kE m))
    (I : Interior kE m → Finset (Fin m))
    (f0 : kE 0 → kE 1 → ℝ)
    (f : (i : Fin m) → kE (i.1 + 1) → kE (i.1 + 2) → ℝ)
    (zStar : (i : Fin m) → kE (i.1 + 1))
    (x0 y0 : kE 0) (xLast : kE (m + 1)) (yLast : kE (m + 1))
    (c : ℝ) (n : Nat) : ℝ :=
  Finset.sum A fun U =>
    entryMinus f0 x0 y0 xLast yLast U * bodyProd I f zStar c xLast yLast U n

/-- The blueprint's `F_{n+1} = F_{n+1}^+ - F_{n+1}^-`. -/
def partialSum {m : Nat} (A : Finset (Interior kE m))
    (I : Interior kE m → Finset (Fin m))
    (f0 : kE 0 → kE 1 → ℝ)
    (f : (i : Fin m) → kE (i.1 + 1) → kE (i.1 + 2) → ℝ)
    (zStar : (i : Fin m) → kE (i.1 + 1))
    (x0 y0 : kE 0) (xLast : kE (m + 1)) (yLast : kE (m + 1))
    (c : ℝ) (n : Nat) : ℝ :=
  partialPlus A I f0 f zStar x0 y0 xLast yLast c n -
    partialMinus A I f0 f zStar x0 y0 xLast yLast c n

@[simp] lemma bodyProd_zero {m : Nat} (I : Interior kE m → Finset (Fin m))
    (f : (i : Fin m) → kE (i.1 + 1) → kE (i.1 + 2) → ℝ)
    (zStar : (i : Fin m) → kE (i.1 + 1))
    (c : ℝ) (xLast : kE (m + 1)) (yLast : kE (m + 1))
    (U : Interior kE m) :
    bodyProd I f zStar c xLast yLast U 0 =
      Finset.prod Finset.univ fun i : Fin m =>
        if i ∈ I U then
          deltaFactor zStar f c xLast yLast U i
        else
          plainFactor f xLast yLast U i := by
  simp [bodyProd]

@[simp] lemma bodyProd_top {m : Nat} (I : Interior kE m → Finset (Fin m))
    (f : (i : Fin m) → kE (i.1 + 1) → kE (i.1 + 2) → ℝ)
    (zStar : (i : Fin m) → kE (i.1 + 1))
    (c : ℝ) (xLast : kE (m + 1)) (yLast : kE (m + 1))
    (U : Interior kE m) :
    bodyProd I f zStar c xLast yLast U m =
      Finset.prod Finset.univ (plainFactor f xLast yLast U) := by
  simp [bodyProd]

lemma deltaFactor_eq_plainFactor_sub {m : Nat}
    (zStar : (i : Fin m) → kE (i.1 + 1))
    (f : (i : Fin m) → kE (i.1 + 1) → kE (i.1 + 2) → ℝ)
    (c : ℝ) (xLast : kE (m + 1)) (yLast : kE (m + 1))
    (U : Interior kE m) (i : Fin m) :
    deltaFactor zStar f c xLast yLast U i =
      plainFactor f xLast yLast U i - c * starFactor zStar f xLast yLast U i := by
  simp [deltaFactor, plainFactor, starFactor, delta]
  ring

lemma entryPlus_swapUpTo {m : Nat} (f0 : kE 0 → kE 1 → ℝ)
    (x0 y0 : kE 0) (xLast : kE (m + 1)) (yLast : kE (m + 1))
    (U : Interior kE m) (q : Fin m) :
    entryPlus f0 x0 y0 xLast yLast (swapUpTo q U) =
      entryMinus f0 x0 y0 xLast yLast U := by
  have hm : 0 < m := Nat.zero_lt_of_lt q.2
  have hz : (⟨0, hm⟩ : Fin m) ≤ q := by
    simp [Fin.le_iff_val_le_val]
  simp [entryPlus, entryMinus, headX, headY, hm, swapUpTo, hz]
  ring

lemma entryMinus_swapUpTo {m : Nat} (f0 : kE 0 → kE 1 → ℝ)
    (x0 y0 : kE 0) (xLast : kE (m + 1)) (yLast : kE (m + 1))
    (U : Interior kE m) (q : Fin m) :
    entryMinus f0 x0 y0 xLast yLast (swapUpTo q U) =
      entryPlus f0 x0 y0 xLast yLast U := by
  have hm : 0 < m := Nat.zero_lt_of_lt q.2
  have hz : (⟨0, hm⟩ : Fin m) ≤ q := by
    simp [Fin.le_iff_val_le_val]
  simp [entryPlus, entryMinus, headX, headY, hm, swapUpTo, hz]
  ring

lemma plainFactor_swapUpTo_of_lt {m : Nat}
    (f : (i : Fin m) → kE (i.1 + 1) → kE (i.1 + 2) → ℝ)
    (xLast : kE (m + 1)) (yLast : kE (m + 1)) (U : Interior kE m)
    {i q : Fin m} (h : i < q) :
    plainFactor f xLast yLast (swapUpTo q U) i =
      plainFactor f xLast yLast U i := by
  have hiq : i ≤ q := le_of_lt h
  have hsucc : i.1 + 1 ≤ q.1 := Nat.succ_le_of_lt h
  have hnext : i.1 + 1 < m := lt_of_le_of_lt hsucc q.2
  let j : Fin m := ⟨i.1 + 1, hnext⟩
  have hjq : j ≤ q := hsucc
  simp [plainFactor, nextX, nextY, swapUpTo, hiq, hjq, hnext, j]
  ring

lemma plainFactor_swapUpTo_of_gt {m : Nat}
    (f : (i : Fin m) → kE (i.1 + 1) → kE (i.1 + 2) → ℝ)
    (xLast : kE (m + 1)) (yLast : kE (m + 1)) (U : Interior kE m)
    {i q : Fin m} (h : q < i) :
    plainFactor f xLast yLast (swapUpTo q U) i =
      plainFactor f xLast yLast U i := by
  have hiq : ¬ i ≤ q := not_le_of_gt h
  by_cases hnext : i.1 + 1 < m
  · let j : Fin m := ⟨i.1 + 1, hnext⟩
    have hjq : ¬ j ≤ q := by
      apply not_le_of_gt
      exact lt_of_lt_of_le h (Nat.le_succ _)
    simp [plainFactor, nextX, nextY, swapUpTo, hiq, hjq, hnext, j]
  · simp [plainFactor, nextX, nextY, swapUpTo, hiq, hnext]

lemma starFactor_swapUpTo {m : Nat}
    (zStar : (i : Fin m) → kE (i.1 + 1))
    (f : (i : Fin m) → kE (i.1 + 1) → kE (i.1 + 2) → ℝ)
    (xLast : kE (m + 1)) (yLast : kE (m + 1))
    (U : Interior kE m) (q : Fin m) :
    starFactor zStar f xLast yLast (swapUpTo q U) q =
      starFactor zStar f xLast yLast U q := by
  by_cases hnext : q.1 + 1 < m
  · let j : Fin m := ⟨q.1 + 1, hnext⟩
    have hjq : ¬ j ≤ q := by
      apply not_le_of_gt
      exact Nat.lt_succ_self q.1
    simp [starFactor, nextX, nextY, swapUpTo, hnext, hjq, j]
  · simp [starFactor, nextX, nextY, hnext]

lemma deltaFactor_swapUpTo_of_gt {m : Nat}
    (zStar : (i : Fin m) → kE (i.1 + 1))
    (f : (i : Fin m) → kE (i.1 + 1) → kE (i.1 + 2) → ℝ)
    (c : ℝ) (xLast : kE (m + 1)) (yLast : kE (m + 1))
    (U : Interior kE m) {i q : Fin m} (h : q < i) :
    deltaFactor zStar f c xLast yLast (swapUpTo q U) i =
      deltaFactor zStar f c xLast yLast U i := by
  have hiq : ¬ i ≤ q := not_le_of_gt h
  by_cases hnext : i.1 + 1 < m
  · let j : Fin m := ⟨i.1 + 1, hnext⟩
    have hjq : ¬ j ≤ q := by
      apply not_le_of_gt
      exact lt_of_lt_of_le h (Nat.le_succ _)
    simp [deltaFactor, delta, nextX, nextY, swapUpTo, hnext, hiq, hjq, j]
  · simp [deltaFactor, delta, nextX, nextY, swapUpTo, hnext, hiq]

/--
Finite-set reindexing under an involution.

This is the basic summation device used in the swapping proof.
-/
lemma sum_eq_sum_of_involution {α β : Type*} [DecidableEq α] [AddCommMonoid β]
    (A : Finset α) (tau : α → α) (hA : ∀ ⦃u : α⦄, u ∈ A → tau u ∈ A)
    (htau : Function.Involutive tau) (g h : α → β)
    (hgh : ∀ ⦃u : α⦄, u ∈ A → g (tau u) = h u) :
    Finset.sum A g = Finset.sum A h := by
  classical
  refine Finset.sum_bij (fun u _ => tau u) ?_ ?_ ?_ ?_
  · intro u hu
    exact hA hu
  · intro u1 hu1 u2 hu2 hEq
    exact htau.injective hEq
  · intro v hv
    refine ⟨tau v, hA hv, htau v⟩
  · intro u hu
    have htu : tau u ∈ A := hA hu
    simpa [htau u] using hgh htu

section WithDecEq

variable [∀ n, DecidableEq (kE n)]

/--
The subset `{U ∈ A | q ∈ I U}`.

This is the set of terms that actually survive in the difference
`F_{q+1} - F_q` in the blueprint proof.
-/
def activeSet {m : Nat} (A : Finset (Interior kE m))
    (I : Interior kE m → Finset (Fin m)) (q : Fin m) : Finset (Interior kE m) :=
  A.filter fun U => q ∈ I U

omit [∀ n, DecidableEq (kE n)] in
@[simp] lemma mem_activeSet {m : Nat} (A : Finset (Interior kE m))
    (I : Interior kE m → Finset (Fin m)) (q : Fin m) (U : Interior kE m) :
    U ∈ activeSet A I q ↔ U ∈ A ∧ q ∈ I U := by
  simp [activeSet]

/--
This is the common product appearing in the blueprint's two auxiliary sums
`I` and `-II` after factoring out the coefficient `c`.

Compared to `bodyProd ... q.1`, the `q`-th factor is replaced by
`starFactor ... q`, and the remaining decorated factors begin at `q + 1`.
-/
def stepBodyProd {m : Nat} (I : Interior kE m → Finset (Fin m))
    (f : (i : Fin m) → kE (i.1 + 1) → kE (i.1 + 2) → ℝ)
    (zStar : (i : Fin m) → kE (i.1 + 1))
    (c : ℝ) (xLast : kE (m + 1)) (yLast : kE (m + 1))
    (U : Interior kE m) (q : Fin m) : ℝ :=
  starFactor zStar f xLast yLast U q *
    Finset.prod Finset.univ fun i : Fin m =>
      if i ∈ tailSet I U (q.1 + 1) then
        deltaFactor zStar f c xLast yLast U i
      else if i = q then
        1
      else
        plainFactor f xLast yLast U i

/-- The summand denoted `G_q(U)` in the blueprint proof. -/
def stepPlusTerm {m : Nat} (I : Interior kE m → Finset (Fin m))
    (f0 : kE 0 → kE 1 → ℝ)
    (f : (i : Fin m) → kE (i.1 + 1) → kE (i.1 + 2) → ℝ)
    (zStar : (i : Fin m) → kE (i.1 + 1))
    (x0 y0 : kE 0) (xLast : kE (m + 1)) (yLast : kE (m + 1))
    (c : ℝ) (U : Interior kE m) (q : Fin m) : ℝ :=
  entryPlus f0 x0 y0 xLast yLast U * stepBodyProd I f zStar c xLast yLast U q

/-- The summand denoted `H_q(U)` in the blueprint proof. -/
def stepMinusTerm {m : Nat} (I : Interior kE m → Finset (Fin m))
    (f0 : kE 0 → kE 1 → ℝ)
    (f : (i : Fin m) → kE (i.1 + 1) → kE (i.1 + 2) → ℝ)
    (zStar : (i : Fin m) → kE (i.1 + 1))
    (x0 y0 : kE 0) (xLast : kE (m + 1)) (yLast : kE (m + 1))
    (c : ℝ) (U : Interior kE m) (q : Fin m) : ℝ :=
  entryMinus f0 x0 y0 xLast yLast U * stepBodyProd I f zStar c xLast yLast U q

/-- The blueprint's auxiliary sum `I` after restricting to the active set. -/
def stepPlus {m : Nat} (A : Finset (Interior kE m))
    (I : Interior kE m → Finset (Fin m))
    (f0 : kE 0 → kE 1 → ℝ)
    (f : (i : Fin m) → kE (i.1 + 1) → kE (i.1 + 2) → ℝ)
    (zStar : (i : Fin m) → kE (i.1 + 1))
    (x0 y0 : kE 0) (xLast : kE (m + 1)) (yLast : kE (m + 1))
    (c : ℝ) (q : Fin m) : ℝ :=
  Finset.sum (activeSet A I q) fun U =>
    stepPlusTerm I f0 f zStar x0 y0 xLast yLast c U q

/--
The positive version of the blueprint's second auxiliary sum:
the displayed `II` in the blueprint is `- stepMinus ... q`.
-/
def stepMinus {m : Nat} (A : Finset (Interior kE m))
    (I : Interior kE m → Finset (Fin m))
    (f0 : kE 0 → kE 1 → ℝ)
    (f : (i : Fin m) → kE (i.1 + 1) → kE (i.1 + 2) → ℝ)
    (zStar : (i : Fin m) → kE (i.1 + 1))
    (x0 y0 : kE 0) (xLast : kE (m + 1)) (yLast : kE (m + 1))
    (c : ℝ) (q : Fin m) : ℝ :=
  Finset.sum (activeSet A I q) fun U =>
    stepMinusTerm I f0 f zStar x0 y0 xLast yLast c U q

/-- The common product over all indices except `q`. -/
def stepRemainderProd {m : Nat} (I : Interior kE m → Finset (Fin m))
    (f : (i : Fin m) → kE (i.1 + 1) → kE (i.1 + 2) → ℝ)
    (zStar : (i : Fin m) → kE (i.1 + 1))
    (c : ℝ) (xLast : kE (m + 1)) (yLast : kE (m + 1))
    (U : Interior kE m) (q : Fin m) : ℝ :=
  Finset.prod (Finset.univ.erase q) fun i =>
    if i ∈ tailSet I U (q.1 + 1) then
      deltaFactor zStar f c xLast yLast U i
    else
      plainFactor f xLast yLast U i

omit [∀ n, DecidableEq (kE n)] in
lemma mem_tailSet_step_of_ne {m : Nat} (I : Interior kE m → Finset (Fin m))
    (U : Interior kE m) (q : Fin m) {i : Fin m} (hne : i ≠ q) :
    i ∈ tailSet I U q.1 ↔ i ∈ tailSet I U (q.1 + 1) := by
  constructor
  · intro hi
    rcases (mem_tailSet I U q.1 i).1 hi with ⟨hiI, hqi⟩
    have hqne : q.1 ≠ i.1 := by
      intro hEq
      apply hne
      exact Fin.ext hEq.symm
    have hlt : q.1 < i.1 := lt_of_le_of_ne hqi hqne
    exact (mem_tailSet I U (q.1 + 1) i).2 ⟨hiI, Nat.succ_le_of_lt hlt⟩
  · intro hi
    rcases (mem_tailSet I U (q.1 + 1) i).1 hi with ⟨hiI, hqi⟩
    exact (mem_tailSet I U q.1 i).2 ⟨hiI, Nat.le_of_succ_le hqi⟩

omit [∀ n, DecidableEq (kE n)] in
lemma stepBodyProd_eq_star_mul_remainder {m : Nat} (I : Interior kE m → Finset (Fin m))
    (f : (i : Fin m) → kE (i.1 + 1) → kE (i.1 + 2) → ℝ)
    (zStar : (i : Fin m) → kE (i.1 + 1))
    (c : ℝ) (xLast : kE (m + 1)) (yLast : kE (m + 1))
    (U : Interior kE m) (q : Fin m) :
    stepBodyProd I f zStar c xLast yLast U q =
      starFactor zStar f xLast yLast U q *
        stepRemainderProd I f zStar c xLast yLast U q := by
  let g : Fin m → ℝ := fun i =>
    if i ∈ tailSet I U (q.1 + 1) then
      deltaFactor zStar f c xLast yLast U i
    else if i = q then
      1
    else
      plainFactor f xLast yLast U i
  have hgq : g q = 1 := by
    simp [g, mem_tailSet]
  rw [stepBodyProd, stepRemainderProd]
  have hprod : Finset.prod Finset.univ g = Finset.prod (Finset.univ.erase q) g := by
    simpa [g, hgq] using (Finset.prod_erase (s := Finset.univ) (f := g) (a := q) hgq).symm
  rw [hprod]
  congr 1
  apply Finset.prod_congr rfl
  intro i hi
  have hiq : i ≠ q := (Finset.mem_erase.1 hi).1
  simp [g, hiq]

omit [∀ n, DecidableEq (kE n)] in
lemma bodyProd_succ_eq_plain_mul_remainder {m : Nat} (I : Interior kE m → Finset (Fin m))
    (f : (i : Fin m) → kE (i.1 + 1) → kE (i.1 + 2) → ℝ)
    (zStar : (i : Fin m) → kE (i.1 + 1))
    (c : ℝ) (xLast : kE (m + 1)) (yLast : kE (m + 1))
    (U : Interior kE m) (q : Fin m) :
    bodyProd I f zStar c xLast yLast U (q.1 + 1) =
      plainFactor f xLast yLast U q * stepRemainderProd I f zStar c xLast yLast U q := by
  let g : Fin m → ℝ := fun i =>
    if i ∈ tailSet I U (q.1 + 1) then
      deltaFactor zStar f c xLast yLast U i
    else
      plainFactor f xLast yLast U i
  have hgq : g q = plainFactor f xLast yLast U q := by
    simp [g, mem_tailSet]
  rw [bodyProd, stepRemainderProd]
  have hprod :
      Finset.prod Finset.univ g = g q * Finset.prod (Finset.univ.erase q) g := by
    simpa using
      (Finset.mul_prod_erase (s := Finset.univ) (f := g) (a := q) (by simp)).symm
  rw [hprod, hgq]

omit [∀ n, DecidableEq (kE n)] in
lemma bodyProd_eq_delta_mul_remainder {m : Nat} (I : Interior kE m → Finset (Fin m))
    (f : (i : Fin m) → kE (i.1 + 1) → kE (i.1 + 2) → ℝ)
    (zStar : (i : Fin m) → kE (i.1 + 1))
    (c : ℝ) (xLast : kE (m + 1)) (yLast : kE (m + 1))
    (U : Interior kE m) (q : Fin m) (hqU : q ∈ I U) :
    bodyProd I f zStar c xLast yLast U q.1 =
      deltaFactor zStar f c xLast yLast U q * stepRemainderProd I f zStar c xLast yLast U q := by
  let g0 : Fin m → ℝ := fun i =>
    if i ∈ tailSet I U q.1 then
      deltaFactor zStar f c xLast yLast U i
    else
      plainFactor f xLast yLast U i
  let g1 : Fin m → ℝ := fun i =>
    if i ∈ tailSet I U (q.1 + 1) then
      deltaFactor zStar f c xLast yLast U i
    else
      plainFactor f xLast yLast U i
  have hgq : g0 q = deltaFactor zStar f c xLast yLast U q := by
    simp [g0, hqU, mem_tailSet]
  rw [bodyProd]
  calc
    Finset.prod Finset.univ g0
        = g0 q * Finset.prod (Finset.univ.erase q) g0 := by
            symm
            exact Finset.mul_prod_erase (s := Finset.univ) (f := g0) (a := q) (by simp)
    _ = deltaFactor zStar f c xLast yLast U q * Finset.prod (Finset.univ.erase q) g1 := by
          rw [hgq]
          congr 1
          apply Finset.prod_congr rfl
          intro i hi
          have hne : i ≠ q := (Finset.mem_erase.1 hi).1
          have hiff : i ∈ tailSet I U q.1 ↔ i ∈ tailSet I U (q.1 + 1) :=
            mem_tailSet_step_of_ne I U q hne
          by_cases hi0 : i ∈ tailSet I U q.1
          · have hi1 : i ∈ tailSet I U (q.1 + 1) := hiff.mp hi0
            have hg0 : g0 i = deltaFactor zStar f c xLast yLast U i := by
              dsimp [g0]
              simp [hi0]
            have hg1 : g1 i = deltaFactor zStar f c xLast yLast U i := by
              dsimp [g1]
              simp [hi1]
            rw [hg0, hg1]
          · have hi1 : i ∉ tailSet I U (q.1 + 1) := by
              intro hmem
              exact hi0 (hiff.mpr hmem)
            have hg0 : g0 i = plainFactor f xLast yLast U i := by
              dsimp [g0]
              simp [hi0]
            have hg1 : g1 i = plainFactor f xLast yLast U i := by
              dsimp [g1]
              simp [hi1]
            rw [hg0, hg1]
    _ = deltaFactor zStar f c xLast yLast U q *
          stepRemainderProd I f zStar c xLast yLast U q := by
          simp [stepRemainderProd, g1]

omit [∀ n, DecidableEq (kE n)] in
lemma bodyProd_eq_plain_mul_remainder {m : Nat} (I : Interior kE m → Finset (Fin m))
    (f : (i : Fin m) → kE (i.1 + 1) → kE (i.1 + 2) → ℝ)
    (zStar : (i : Fin m) → kE (i.1 + 1))
    (c : ℝ) (xLast : kE (m + 1)) (yLast : kE (m + 1))
    (U : Interior kE m) (q : Fin m) (hqU : q ∉ I U) :
    bodyProd I f zStar c xLast yLast U q.1 =
      plainFactor f xLast yLast U q * stepRemainderProd I f zStar c xLast yLast U q := by
  let g0 : Fin m → ℝ := fun i =>
    if i ∈ tailSet I U q.1 then
      deltaFactor zStar f c xLast yLast U i
    else
      plainFactor f xLast yLast U i
  let g1 : Fin m → ℝ := fun i =>
    if i ∈ tailSet I U (q.1 + 1) then
      deltaFactor zStar f c xLast yLast U i
    else
      plainFactor f xLast yLast U i
  have hgq : g0 q = plainFactor f xLast yLast U q := by
    simp [g0, hqU, mem_tailSet]
  rw [bodyProd]
  calc
    Finset.prod Finset.univ g0
        = g0 q * Finset.prod (Finset.univ.erase q) g0 := by
            symm
            exact Finset.mul_prod_erase (s := Finset.univ) (f := g0) (a := q) (by simp)
    _ = plainFactor f xLast yLast U q * Finset.prod (Finset.univ.erase q) g1 := by
          rw [hgq]
          congr 1
          apply Finset.prod_congr rfl
          intro i hi
          have hne : i ≠ q := (Finset.mem_erase.1 hi).1
          have hiff : i ∈ tailSet I U q.1 ↔ i ∈ tailSet I U (q.1 + 1) :=
            mem_tailSet_step_of_ne I U q hne
          by_cases hi0 : i ∈ tailSet I U q.1
          · have hi1 : i ∈ tailSet I U (q.1 + 1) := hiff.mp hi0
            have hg0 : g0 i = deltaFactor zStar f c xLast yLast U i := by
              dsimp [g0]
              simp [hi0]
            have hg1 : g1 i = deltaFactor zStar f c xLast yLast U i := by
              dsimp [g1]
              simp [hi1]
            rw [hg0, hg1]
          · have hi1 : i ∉ tailSet I U (q.1 + 1) := by
              intro hmem
              exact hi0 (hiff.mpr hmem)
            have hg0 : g0 i = plainFactor f xLast yLast U i := by
              dsimp [g0]
              simp [hi0]
            have hg1 : g1 i = plainFactor f xLast yLast U i := by
              dsimp [g1]
              simp [hi1]
            rw [hg0, hg1]
    _ = plainFactor f xLast yLast U q *
          stepRemainderProd I f zStar c xLast yLast U q := by
          simp [stepRemainderProd, g1]

omit [∀ n, DecidableEq (kE n)] in
lemma bodyProd_succ_eq_bodyProd_add_c_step_of_mem {m : Nat}
    (I : Interior kE m → Finset (Fin m))
    (f : (i : Fin m) → kE (i.1 + 1) → kE (i.1 + 2) → ℝ)
    (zStar : (i : Fin m) → kE (i.1 + 1))
    (c : ℝ) (xLast : kE (m + 1)) (yLast : kE (m + 1))
    (U : Interior kE m) (q : Fin m) (hqU : q ∈ I U) :
    bodyProd I f zStar c xLast yLast U (q.1 + 1) =
      bodyProd I f zStar c xLast yLast U q.1 +
        c * stepBodyProd I f zStar c xLast yLast U q := by
  rw [bodyProd_succ_eq_plain_mul_remainder]
  rw [bodyProd_eq_delta_mul_remainder I f zStar c xLast yLast U q hqU]
  rw [stepBodyProd_eq_star_mul_remainder]
  rw [deltaFactor_eq_plainFactor_sub]
  ring

omit [∀ n, DecidableEq (kE n)] in
lemma bodyProd_succ_eq_bodyProd_of_not_mem {m : Nat}
    (I : Interior kE m → Finset (Fin m))
    (f : (i : Fin m) → kE (i.1 + 1) → kE (i.1 + 2) → ℝ)
    (zStar : (i : Fin m) → kE (i.1 + 1))
    (c : ℝ) (xLast : kE (m + 1)) (yLast : kE (m + 1))
    (U : Interior kE m) (q : Fin m) (hqU : q ∉ I U) :
    bodyProd I f zStar c xLast yLast U (q.1 + 1) =
      bodyProd I f zStar c xLast yLast U q.1 := by
  rw [bodyProd_succ_eq_plain_mul_remainder,
    bodyProd_eq_plain_mul_remainder I f zStar c xLast yLast U q hqU]

omit [∀ n, DecidableEq (kE n)] in
lemma stepBodyProd_swapUpTo {m : Nat} (I : Interior kE m → Finset (Fin m))
    (f : (i : Fin m) → kE (i.1 + 1) → kE (i.1 + 2) → ℝ)
    (zStar : (i : Fin m) → kE (i.1 + 1))
    (c : ℝ) (xLast : kE (m + 1)) (yLast : kE (m + 1))
    (U : Interior kE m) (q : Fin m) (hIU : I (swapUpTo q U) = I U) :
    stepBodyProd I f zStar c xLast yLast (swapUpTo q U) q =
      stepBodyProd I f zStar c xLast yLast U q := by
  rw [stepBodyProd, stepBodyProd, starFactor_swapUpTo]
  congr 1
  apply Finset.prod_congr rfl
  intro i hi
  by_cases hiq : i = q
  · subst hiq
    simp [mem_tailSet]
  · by_cases hlt : i < q
    · have hnotmemU : i ∉ tailSet I U (q.1 + 1) := by
        intro himem
        rcases (mem_tailSet I U (q.1 + 1) i).1 himem with ⟨_, hqi⟩
        omega
      have hnotmemSw : i ∉ tailSet I (swapUpTo q U) (q.1 + 1) := by
        simpa [tailSet, hIU] using hnotmemU
      simp [hnotmemU, hnotmemSw, hiq, plainFactor_swapUpTo_of_lt, hlt]
    · have hgt : q < i := by
        exact lt_of_le_of_ne (le_of_not_gt hlt) (Ne.symm hiq)
      by_cases himem : i ∈ tailSet I U (q.1 + 1)
      · have himemSw : i ∈ tailSet I (swapUpTo q U) (q.1 + 1) := by
          simpa [tailSet, hIU] using himem
        simp [himem, himemSw, deltaFactor_swapUpTo_of_gt, hgt]
      · have himemSw : i ∉ tailSet I (swapUpTo q U) (q.1 + 1) := by
          simpa [tailSet, hIU] using himem
        simp [himem, himemSw, plainFactor_swapUpTo_of_gt, hgt]

omit [∀ n, DecidableEq (kE n)] in
lemma stepPlusTerm_swapUpTo_eq_stepMinusTerm {m : Nat}
    (I : Interior kE m → Finset (Fin m))
    (f0 : kE 0 → kE 1 → ℝ)
    (f : (i : Fin m) → kE (i.1 + 1) → kE (i.1 + 2) → ℝ)
    (zStar : (i : Fin m) → kE (i.1 + 1))
    (x0 y0 : kE 0) (xLast : kE (m + 1)) (yLast : kE (m + 1))
    (c : ℝ) (U : Interior kE m) (q : Fin m) (hIU : I (swapUpTo q U) = I U) :
    stepPlusTerm I f0 f zStar x0 y0 xLast yLast c (swapUpTo q U) q =
      stepMinusTerm I f0 f zStar x0 y0 xLast yLast c U q := by
  simp [stepPlusTerm, stepMinusTerm, entryPlus_swapUpTo, stepBodyProd_swapUpTo, hIU]

omit [∀ n, DecidableEq (kE n)] in
lemma stepMinusTerm_swapUpTo_eq_stepPlusTerm {m : Nat}
    (I : Interior kE m → Finset (Fin m))
    (f0 : kE 0 → kE 1 → ℝ)
    (f : (i : Fin m) → kE (i.1 + 1) → kE (i.1 + 2) → ℝ)
    (zStar : (i : Fin m) → kE (i.1 + 1))
    (x0 y0 : kE 0) (xLast : kE (m + 1)) (yLast : kE (m + 1))
    (c : ℝ) (U : Interior kE m) (q : Fin m) (hIU : I (swapUpTo q U) = I U) :
    stepMinusTerm I f0 f zStar x0 y0 xLast yLast c (swapUpTo q U) q =
      stepPlusTerm I f0 f zStar x0 y0 xLast yLast c U q := by
  simp [stepPlusTerm, stepMinusTerm, entryMinus_swapUpTo, stepBodyProd_swapUpTo, hIU]

omit [∀ n, DecidableEq (kE n)] in
lemma swapUpTo_mem_activeSet {m : Nat} (A : Finset (Interior kE m))
    (I : Interior kE m → Finset (Fin m))
    (hA : ∀ q : Fin m, ∀ ⦃U : Interior kE m⦄, U ∈ A → swapUpTo q U ∈ A)
    (hI : ∀ q : Fin m, ∀ ⦃U : Interior kE m⦄, U ∈ A → I (swapUpTo q U) = I U)
    (q r : Fin m) {U : Interior kE m} (hU : U ∈ activeSet A I r) :
    swapUpTo q U ∈ activeSet A I r := by
  rw [mem_activeSet] at hU ⊢
  constructor
  · exact hA q hU.1
  · have hIU : I (swapUpTo q U) = I U := hI q hU.1
    simpa [hIU] using hU.2

lemma stepPlus_eq_stepMinus {m : Nat} (A : Finset (Interior kE m))
    (I : Interior kE m → Finset (Fin m))
    (f0 : kE 0 → kE 1 → ℝ)
    (f : (i : Fin m) → kE (i.1 + 1) → kE (i.1 + 2) → ℝ)
    (zStar : (i : Fin m) → kE (i.1 + 1))
    (hA : ∀ q : Fin m, ∀ ⦃U : Interior kE m⦄, U ∈ A → swapUpTo q U ∈ A)
    (hI : ∀ q : Fin m, ∀ ⦃U : Interior kE m⦄, U ∈ A → I (swapUpTo q U) = I U)
    (x0 y0 : kE 0) (xLast : kE (m + 1)) (yLast : kE (m + 1))
    (c : ℝ) (q : Fin m) :
    stepPlus A I f0 f zStar x0 y0 xLast yLast c q =
      stepMinus A I f0 f zStar x0 y0 xLast yLast c q := by
  classical
  have hsum :=
    sum_eq_sum_of_involution
      (A := activeSet A I q) (tau := swapUpTo q)
      (g := fun U => stepPlusTerm I f0 f zStar x0 y0 xLast yLast c U q)
      (h := fun U => stepMinusTerm I f0 f zStar x0 y0 xLast yLast c U q)
      (fun U hU => swapUpTo_mem_activeSet A I hA hI q q hU)
      (swapUpTo_involutive q)
      (by
        intro U hU
        rw [mem_activeSet] at hU
        exact stepPlusTerm_swapUpTo_eq_stepMinusTerm I f0 f zStar x0 y0 xLast yLast c U q
          (hI q hU.1))
  simpa [stepPlus, stepMinus] using hsum

omit [∀ n, DecidableEq (kE n)] in
lemma partialPlus_succ_eq_add_c_stepPlus {m : Nat} (A : Finset (Interior kE m))
    (I : Interior kE m → Finset (Fin m))
    (f0 : kE 0 → kE 1 → ℝ)
    (f : (i : Fin m) → kE (i.1 + 1) → kE (i.1 + 2) → ℝ)
    (zStar : (i : Fin m) → kE (i.1 + 1))
    (x0 y0 : kE 0) (xLast : kE (m + 1)) (yLast : kE (m + 1))
    (c : ℝ) (q : Fin m) :
    partialPlus A I f0 f zStar x0 y0 xLast yLast c (q.1 + 1) =
      partialPlus A I f0 f zStar x0 y0 xLast yLast c q.1 +
        c * stepPlus A I f0 f zStar x0 y0 xLast yLast c q := by
  classical
  let termSucc : Interior kE m → ℝ := fun U =>
    entryPlus f0 x0 y0 xLast yLast U * bodyProd I f zStar c xLast yLast U (q.1 + 1)
  let termNow : Interior kE m → ℝ := fun U =>
    entryPlus f0 x0 y0 xLast yLast U * bodyProd I f zStar c xLast yLast U q.1
  let inactive : Finset (Interior kE m) := A.filter fun U => q ∉ I U
  have hsplitSucc :
      Finset.sum A termSucc =
        Finset.sum (activeSet A I q) termSucc + Finset.sum inactive termSucc := by
    simpa [activeSet, inactive, termSucc] using
      (Finset.sum_filter_add_sum_filter_not A (fun U => q ∈ I U) termSucc).symm
  have hsplitNow :
      Finset.sum A termNow =
        Finset.sum (activeSet A I q) termNow + Finset.sum inactive termNow := by
    simpa [activeSet, inactive, termNow] using
      (Finset.sum_filter_add_sum_filter_not A (fun U => q ∈ I U) termNow).symm
  have hactive :
      Finset.sum (activeSet A I q) termSucc =
        Finset.sum (activeSet A I q) termNow +
          c * stepPlus A I f0 f zStar x0 y0 xLast yLast c q := by
    calc
      Finset.sum (activeSet A I q) termSucc
          = Finset.sum (activeSet A I q) fun U =>
              termNow U + c * stepPlusTerm I f0 f zStar x0 y0 xLast yLast c U q := by
                apply Finset.sum_congr rfl
                intro U hU
                rw [mem_activeSet] at hU
                dsimp [termSucc, termNow]
                rw [bodyProd_succ_eq_bodyProd_add_c_step_of_mem I f zStar c xLast yLast U q hU.2]
                simp [stepPlusTerm]
                ring
      _ = Finset.sum (activeSet A I q) termNow +
            Finset.sum (activeSet A I q)
              (fun U => c * stepPlusTerm I f0 f zStar x0 y0 xLast yLast c U q) := by
                rw [Finset.sum_add_distrib]
      _ = Finset.sum (activeSet A I q) termNow +
            c * stepPlus A I f0 f zStar x0 y0 xLast yLast c q := by
                rw [stepPlus]
                simpa using (Finset.mul_sum (activeSet A I q)
                  (fun U => stepPlusTerm I f0 f zStar x0 y0 xLast yLast c U q) c).symm
  have hinactive :
      Finset.sum inactive termSucc = Finset.sum inactive termNow := by
    apply Finset.sum_congr rfl
    intro U hU
    have hqU : q ∉ I U := by
      simpa [inactive] using (Finset.mem_filter.1 hU).2
    dsimp [termSucc, termNow]
    rw [bodyProd_succ_eq_bodyProd_of_not_mem I f zStar c xLast yLast U q hqU]
  have hmain :
      Finset.sum A termSucc =
        Finset.sum A termNow + c * stepPlus A I f0 f zStar x0 y0 xLast yLast c q := by
    calc
      Finset.sum A termSucc
          = Finset.sum (activeSet A I q) termSucc + Finset.sum inactive termSucc := hsplitSucc
      _ = (Finset.sum (activeSet A I q) termNow +
            c * stepPlus A I f0 f zStar x0 y0 xLast yLast c q) +
            Finset.sum inactive termNow := by rw [hactive, hinactive]
      _ = (Finset.sum (activeSet A I q) termNow + Finset.sum inactive termNow) +
            c * stepPlus A I f0 f zStar x0 y0 xLast yLast c q := by ring
      _ = Finset.sum A termNow + c * stepPlus A I f0 f zStar x0 y0 xLast yLast c q := by
            rw [← hsplitNow]
  simpa [partialPlus, termSucc, termNow] using hmain

omit [∀ n, DecidableEq (kE n)] in
lemma partialMinus_succ_eq_add_c_stepMinus {m : Nat} (A : Finset (Interior kE m))
    (I : Interior kE m → Finset (Fin m))
    (f0 : kE 0 → kE 1 → ℝ)
    (f : (i : Fin m) → kE (i.1 + 1) → kE (i.1 + 2) → ℝ)
    (zStar : (i : Fin m) → kE (i.1 + 1))
    (x0 y0 : kE 0) (xLast : kE (m + 1)) (yLast : kE (m + 1))
    (c : ℝ) (q : Fin m) :
    partialMinus A I f0 f zStar x0 y0 xLast yLast c (q.1 + 1) =
      partialMinus A I f0 f zStar x0 y0 xLast yLast c q.1 +
        c * stepMinus A I f0 f zStar x0 y0 xLast yLast c q := by
  classical
  let termSucc : Interior kE m → ℝ := fun U =>
    entryMinus f0 x0 y0 xLast yLast U * bodyProd I f zStar c xLast yLast U (q.1 + 1)
  let termNow : Interior kE m → ℝ := fun U =>
    entryMinus f0 x0 y0 xLast yLast U * bodyProd I f zStar c xLast yLast U q.1
  let inactive : Finset (Interior kE m) := A.filter fun U => q ∉ I U
  have hsplitSucc :
      Finset.sum A termSucc =
        Finset.sum (activeSet A I q) termSucc + Finset.sum inactive termSucc := by
    simpa [activeSet, inactive, termSucc] using
      (Finset.sum_filter_add_sum_filter_not A (fun U => q ∈ I U) termSucc).symm
  have hsplitNow :
      Finset.sum A termNow =
        Finset.sum (activeSet A I q) termNow + Finset.sum inactive termNow := by
    simpa [activeSet, inactive, termNow] using
      (Finset.sum_filter_add_sum_filter_not A (fun U => q ∈ I U) termNow).symm
  have hactive :
      Finset.sum (activeSet A I q) termSucc =
        Finset.sum (activeSet A I q) termNow +
          c * stepMinus A I f0 f zStar x0 y0 xLast yLast c q := by
    calc
      Finset.sum (activeSet A I q) termSucc
          = Finset.sum (activeSet A I q) fun U =>
              termNow U + c * stepMinusTerm I f0 f zStar x0 y0 xLast yLast c U q := by
                apply Finset.sum_congr rfl
                intro U hU
                rw [mem_activeSet] at hU
                dsimp [termSucc, termNow]
                rw [bodyProd_succ_eq_bodyProd_add_c_step_of_mem I f zStar c xLast yLast U q hU.2]
                simp [stepMinusTerm]
                ring
      _ = Finset.sum (activeSet A I q) termNow +
            Finset.sum (activeSet A I q)
              (fun U => c * stepMinusTerm I f0 f zStar x0 y0 xLast yLast c U q) := by
                rw [Finset.sum_add_distrib]
      _ = Finset.sum (activeSet A I q) termNow +
            c * stepMinus A I f0 f zStar x0 y0 xLast yLast c q := by
                rw [stepMinus]
                simpa using (Finset.mul_sum (activeSet A I q)
                  (fun U => stepMinusTerm I f0 f zStar x0 y0 xLast yLast c U q) c).symm
  have hinactive :
      Finset.sum inactive termSucc = Finset.sum inactive termNow := by
    apply Finset.sum_congr rfl
    intro U hU
    have hqU : q ∉ I U := by
      simpa [inactive] using (Finset.mem_filter.1 hU).2
    dsimp [termSucc, termNow]
    rw [bodyProd_succ_eq_bodyProd_of_not_mem I f zStar c xLast yLast U q hqU]
  have hmain :
      Finset.sum A termSucc =
        Finset.sum A termNow + c * stepMinus A I f0 f zStar x0 y0 xLast yLast c q := by
    calc
      Finset.sum A termSucc
          = Finset.sum (activeSet A I q) termSucc + Finset.sum inactive termSucc := hsplitSucc
      _ = (Finset.sum (activeSet A I q) termNow +
            c * stepMinus A I f0 f zStar x0 y0 xLast yLast c q) +
            Finset.sum inactive termNow := by rw [hactive, hinactive]
      _ = (Finset.sum (activeSet A I q) termNow + Finset.sum inactive termNow) +
            c * stepMinus A I f0 f zStar x0 y0 xLast yLast c q := by ring
      _ = Finset.sum A termNow + c * stepMinus A I f0 f zStar x0 y0 xLast yLast c q := by
            rw [← hsplitNow]
  simpa [partialMinus, termSucc, termNow] using hmain

lemma partialSum_succ_eq {m : Nat} (A : Finset (Interior kE m))
    (I : Interior kE m → Finset (Fin m))
    (f0 : kE 0 → kE 1 → ℝ)
    (f : (i : Fin m) → kE (i.1 + 1) → kE (i.1 + 2) → ℝ)
    (zStar : (i : Fin m) → kE (i.1 + 1))
    (hA : ∀ q : Fin m, ∀ ⦃U : Interior kE m⦄, U ∈ A → swapUpTo q U ∈ A)
    (hI : ∀ q : Fin m, ∀ ⦃U : Interior kE m⦄, U ∈ A → I (swapUpTo q U) = I U)
    (x0 y0 : kE 0) (xLast : kE (m + 1)) (yLast : kE (m + 1))
    (c : ℝ) (q : Fin m) :
    partialSum A I f0 f zStar x0 y0 xLast yLast c (q.1 + 1) =
      partialSum A I f0 f zStar x0 y0 xLast yLast c q.1 := by
  rw [partialSum, partialSum, partialPlus_succ_eq_add_c_stepPlus,
    partialMinus_succ_eq_add_c_stepMinus]
  rw [stepPlus_eq_stepMinus A I f0 f zStar hA hI x0 y0 xLast yLast c q]
  ring

/--
Dictionary between the one-based blueprint notation and the zero-based Lean
definitions used in this file.

- `I_U^(q)` in the blueprint corresponds to `tailSet I U (q - 1)`.
- `F_q^+` corresponds to `partialPlus A I f0 f zStar x0 y0 xLast yLast c (q - 1)`.
- `F_q^-` corresponds to `partialMinus A I f0 f zStar x0 y0 xLast yLast c (q - 1)`.
- `F_q` corresponds to `partialSum A I f0 f zStar x0 y0 xLast yLast c (q - 1)`.
- The blueprint's auxiliary sums `I` and `-II` are `stepPlus ... q` and
  `stepMinus ... q` with zero-based `q : Fin m`.
-/
def BlueprintIndexingGuide : Prop := True

end WithDecEq

/--
A Lean-friendly version of the swapping lemma from `blueprint_swapping.txt`.

`partialSum A I f0 f zStar x0 y0 xLast yLast c 0` is the decorated right-hand
side of the blueprint, while
`partialSum A I f0 f zStar x0 y0 xLast yLast c m` is the undecorated left-hand side.

The theorem assumes `0 < m` to match the convention `ℕ = {1, 2, ...}`.
The parameter `zStar : ZStarFamily kE m` is the explicit typed form of the
assumption `z_i^* ∈ \kE_i`.
-/
theorem swapping_lemma {m : Nat} (A : Finset (Interior kE m))
    [∀ n, DecidableEq (kE n)]
    (_hm : 0 < m)
    (I : Interior kE m → Finset (Fin m))
    (f0 : kE 0 → kE 1 → ℝ)
    (f : (i : Fin m) → kE (i.1 + 1) → kE (i.1 + 2) → ℝ)
    (zStar : ZStarFamily kE m)
    (hA : ∀ q : Fin m, ∀ ⦃U : Interior kE m⦄, U ∈ A → swapUpTo q U ∈ A)
    (hI : ∀ q : Fin m, ∀ ⦃U : Interior kE m⦄, U ∈ A → I (swapUpTo q U) = I U)
    (x0 y0 : kE 0) (xLast : kE (m + 1)) (yLast : kE (m + 1)) (c : ℝ) :
    partialSum A I f0 f zStar x0 y0 xLast yLast c m =
      partialSum A I f0 f zStar x0 y0 xLast yLast c 0 := by
  classical
  have hconst :
      ∀ n, n ≤ m →
        partialSum A I f0 f zStar x0 y0 xLast yLast c n =
          partialSum A I f0 f zStar x0 y0 xLast yLast c 0 := by
    intro n
    induction n with
    | zero =>
        intro _hn
        rfl
    | succ n ih =>
        intro hnle
        have hnm : n < m := lt_of_lt_of_le (Nat.lt_succ_self n) hnle
        let q : Fin m := ⟨n, hnm⟩
        calc
          partialSum A I f0 f zStar x0 y0 xLast yLast c (n + 1)
              = partialSum A I f0 f zStar x0 y0 xLast yLast c n := by
                  simpa [q] using
                    partialSum_succ_eq A I f0 f zStar hA hI x0 y0 xLast yLast c q
          _ = partialSum A I f0 f zStar x0 y0 xLast yLast c 0 := by
                exact ih (Nat.le_of_succ_le hnle)
  simpa using hconst m le_rfl

end Swapping
