/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: af80b72c-f01f-4bf1-a908-6d2ce6d4c685

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>

The version of Mathlib expected in this file appears to be incompatible with Aristotle's.
Please either switch your project to use the same version, or try again with `import Mathlib` only.
Details:
object file '/code/harmonic-lean/.lake/packages/mathlib/.lake/build/lib/lean/Mathlib/Combinatorics/SimpleGraph/Walks/Basic.olean' of module Mathlib.Combinatorics.SimpleGraph.Walks.Basic does not exist
unknown namespace `BigOperators`
Unknown identifier `Fin`
Unknown identifier `Fin`
expected token
Unknown constant `CoeFun`
Unknown constant `CoeFun`
unexpected token ':'; expected command
Unknown identifier `List.Vector`
Unknown constant `CoeFun`
Unknown constant `CoeFun`
unexpected token ':'; expected command
unexpected token 'if'; expected term
Unknown constant `CoeFun`
unexpected token '+'; expected ')', ',' or ':'
Unknown constant `CoeFun`
Unknown constant `CoeFun`
Unknown constant `CoeFun`
Unknown constant `CoeFun`
expected token
unknown namespace `MeasureTheory`
unexpected token '*'; expected '}'
Unknown constant `CoeFun`
expected token
expected token
Unknown constant `CoeFun`
expected token
Unknown constant `CoeFun`
expected token
Unknown constant `CoeFun`
expected token
Unknown constant `CoeFun`
expected token
expected token
expected token
expected token
unexpected token 'if'; expected term
Unknown identifier `Percolation.Zd`
unknown namespace `MeasureTheory`
Unknown identifier `Percolation.Zd`
expected token
Unknown constant `CoeFun`
unexpected identifier; expected '|'
Unknown constant `CoeFun`
Unknown identifier `Percolation.Zd`
Unknown constant `CoeFun`
expected token
expected token
expected token
expected token
expected token
Unknown constant `CoeFun`
unknown tactic
Unknown constant `CoeFun`
Unknown identifier `Percolation.Zd`
expected token
Unknown constant `CoeFun`
unknown tactic
Unknown constant `CoeFun`
expected token
Unknown constant `CoeFun`
expected token
Unknown constant `CoeFun`
expected token
Unknown constant `CoeFun`
expected token
Unknown constant `CoeFun`
Unknown identifier `Percolation.Zd`
Unknown constant `CoeFun`
Unknown identifier `Prob.Edge`
unknown tactic
Unknown constant `CoeFun`
expected token
Unknown constant `CoeFun`
Unknown constant `CoeFun`
expected token
Unknown constant `CoeFun`
expected token
expected token
Unknown constant `CoeFun`
unknown tactic
Unknown constant `CoeFun`
unknown tactic
Unknown constant `CoeFun`
unknown tactic
Unknown constant `CoeFun`
expected token
expected token
Unknown constant `CoeFun`
expected token
Unknown constant `CoeFun`
unknown tactic
Unknown constant `CoeFun`
unknown tactic
Unknown constant `CoeFun`
expected token
expected token
expected token
expected token
expected token
unknown namespace `BigOperators`
unknown namespace `MeasureTheory`
unexpected token '*'; expected ')'
unexpected token '*'; expected '}'
Unknown constant `CoeFun`
expected token
Unknown constant `CoeFun`
expected token
Unknown constant `CoeFun`
expected token
expected token
expected token
unexpected token 'have'; expected '{' or tactic
Unknown constant `CoeFun`
expected token
unknown namespace `BigOperators`
unknown namespace `MeasureTheory`
unexpected token '*'; expected '}'
unexpected token '*'; expected '}'
unexpected token '*'; expected ')'
expected token
Unknown constant `CoeFun`
Unknown constant `CoeFun`
expected token
expected token
Unknown constant `CoeFun`
Unknown constant `Lean.TrailingParserDescr`
invalid syntax node kind `Percolation.BKR.«term_⊠_»`
unexpected token ':'; expected command
unexpected identifier; expected 'abbrev', 'axiom', 'binder_predicate', 'builtin_initialize', 'class', 'def', 'elab', 'elab_rules', 'example', 'inductive', 'infix', 'infixl', 'infixr', 'initialize', 'instance', 'macro', 'macro_rules', 'notation', 'opaque', 'postfix', 'prefix', 'structure', 'syntax' or 'theorem'
unknown namespace `MeasureTheory`
unexpected token '*'; expected '}'
unexpected token '*'; expected '}'
expected token
unknown namespace `ProbabilityTheory`
unexpected token '*'; expected '}'
expected token
expected token
expected token
expected token
expected token
unknown namespace `MeasureTheory`
unexpected token '*'; expected '}'
expected token
expected token
expected token
expected token
expected token
Unknown identifier `Percolation.Zd`
Unknown constant `CoeFun`
Unknown identifier `Prob.Edge`
expected token
Unknown constant `CoeFun`
expected token
Unknown constant `CoeFun`
unknown tactic
Unknown constant `CoeFun`
Unknown constant `CoeSort`
expected token
expected token
expected token
expected token
expected token
expected token
expected token
expected token
expected token
expected token
Unknown identifier `CriticalProbability.p_c`
expected token
Unknown identifier `CriticalProbability.p_c`
-/

import Mathlib

import percolation.PercolationZd
import KignmanSubadditiveErgodic.KSE

open scoped BigOperators
open scoped Topology

namespace FPP

noncomputable section

variable {d : ℕ}

/-- The vertex set `Z^d`, represented as functions `Fin d → ℤ`. -/
abbrev Zd (d : ℕ) : Type := Fin d → ℤ

/-- The ambient space `R^d`, represented as functions `Fin d → ℝ`. -/
abbrev Rd (d : ℕ) : Type := Fin d → ℝ

/-- Coordinatewise floor map `R^d → Z^d`. -/
def floorZd (x : Rd d) : Zd d := fun i => Int.floor (x i)

/-- Nearest-neighbor relation on `Z^d`. -/
def IsNN (x y : Zd d) : Prop :=
  ∃ i : Fin d, (∀ j : Fin d, j ≠ i → x j = y j) ∧ (y i = x i + 1 ∨ y i = x i - 1)

/-- Edge weights on oriented pairs of vertices (no symmetry assumed). -/
abbrev Weights (d : ℕ) : Type := Zd d → Zd d → ℝ≥0∞

/-- A self-avoiding nearest-neighbor path in `Z^d`, encoded as a list of vertices.

`adj` says successive vertices are nearest-neighbors.
`nodup` says the vertex list is self-avoiding.
-/
structure SAPath (d : ℕ) where
  verts : List (Zd d)
  nonempty : verts ≠ []
  adj : verts.Chain' (IsNN (d := d))
  nodup : verts.Nodup

namespace SAPath

variable {d : ℕ}

/-- Start vertex of a path. -/
def start (γ : SAPath d) : Zd d := γ.verts.head!

/-- End vertex of a path. -/
def finish (γ : SAPath d) : Zd d := γ.verts.getLast γ.nonempty

/-- The oriented edge list of consecutive vertex pairs. -/
def edges (γ : SAPath d) : List (Zd d × Zd d) :=
  γ.verts.zip γ.verts.tail

/-- The number of edges in the path. -/
def edgeLength (γ : SAPath d) : ℕ := γ.edges.length

/-- Passage time of a path for a given weight function. -/
def time (w : Weights d) (γ : SAPath d) : ℝ≥0∞ :=
  (γ.edges.map (fun e => w e.1 e.2)).sum

/-- The set of self-avoiding paths from `x` to `y`. -/
def Between (x y : Zd d) : Set (SAPath d) :=
  {γ | γ.start = x ∧ γ.finish = y}

end SAPath

/-- First-passage time on `Z^d`: infimum of passage times over self-avoiding paths. -/
def passageTimeZd (w : Weights d) (x y : Zd d) : ℝ≥0∞ :=
  sInf (Set.image (SAPath.time (d := d) w) (SAPath.Between (d := d) x y))

/-- First-passage time on `R^d × R^d` defined by flooring coordinates. -/
def passageTimeRd (w : Weights d) (x y : Rd d) : ℝ≥0∞ :=
  passageTimeZd (d := d) w (floorZd (d := d) x) (floorZd (d := d) y)

/-- Geodesics in `Z^d`: self-avoiding paths from `x` to `y` attaining the passage time. -/
def GeodesicsZd (w : Weights d) (x y : Zd d) : Set (SAPath d) :=
  {γ | γ ∈ SAPath.Between (d := d) x y ∧ SAPath.time (d := d) w γ = passageTimeZd (d := d) w x y}

/-- Geodesics in `R^d`, defined by flooring the endpoints. -/
def GeodesicsRd (w : Weights d) (x y : Rd d) : Set (SAPath d) :=
  GeodesicsZd (d := d) w (floorZd (d := d) x) (floorZd (d := d) y)

/-- Subadditivity of passage times on `Z^d`. -/
theorem passageTimeZd_subadditive (w : Weights d) (x y z : Zd d) :
    passageTimeZd (d := d) w x z ≤ passageTimeZd (d := d) w x y + passageTimeZd (d := d) w y z := by
  sorry

/-- Subadditivity of passage times on `R^d` (via flooring). -/
theorem passageTimeRd_subadditive (w : Weights d) (x y z : Rd d) :
    passageTimeRd (d := d) w x z ≤ passageTimeRd (d := d) w x y + passageTimeRd (d := d) w y z := by
  sorry

section Random

open MeasureTheory
open scoped BigOperators

variable {Ω : Type*} [MeasurableSpace Ω]
variable (ℙ : Measure Ω) [ProbabilityTheory.IsProbabilityMeasure ℙ]

/-- A random environment: `ω ↦ weight function` on oriented edges. -/
abbrev Env (d : ℕ) (Ω : Type*) : Type := Ω → Weights d

variable (τ : Env d Ω)

/-- Placeholder for the usual i.i.d. assumptions on edge weights. -/
def IIDWeights : Prop := True

/-- Placeholder for stationarity under lattice translations. -/
def Stationary : Prop := True

/-- Placeholder for ergodicity under lattice translations. -/
def Ergodic : Prop := True

/-- The standard basis vector `e_i` in `Z^d`. -/
def stdBasis (i : Fin d) : Zd d := fun j => if j = i then (1 : ℤ) else 0

/-- The weight of the oriented edge from `0` to `± e_i`.

We index the sign by `Bool`: `true` means `+e_i`, `false` means `-e_i`.
-/
def neighborWeight (w : Weights d) (i : Fin d) (sgn : Bool) : ℝ≥0∞ :=
  if sgn then w 0 (stdBasis (d := d) i) else w 0 (-stdBasis (d := d) i)

/-- The minimum of the `2d` weights adjacent to the origin.

This is written as `sInf` of the range so it is defined for all `d`.
When `d ≥ 1`, this agrees with the minimum over the `2d` neighbors.
-/
def minNeighborWeight (w : Weights d) : ℝ≥0∞ :=
  sInf (Set.range (fun p : Fin d × Bool => neighborWeight (d := d) w p.1 p.2))

/-- The integrability hypothesis `E[min_{i=1..2d} τ_i] < ∞`.

We encode it as finiteness of the `lintegral` of the minimum adjacent weight.
-/
def minNeighborIntegrable : Prop :=
  (∫⁻ ω, minNeighborWeight (d := d) (τ ω) ∂ℙ) < ⊤

/-- Random first-passage time on `Z^d`. -/
def Tzd (x y : Zd d) : Ω → ℝ≥0∞ := fun ω => passageTimeZd (d := d) (τ ω) x y

/-- Random first-passage time on `R^d` (via flooring). -/
def Trd (x y : Rd d) : Ω → ℝ≥0∞ := fun ω => passageTimeRd (d := d) (τ ω) x y

/-- Existence of a time constant under an integrability hypothesis.

This is a typical Kingman subadditive ergodic theorem conclusion.
The statement is given for the `R^d` version that uses flooring.
-/
theorem timeConstant_exists
    (hd : 1 ≤ d)
    (hIID : IIDWeights (d := d) (ℙ := ℙ) τ)
    (hStat : Stationary (d := d) (ℙ := ℙ) τ)
    (hErg : Ergodic (d := d) (ℙ := ℙ) τ)
    (hmin : minNeighborIntegrable (d := d) (ℙ := ℙ) τ) :
    ∃ μ : Rd d → ℝ, ∀ x : Rd d,
      (∀ᵐ ω ∂ℙ, Tendsto (fun n : ℕ =>
          (Trd (d := d) (ℙ := ℙ) τ 0 (n • x) ω).toReal / (n : ℝ))
        Filter.atTop (𝓝 (μ x))) := by
  sorry

/-- Event: there exists a self-avoiding path starting at `0` of edge-length `n`
with passage time strictly smaller than `c n`. -/
def FastPathEvent (n : ℕ) (c : ℝ) : Set Ω :=
  {ω | ∃ γ : SAPath d,
      γ.start = 0 ∧ γ.edgeLength = n ∧ SAPath.time (d := d) (τ ω) γ < ENNReal.ofReal (c * n)}

/-- The percolation parameter `p0 := P( τ(0,e₁) = 0 )` as a real number.

This uses a fixed coordinate `i0` built from `hd : 1 ≤ d`.
-/
def pZero (hd : 1 ≤ d) : ℝ :=
  let i0 : Fin d := ⟨0, Nat.lt_of_lt_of_le Nat.zero_lt_one hd⟩
  (ℙ {ω | (τ ω) 0 (stdBasis (d := d) i0) = 0}).toReal

/-- Exponential bound on the probability of very fast self-avoiding paths,
under the subcritical percolation condition `pZero < pcd d`.

The constant `pcd d` is assumed to be defined in `percolation/PercolationZd.lean`.
-/
theorem prob_fastPath_lt_exp
    (hd : 1 ≤ d)
    (hIID : IIDWeights (d := d) (ℙ := ℙ) τ)
    (hsub : pZero (d := d) (ℙ := ℙ) τ hd < pcd d) :
    ∃ c : ℝ, 0 < c ∧ ∀ n : ℕ,
      ℙ (FastPathEvent (d := d) (ℙ := ℙ) τ n c) < ENNReal.ofReal (Real.exp (-c * n)) := by
  sorry

/-- Existence of geodesics as a consequence of an exponential fast-path bound.

The conclusion states that almost surely, for every pair of lattice points `x y`,
there is at least one geodesic from `x` to `y`.
-/
theorem geodesic_exists_of_fastPath_bound
    (hd : 1 ≤ d)
    (hIID : IIDWeights (d := d) (ℙ := ℙ) τ)
    (hbound : ∃ c : ℝ, 0 < c ∧ ∀ n : ℕ,
      ℙ (FastPathEvent (d := d) (ℙ := ℙ) τ n c) < ENNReal.ofReal (Real.exp (-c * n))) :
    ∀ᵐ ω ∂ℙ, ∀ x y : Zd d, (GeodesicsZd (d := d) (τ ω) x y).Nonempty := by
  sorry

end Random

end FPP
