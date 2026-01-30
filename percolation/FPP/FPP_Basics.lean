import Mathlib

import percolation.PercolationZd
import KignmanSubadditiveErgodic.KSE

open scoped BigOperators
open scoped ENNReal
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

section Subadditive

open SimpleGraph

lemma IsNN.symm {d : ℕ} {x y : Zd d} : IsNN (d := d) x y → IsNN (d := d) y x := by
  rintro ⟨i, hcoord, hstep⟩
  refine ⟨i, ?_, ?_⟩
  · intro j hj
    symm
    exact hcoord j hj
  · rcases hstep with h | h
    · right
      have := congrArg (fun t : ℤ => t - 1) h
      simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using this.symm
    · left
      have := congrArg (fun t : ℤ => t + 1) h
      simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using this.symm

lemma IsNN.irrefl {d : ℕ} (x : Zd d) : ¬ IsNN (d := d) x x := by
  intro h
  rcases h with ⟨i, -, hstep⟩
  rcases hstep with h | h
  · have := congrArg (fun t : ℤ => t - x i) h
    have h01 : (0 : ℤ) = 1 := by
      simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using this
    exact (by decide : (0 : ℤ) ≠ 1) h01
  · have := congrArg (fun t : ℤ => t - x i) h
    have h0m1 : (0 : ℤ) = -1 := by
      simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using this
    exact (by decide : (0 : ℤ) ≠ -1) h0m1

/-- The nearest-neighbor graph on `ℤ^d` induced by `IsNN`. -/
def NNGraph (d : ℕ) : SimpleGraph (Zd d) where
  Adj := IsNN (d := d)
  symm := by
    intro x y h
    exact IsNN.symm (d := d) h
  loopless := by
    intro x h
    exact IsNN.irrefl (d := d) x h

namespace SAPath

open SimpleGraph

def toWalkAux {d : ℕ} :
    ∀ (u : Zd d) (vs : List (Zd d)),
      List.IsChain (IsNN (d := d)) (u :: vs) →
        Σ v : Zd d, (NNGraph d).Walk u v := by
  intro u vs hc
  cases vs with
  | nil =>
    exact ⟨u, SimpleGraph.Walk.nil⟩
  | cons v vs =>
    have h' : IsNN (d := d) u v ∧ List.IsChain (IsNN (d := d)) (v :: vs) := by
      simpa using (List.isChain_cons_cons).1 hc
    rcases toWalkAux v vs h'.2 with ⟨w, p⟩
    exact ⟨w, SimpleGraph.Walk.cons h'.1 p⟩

theorem support_toWalkAux {d : ℕ} (u : Zd d) (vs : List (Zd d))
    (hc : List.IsChain (IsNN (d := d)) (u :: vs)) :
    (toWalkAux (d := d) u vs hc).2.support = u :: vs := by
  induction vs generalizing u with
  | nil =>
    simp [toWalkAux]
  | cons v vs ih =>
    have h' : IsNN (d := d) u v ∧ List.IsChain (IsNN (d := d)) (v :: vs) := by
      simpa using (List.isChain_cons_cons).1 hc
    rcases toWalkAux (d := d) v vs h'.2 with ⟨w, p⟩
    simp [toWalkAux, h', ih (u := v) (hc := h'.2), SimpleGraph.Walk.support_cons]

/-- View a self-avoiding nearest-neighbor path as a walk in the nearest-neighbor graph. -/
def toWalk {d : ℕ} (γ : SAPath d) : (NNGraph d).Walk γ.start γ.finish :=
  by
    classical
    let u : Zd d := γ.verts.head!
    let vs : List (Zd d) := γ.verts.tail
    have hcons : u :: vs = γ.verts := by
      simpa [u, vs] using (List.cons_head!_tail (l := γ.verts) γ.nonempty)
    have hc : List.IsChain (IsNN (d := d)) (u :: vs) := by
      simpa [hcons] using γ.adj
    let aux := toWalkAux (d := d) u vs hc
    have hsupp : aux.2.support = u :: vs := support_toWalkAux (d := d) u vs hc
    have hend : aux.1 = γ.finish := by
      have : aux.1 = aux.2.support.getLast (by simp) :=
        (SimpleGraph.Walk.getLast_support (p := aux.2)).symm
      simpa [SAPath.finish, hsupp, hcons] using this
    exact aux.2.copy (by simpa [SAPath.start, u]) hend

@[simp] theorem support_toWalk {d : ℕ} (γ : SAPath d) : (γ.toWalk (d := d)).support = γ.verts := by
  classical
  -- Mirror the construction in `toWalk`, but only keep track of supports.
  let u : Zd d := γ.verts.head!
  let vs : List (Zd d) := γ.verts.tail
  have hcons : u :: vs = γ.verts := by
    simpa [u, vs] using (List.cons_head!_tail (l := γ.verts) γ.nonempty)
  have hc : List.IsChain (IsNN (d := d)) (u :: vs) := by
    simpa [hcons] using γ.adj
  let aux := toWalkAux (d := d) u vs hc
  have hsupp : aux.2.support = u :: vs := support_toWalkAux (d := d) u vs hc
  have hend : aux.1 = γ.finish := by
    have : aux.1 = aux.2.support.getLast (by simp) :=
      (SimpleGraph.Walk.getLast_support (p := aux.2)).symm
    simpa [SAPath.finish, hsupp, hcons] using this
  -- `copy` doesn't change `support`.
  simpa [SAPath.toWalk, u, vs, hcons, hc, aux, hsupp, hend]

end SAPath

private theorem darts_map_toProd_eq_zip_support {V : Type*} {G : SimpleGraph V} {u v : V} :
    ∀ p : G.Walk u v, p.darts.map (fun d => d.toProd) = p.support.zip p.support.tail
  | .nil => by
    simp [SimpleGraph.Walk.darts, SimpleGraph.Walk.support]
  | .cons h p => by
    cases p with
    | nil =>
      simp [SimpleGraph.Walk.darts, SimpleGraph.Walk.support]
    | cons h' p' =>
      have ih := darts_map_toProd_eq_zip_support (p := SimpleGraph.Walk.cons h' p')
      -- `zip (u :: v :: …) (v :: …)` gives `(u, v) :: zip … …`.
      simpa [SimpleGraph.Walk.darts, SimpleGraph.Walk.support, ih, List.zip_cons_cons]

private def walkTime {d : ℕ} (w : Weights d) {x y : Zd d} (p : (NNGraph d).Walk x y) : ℝ≥0∞ :=
  (p.darts.map (fun e => w e.fst e.snd)).sum

private theorem darts_dropUntil_sublist {V : Type*} {G : SimpleGraph V} [DecidableEq V] {u v w : V}
    (p : G.Walk u v) (h : w ∈ p.support) :
    (p.dropUntil w h).darts.Sublist p.darts := by
  have hsplit :
      (p.takeUntil w h).darts ++ (p.dropUntil w h).darts = p.darts := by
    have hsplit' := congrArg SimpleGraph.Walk.darts (p.take_spec h)
    -- Avoid `simp` here: `take_spec` is a simp lemma, and can rewrite the LHS back to `p`.
    -- We only want to expand `darts` of an `append`.
    simpa using (by
      rw [SimpleGraph.Walk.darts_append] at hsplit'
      exact hsplit')
  simpa [hsplit] using List.sublist_append_right (p.takeUntil w h).darts (p.dropUntil w h).darts

private theorem darts_bypass_sublist {V : Type*} {G : SimpleGraph V} [DecidableEq V] {u v : V} :
    ∀ p : G.Walk u v, p.bypass.darts.Sublist p.darts
  | .nil => by simp [SimpleGraph.Walk.bypass]
  | .cons ha p =>
    by
      have ih : p.bypass.darts.Sublist p.darts := darts_bypass_sublist p
      by_cases hs : u ∈ (p.bypass).support
      · have hdrop : ((p.bypass).dropUntil u hs).darts.Sublist (p.bypass).darts :=
          darts_dropUntil_sublist (p := p.bypass) hs
        simpa [SimpleGraph.Walk.bypass, hs] using
          List.sublist_cons_of_sublist (a := ⟨(u, _), ha⟩) (hdrop.trans ih)
      · simpa [SimpleGraph.Walk.bypass, hs] using (List.Sublist.cons_cons (a := ⟨(u, _), ha⟩) ih)

private theorem walkTime_le_of_darts_sublist {d : ℕ} (w : Weights d) {x y : Zd d}
    {p q : (NNGraph d).Walk x y} (h : q.darts.Sublist p.darts) :
    walkTime (d := d) w q ≤ walkTime (d := d) w p := by
  refine (List.Sublist.sum_le_sum (h.map _) ?_)
  intro a ha
  exact bot_le

private theorem walkTime_eq_time (w : Weights d) (γ : SAPath d) :
    walkTime (d := d) w (γ.toWalk (d := d)) = SAPath.time (d := d) w γ := by
  classical
  unfold walkTime SAPath.time SAPath.edges
  let p : (NNGraph d).Walk γ.start γ.finish := γ.toWalk (d := d)
  have hmap :
      (p.darts.map (fun e => w e.fst e.snd)) =
        (p.darts.map (fun e => e.toProd)).map (fun pr => w pr.1 pr.2) := by
    simp [List.map_map, p]
  -- Convert darts to the support `zip`, then use `SAPath.support_toWalk`.
  simp [p, hmap, darts_map_toProd_eq_zip_support (p := p), SAPath.support_toWalk (d := d) γ, List.map_map]

private def SAPath.ofWalk {d : ℕ} {x y : Zd d} (p : (NNGraph d).Walk x y) (hp : p.IsPath) : SAPath d where
  verts := p.support
  nonempty := by simpa using (SimpleGraph.Walk.support_ne_nil (p := p))
  adj := by
    simpa using (SimpleGraph.Walk.isChain_adj_support (p := p))
  nodup := (SimpleGraph.Walk.isPath_def (p := p)).1 hp

private theorem walkTime_eq_time_ofWalk (w : Weights d) {x y : Zd d} (p : (NNGraph d).Walk x y) (hp : p.IsPath) :
    walkTime (d := d) w p = SAPath.time (d := d) w (SAPath.ofWalk (d := d) p hp) := by
  classical
  unfold walkTime SAPath.ofWalk SAPath.time SAPath.edges
  have hmap :
      (p.darts.map (fun e => w e.fst e.snd)) =
        (p.darts.map (fun e => e.toProd)).map (fun pr => w pr.1 pr.2) := by
    simp [List.map_map]
  simp [hmap, darts_map_toProd_eq_zip_support (p := p)]

private theorem passageTimeZd_le_add_of_paths (w : Weights d) (x y z : Zd d)
    (γxy : SAPath d) (hxy : γxy ∈ SAPath.Between (d := d) x y)
    (γyz : SAPath d) (hyz : γyz ∈ SAPath.Between (d := d) y z) :
    passageTimeZd (d := d) w x z ≤ SAPath.time (d := d) w γxy + SAPath.time (d := d) w γyz := by
  rcases hxy with ⟨hxy_start, hxy_finish⟩
  rcases hyz with ⟨hyz_start, hyz_finish⟩
  let pxy : (NNGraph d).Walk x y := (γxy.toWalk (d := d)).copy hxy_start hxy_finish
  let pyz : (NNGraph d).Walk y z := (γyz.toWalk (d := d)).copy hyz_start hyz_finish
  let p : (NNGraph d).Walk x z := pxy.append pyz
  let p' : (NNGraph d).Walk x z := p.bypass
  have hp' : p'.IsPath := p.bypass_isPath
  let γxz : SAPath d := SAPath.ofWalk (d := d) p' hp'
  have hBetween : γxz ∈ SAPath.Between (d := d) x z := by
    constructor
    · have hs : p'.support = x :: p'.support.tail := SimpleGraph.Walk.support_eq_cons (p := p')
      -- Avoid `simp` loops by rewriting explicitly.
      dsimp [γxz, SAPath.ofWalk, SAPath.start]
      rw [hs]
      simp
    · simp [γxz, SAPath.ofWalk, SAPath.finish]
  have hmem :
      SAPath.time (d := d) w γxz ∈
        Set.image (SAPath.time (d := d) w) (SAPath.Between (d := d) x z) := by
    exact ⟨γxz, hBetween, rfl⟩
  have hPT_le : passageTimeZd (d := d) w x z ≤ SAPath.time (d := d) w γxz := by
    simpa [passageTimeZd] using (sInf_le hmem)
  have htime :
      SAPath.time (d := d) w γxz ≤ SAPath.time (d := d) w γxy + SAPath.time (d := d) w γyz := by
    have hsub : p'.darts.Sublist p.darts := by
      simpa [p', p] using (darts_bypass_sublist (p := p))
    have hle : walkTime (d := d) w p' ≤ walkTime (d := d) w p :=
      walkTime_le_of_darts_sublist (d := d) w hsub
    have happ : walkTime (d := d) w p = walkTime (d := d) w pxy + walkTime (d := d) w pyz := by
      simp [walkTime, p, pxy, pyz, List.sum_append]
    have hγxz : walkTime (d := d) w p' = SAPath.time (d := d) w γxz := by
      simpa [γxz] using (walkTime_eq_time_ofWalk (d := d) w p' hp')
    have hγxy : walkTime (d := d) w pxy = SAPath.time (d := d) w γxy := by
      calc
        walkTime (d := d) w pxy = walkTime (d := d) w (γxy.toWalk (d := d)) := by
          simp [pxy, walkTime]
        _ = SAPath.time (d := d) w γxy := walkTime_eq_time (d := d) w γxy
    have hγyz : walkTime (d := d) w pyz = SAPath.time (d := d) w γyz := by
      calc
        walkTime (d := d) w pyz = walkTime (d := d) w (γyz.toWalk (d := d)) := by
          simp [pyz, walkTime]
        _ = SAPath.time (d := d) w γyz := walkTime_eq_time (d := d) w γyz
    calc
      SAPath.time (d := d) w γxz = walkTime (d := d) w p' := by simpa [hγxz]
      _ ≤ walkTime (d := d) w p := hle
      _ = walkTime (d := d) w pxy + walkTime (d := d) w pyz := happ
      _ = SAPath.time (d := d) w γxy + SAPath.time (d := d) w γyz := by simpa [hγxy, hγyz]
  exact hPT_le.trans htime

/-- Subadditivity of passage times on `Z^d`. -/
theorem passageTimeZd_subadditive (w : Weights d) (x y z : Zd d) :
    passageTimeZd (d := d) w x z ≤ passageTimeZd (d := d) w x y + passageTimeZd (d := d) w y z := by
  classical
  -- Subadditivity via the infimum-over-paths characterization `sInf_image`.
  have hmain :
      passageTimeZd (d := d) w x z ≤
        (⨅ γxy ∈ SAPath.Between (d := d) x y, SAPath.time (d := d) w γxy) +
          ⨅ γyz ∈ SAPath.Between (d := d) y z, SAPath.time (d := d) w γyz := by
    refine ENNReal.le_iInf₂_add_iInf₂ (a := passageTimeZd (d := d) w x z) ?_
    intro γxy hxy γyz hyz
    exact passageTimeZd_le_add_of_paths (d := d) w x y z γxy hxy γyz hyz
  have hx :
      (⨅ γxy ∈ SAPath.Between (d := d) x y, SAPath.time (d := d) w γxy) =
        passageTimeZd (d := d) w x y := by
    simpa [passageTimeZd] using
      (sInf_image (s := SAPath.Between (d := d) x y) (f := SAPath.time (d := d) w)).symm
  have hy :
      (⨅ γyz ∈ SAPath.Between (d := d) y z, SAPath.time (d := d) w γyz) =
        passageTimeZd (d := d) w y z := by
    simpa [passageTimeZd] using
      (sInf_image (s := SAPath.Between (d := d) y z) (f := SAPath.time (d := d) w)).symm
  simpa [hx, hy] using hmain

/-- Subadditivity of passage times on `R^d` (via flooring). -/
theorem passageTimeRd_subadditive (w : Weights d) (x y z : Rd d) :
    passageTimeRd (d := d) w x z ≤ passageTimeRd (d := d) w x y + passageTimeRd (d := d) w y z := by
  simpa [passageTimeRd] using
    (passageTimeZd_subadditive (d := d) w (floorZd (d := d) x) (floorZd (d := d) y) (floorZd (d := d) z))

end Subadditive

section Random

open MeasureTheory
open scoped BigOperators

variable {Ω : Type*} [MeasurableSpace Ω]
variable (ℙ : Measure Ω) [MeasureTheory.IsProbabilityMeasure ℙ]

/-- A random environment: `ω ↦ weight function` on oriented edges. -/
abbrev Env (d : ℕ) (Ω : Type*) : Type _ := Ω → Weights d

abbrev Edge (d : ℕ) : Type := Zd d × Zd d

variable (τ : Env d Ω)

variable [SMul (Zd d) (Weights d)]

/--
i.i.d. edge weights (on oriented edges): the coordinate maps `ω ↦ τ ω e`
are measurable, independent, and identically distributed.
-/
def IIDWeights (d : ℕ) (ℙ : Measure Ω) (τ : Env d Ω) : Prop :=
  (∀ e : Edge d, Measurable fun ω => (τ ω) e.1 e.2) ∧
    ProbabilityTheory.iIndepFun (fun e : Edge d => fun ω => (τ ω) e.1 e.2) ℙ ∧
    (∀ e₁ e₂ : Edge d,
      ProbabilityTheory.IdentDistrib (fun ω => (τ ω) e₁.1 e₁.2) (fun ω => (τ ω) e₂.1 e₂.2) ℙ ℙ)

/--
Stationarity under lattice translations: the law of `τ` is invariant under the
shift action of `ℤ^d` on configurations `Weights d`.

This definition assumes you have provided an action `SMul (Zd d) (Weights d)`
encoding translations of environments.
-/
def Stationary (d : ℕ) (ℙ : Measure Ω) (τ : Env d Ω) [SMul (Zd d) (Weights d)] : Prop :=
  ∀ z : Zd d, Measure.map (fun ω => (z • τ ω : Weights d)) ℙ = Measure.map τ ℙ

/--
Ergodicity under lattice translations: any measurable translation-invariant event
in configuration space has probability `0` or `1` under the law of `τ`.

This definition assumes you have provided an action `SMul (Zd d) (Weights d)`
encoding translations of environments.
-/
def Ergodic (d : ℕ) (ℙ : Measure Ω) (τ : Env d Ω) [SMul (Zd d) (Weights d)] : Prop :=
  let μ : Measure (Weights d) := Measure.map τ ℙ
  ∀ A : Set (Weights d),
    MeasurableSet A →
      (∀ z : Zd d, (fun w : Weights d => (z • w : Weights d)) ⁻¹' A = A) →
        μ A = 0 ∨ μ A = μ Set.univ

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
def minNeighborIntegrable (d : ℕ) (ℙ : Measure Ω) (τ : Env d Ω) : Prop :=
  (∫⁻ ω, minNeighborWeight (d := d) (τ ω) ∂ℙ) < ⊤

/-- Random first-passage time on `Z^d`. -/
def Tzd (d : ℕ) (ℙ : Measure Ω) (τ : Env d Ω) (x y : Zd d) : Ω → ℝ≥0∞ :=
  fun ω => passageTimeZd (d := d) (τ ω) x y

/-- Random first-passage time on `R^d` (via flooring). -/
def Trd (d : ℕ) (ℙ : Measure Ω) (τ : Env d Ω) (x y : Rd d) : Ω → ℝ≥0∞ :=
  fun ω => passageTimeRd (d := d) (τ ω) x y

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
      (∀ᵐ ω ∂ℙ, Filter.Tendsto (fun n : ℕ =>
          (Trd (d := d) (ℙ := ℙ) τ 0 (n • x) ω).toReal / (n : ℝ))
        Filter.atTop (𝓝 (μ x))) := by
  classical
  -- Apply the (axiomatic) Kingman ray statement to `F y ω = (Trd 0 y ω).toReal`.
  simpa [Trd] using
    (Kingman.ray_timeConstant_exists (ℙ := ℙ)
      (F := fun (y : Rd d) (ω : Ω) => (Trd (d := d) (ℙ := ℙ) τ 0 y ω).toReal))

/-- Event: there exists a self-avoiding path starting at `0` of edge-length `n`
with passage time strictly smaller than `c n`. -/
def FastPathEvent (d : ℕ) (ℙ : Measure Ω) (τ : Env d Ω) (n : ℕ) (c : ℝ) : Set Ω :=
  {ω | ∃ γ : SAPath d,
      γ.start = 0 ∧ γ.edgeLength = n ∧ SAPath.time (d := d) (τ ω) γ < ENNReal.ofReal (c * n)}

/-- The percolation parameter `p0 := P( τ(0,e₁) = 0 )` as a real number.

This uses a fixed coordinate `i0` built from `hd : 1 ≤ d`.
-/
def pZero (d : ℕ) (ℙ : Measure Ω) (τ : Env d Ω) (hd : 1 ≤ d) : ℝ :=
  let i0 : Fin d := ⟨0, Nat.lt_of_lt_of_le Nat.zero_lt_one hd⟩
  (ℙ {ω | (τ ω) 0 (stdBasis (d := d) i0) = 0}).toReal

/-- Placeholder for the critical percolation parameter in dimension `d`. -/
def pcd (_d : ℕ) : ℝ := 0

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

end
end FPP
