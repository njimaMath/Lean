import percolation.PercolationZd

open scoped BigOperators ENNReal Topology

namespace Percolation

namespace Bond

namespace Open

open Lattice Prob Geometry

variable {d : ℕ}

/-- The set of lengths (in `WithTop ℕ`) of open walks from `x` to `y` in the configuration `ω`. -/
def openWalkLengths (ω : Set (E (d := d))) (x y : V (d := d)) : Set (WithTop ℕ) :=
  {n | ∃ w : (G (d := d)).Walk x y, WalkAllOpen (d := d) ω w ∧ (w.length : WithTop ℕ) = n}

/-- Chemical distance (graph distance in the open subgraph).

It is the infimum of the lengths of open walks connecting `x` to `y`, with value `⊤` if there is no
open walk. -/
noncomputable def chemicalDist (ω : Set (E (d := d))) (x y : V (d := d)) : WithTop ℕ :=
  sInf (openWalkLengths (d := d) ω x y)

lemma chemicalDist_le_length (ω : Set (E (d := d))) {x y : V (d := d)}
    (w : (G (d := d)).Walk x y) (hw : WalkAllOpen (d := d) ω w) :
    chemicalDist (d := d) ω x y ≤ (w.length : WithTop ℕ) := by
  unfold chemicalDist
  refine sInf_le ?_
  exact ⟨w, hw, rfl⟩

lemma chemicalDist_ne_top_of_openConnected (ω : Set (E (d := d))) {x y : V (d := d)}
    (hconn : OpenConnected (d := d) ω x y) : chemicalDist (d := d) ω x y ≠ ⊤ := by
  rcases hconn with ⟨w, hw⟩
  have hle : chemicalDist (d := d) ω x y ≤ (w.length : WithTop ℕ) :=
    chemicalDist_le_length (d := d) (ω := ω) (w := w) hw
  intro htop
  have : (⊤ : WithTop ℕ) ≤ (w.length : WithTop ℕ) := by
    simpa [htop] using hle
  -- `⊤` cannot be ≤ a finite number.
  simpa using this

theorem chemicalDist_eq_top_iff_not_openConnected (ω : Set (E (d := d))) (x y : V (d := d)) :
    chemicalDist (d := d) ω x y = ⊤ ↔ ¬ OpenConnected (d := d) ω x y := by
  constructor
  · intro hdist hconn
    exact (chemicalDist_ne_top_of_openConnected (d := d) (ω := ω) (x := x) (y := y) hconn) hdist
  · intro hnot
    have hEmpty : openWalkLengths (d := d) ω x y = ∅ := by
      ext n
      constructor
      · intro hn
        rcases hn with ⟨w, hw, rfl⟩
        exact (hnot ⟨w, hw⟩).elim
      · intro hn
        exact False.elim (by simpa using hn)
    simp [chemicalDist, hEmpty]

lemma chemicalDist_self (ω : Set (E (d := d))) (x : V (d := d)) :
    chemicalDist (d := d) ω x x = 0 := by
  apply le_antisymm
  · -- The empty walk is open and has length 0.
    have : (0 : WithTop ℕ) ∈ openWalkLengths (d := d) ω x x := by
      refine ⟨(SimpleGraph.Walk.nil : (G (d := d)).Walk x x), ?_, ?_⟩
      · simp [WalkAllOpen]
      · simp
    simpa [chemicalDist] using (sInf_le this)
  · exact bot_le

end Open

end Bond

end Percolation
