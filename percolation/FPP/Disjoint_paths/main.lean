import Mathlib
import percolation.FPP.FPP_Basics

open scoped BigOperators

namespace FPP
namespace DisjointPaths

noncomputable section

variable {d : ℕ}

/-- The ℓ¹ norm on `ℤ^d`, valued in `ℕ`. -/
def l1NormNat (x : Zd d) : ℕ :=
  ∑ i : Fin d, Int.natAbs (x i)

/-- The discrete sphere (shell) `∂D_n = {x : ℤ^d : ‖x‖₁ = n}`. -/
def boundary (n : ℕ) : Set (Zd d) :=
  {x | l1NormNat (d := d) x = n}

/-- Coordinates of `x` that are nonzero. -/
def nonzeroCoords (x : Zd d) : Finset (Fin d) :=
  Finset.univ.filter (fun i => x i ≠ 0)

/-- Axis points `± n e_i` in `ℤ^d`. -/
def IsAxisPoint (n : ℕ) (x : Zd d) : Prop :=
  ∃ i : Fin d,
    x = ((n : ℤ) • Percolation.Zd.e i) ∨ x = ((-(n : ℤ)) • Percolation.Zd.e i)

/-- ℓ¹ distance in `ℤ^d`. -/
def l1Dist (x y : Zd d) : ℕ :=
  ∑ i : Fin d, Int.natAbs (x i - y i)

/-- A path stays in `∂D_n ∪ ∂D_{n+1}`. -/
def PathStaysInShells (n : ℕ) (γ : SAPath d) : Prop :=
  ∀ v ∈ γ.verts, v ∈ boundary (d := d) n ∪ boundary (d := d) (n + 1)

/-- Length window from the blueprint. -/
def PathLengthBetween (n : ℕ) (δ : ℝ) (γ : SAPath d) : Prop :=
  Nat.floor (δ ^ (3 : ℕ) * (n + 1 : ℝ)) ≤ γ.edgeLength ∧
    γ.edgeLength ≤ Nat.floor (2 * (d : ℝ) * δ ^ (2 : ℕ) * (n + 1 : ℝ))

/-- Endpoint of `γ` is at least `m` away from all vertices of `γ'` in ℓ¹ distance. -/
def EndpointFarFromPath (m : ℕ) (γ γ' : SAPath d) : Prop :=
  ∀ v ∈ γ'.verts, m ≤ l1Dist (d := d) γ.finish v

/-- Oriented edge set of a path. -/
def edgeSet (γ : SAPath d) : Finset (Zd d × Zd d) :=
  γ.edges.toFinset

/-- Two paths are edge-disjoint (as oriented edges). -/
def EdgeDisjoint (γ γ' : SAPath d) : Prop :=
  Disjoint (edgeSet (d := d) γ) (edgeSet (d := d) γ')

axiom path_separation
    (d : ℕ) (n : ℕ) (δ : ℝ) (i : Fin d)
    (γ γ' : SAPath d)
    (hδ : δ ≤ (6 * d + 1 : ℝ)⁻¹)
    (hlenγ : Nat.floor (δ ^ (2 : ℕ) * (n + 1 : ℝ)) ≤ γ.edgeLength)
    (hlenγ' : Nat.floor (δ ^ (2 : ℕ) * (n + 1 : ℝ)) ≤ γ'.edgeLength)
    (hps1 : Prop)
    (hps2 : Prop)
    (hps3 : Prop) :
    EndpointFarFromPath (d := d) (Nat.floor (δ ^ (3 : ℕ) * (n + 1 : ℝ))) γ γ'

/--
Blueprint lemma `lem:2d-2` (formal skeleton): construction of many edge-disjoint
paths from `x_n` and `x_{n+1}` with shell/length/separation constraints.
-/
axiom exists_disjoint_paths_2d_sub
    (d : ℕ) (hd : 3 ≤ d)
    (n : ℕ)
    (x_n : Zd d) (x_np1 : Zd d)
    (hx_n : x_n ∈ boundary (d := d) n)
    (hx_np1 : x_np1 ∈ boundary (d := d) (n + 1))
    (r : Fin d)
    (hOppositeSign : x_n r * x_np1 r < 0)
    (k : ℕ)
    (hk : k ≤ d)
    (hSupportXn : ∀ i : Fin d, k ≤ i.1 → x_n i = 0)
    (δ : ℝ)
    (hδ : δ ≤ (8 * d : ℝ)⁻¹) :
    ∃ (m_n m_np1 : ℕ) (Γn : Fin m_n → SAPath d) (Γnp1 : Fin m_np1 → SAPath d),
      (¬ IsAxisPoint (d := d) n x_n →
          m_n = 2 * d - (nonzeroCoords (d := d) x_n).card - 1) ∧
      (IsAxisPoint (d := d) n x_n → m_n = 2 * d - 3) ∧
      (¬ IsAxisPoint (d := d) (n + 1) x_np1 →
          m_np1 = (nonzeroCoords (d := d) x_np1).card - 1) ∧
      (IsAxisPoint (d := d) (n + 1) x_np1 → m_np1 = 1) ∧
      (∀ a, (Γn a).start = x_n) ∧
      (∀ b, (Γnp1 b).start = x_np1) ∧
      (let Γ : Fin m_n ⊕ Fin m_np1 → SAPath d := Sum.elim Γn Γnp1
       Pairwise (fun a b => EdgeDisjoint (d := d) (Γ a) (Γ b))) ∧
      (∀ a, PathStaysInShells (d := d) n (Γn a)) ∧
      (∀ b, PathStaysInShells (d := d) n (Γnp1 b)) ∧
      (∀ a, PathLengthBetween (d := d) n δ (Γn a)) ∧
      (∀ b, PathLengthBetween (d := d) n δ (Γnp1 b)) ∧
      (let Γ : Fin m_n ⊕ Fin m_np1 → SAPath d := Sum.elim Γn Γnp1
       ∀ a b, a ≠ b →
         EndpointFarFromPath
           (d := d) (Nat.floor (δ ^ (3 : ℕ) * (n + 1 : ℝ)))
           (Γ a) (Γ b))

end

end DisjointPaths
end FPP
