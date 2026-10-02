import Disjoint_paths.Lemmas.Basic

/-!
# A formula-based lattice-path constructor

The geometric cases describe a path by its vertex at time `k`. The
constructor below turns such a formula into the exact list-based
`LatticePath` used by the main statement.
-/

namespace DisjointPaths

def signedBasis {d : ℕ} (i : Fin d) (s : ℤ) : LatticePoint d :=
  fun j => if j = i then s else 0

@[simp] lemma signedBasis_same {d : ℕ} (i : Fin d) (s : ℤ) :
    signedBasis i s i = s := by
  simp [signedBasis]

@[simp] lemma signedBasis_of_ne {d : ℕ} {i j : Fin d} (h : j ≠ i) (s : ℤ) :
    signedBasis i s j = 0 := by
  simp [signedBasis, h]

@[simp] lemma signedBasis_neg {d : ℕ} (i : Fin d) (s : ℤ) :
    signedBasis i (-s) = -signedBasis i s := by
  ext j
  by_cases hji : j = i <;> simp [signedBasis, hji]

lemma nearestNeighbor_add_signedBasis {d : ℕ} (x : LatticePoint d)
    (i : Fin d) (s : ℤ) (hs : Int.natAbs s = 1) :
    NearestNeighbor x (x + signedBasis i s) := by
  classical
  simp only [NearestNeighbor, l1Dist, l1Norm, Pi.add_apply, signedBasis,
    sub_add_cancel_left, Int.natAbs_neg]
  rw [Finset.sum_eq_single i]
  · simpa using hs
  · intro j _ hji
    simp [hji]
  · simp

lemma nearestNeighbor_sub_signedBasis {d : ℕ} (x : LatticePoint d)
    (i : Fin d) (s : ℤ) (hs : Int.natAbs s = 1) :
    NearestNeighbor x (x - signedBasis i s) := by
  convert nearestNeighbor_add_signedBasis x i (-s) (by simpa using hs) using 1
  ext j
  by_cases hji : j = i <;> simp [signedBasis, hji, sub_eq_add_neg]

/-- Build a path with vertices `v 0, ..., v m` from a globally injective
vertex formula and a proof of nearest-neighbor motion at consecutive times.
-/
def LatticePath.ofInjectiveFormula {d : ℕ} (m : ℕ)
    (v : ℕ → LatticePoint d) (hinj : Function.Injective v)
    (hadj : ∀ k < m, NearestNeighbor (v k) (v (k + 1))) : LatticePath d where
  vertices := (List.range (m + 1)).map v
  nonempty := by simp
  adjacent := by
    rw [List.isChain_iff_getElem]
    intro k hk
    simp only [List.length_map, List.length_range] at hk
    simpa using hadj k (by omega)
  nodup := List.Nodup.map hinj List.nodup_range

namespace LatticePath

@[simp] lemma vertices_ofInjectiveFormula {d : ℕ} (m : ℕ)
    (v : ℕ → LatticePoint d) (hinj : Function.Injective v)
    (hadj : ∀ k < m, NearestNeighbor (v k) (v (k + 1))) :
    (ofInjectiveFormula m v hinj hadj).vertices = (List.range (m + 1)).map v := rfl

@[simp] lemma start_ofInjectiveFormula {d : ℕ} (m : ℕ)
    (v : ℕ → LatticePoint d) (hinj : Function.Injective v)
    (hadj : ∀ k < m, NearestNeighbor (v k) (v (k + 1))) :
    (ofInjectiveFormula m v hinj hadj).start = v 0 := by
  simp [ofInjectiveFormula, start]

@[simp] lemma finish_ofInjectiveFormula {d : ℕ} (m : ℕ)
    (v : ℕ → LatticePoint d) (hinj : Function.Injective v)
    (hadj : ∀ k < m, NearestNeighbor (v k) (v (k + 1))) :
    (ofInjectiveFormula m v hinj hadj).finish = v m := by
  simp [ofInjectiveFormula, finish]

@[simp] lemma edgeLength_ofInjectiveFormula {d : ℕ} (m : ℕ)
    (v : ℕ → LatticePoint d) (hinj : Function.Injective v)
    (hadj : ∀ k < m, NearestNeighbor (v k) (v (k + 1))) :
    (ofInjectiveFormula m v hinj hadj).edgeLength = m := by
  simp [ofInjectiveFormula, edgeLength]

lemma mem_vertices_ofInjectiveFormula_iff {d : ℕ} (m : ℕ)
    (v : ℕ → LatticePoint d) (hinj : Function.Injective v)
    (hadj : ∀ k < m, NearestNeighbor (v k) (v (k + 1)))
    (x : LatticePoint d) :
    x ∈ (ofInjectiveFormula m v hinj hadj).vertices ↔
      ∃ k ≤ m, v k = x := by
  simp [ofInjectiveFormula, Nat.lt_succ_iff]

end LatticePath

end DisjointPaths
