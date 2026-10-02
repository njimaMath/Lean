import Disjoint_paths.Lemmas.Basic

/-!
# Coordinatewise reflections

The geometric construction may be normalized to convenient signs.  This file
proves that coordinatewise multiplication by signs transports every object and
property used in the final statement.
-/

namespace DisjointPaths

def reflect {d : ℕ} (s : Fin d → ℤ) (x : LatticePoint d) : LatticePoint d :=
  fun i ↦ s i * x i

variable {d : ℕ} {s : Fin d → ℤ}

@[simp] lemma reflect_apply (x : LatticePoint d) (i : Fin d) :
    reflect s x i = s i * x i := rfl

lemma sign_ne_zero (hs : ∀ i, Int.natAbs (s i) = 1) (i : Fin d) : s i ≠ 0 := by
  intro h
  simpa [h] using hs i

lemma reflect_injective (hs : ∀ i, Int.natAbs (s i) = 1) :
    Function.Injective (reflect s : LatticePoint d → LatticePoint d) := by
  intro x y hxy
  funext i
  have hi := congrFun hxy i
  exact mul_left_cancel₀ (sign_ne_zero hs i) hi

@[simp] lemma reflect_reflect (hs : ∀ i, Int.natAbs (s i) = 1)
    (x : LatticePoint d) : reflect s (reflect s x) = x := by
  funext i
  have hsq : s i * s i = 1 := by
    rcases Int.natAbs_eq_iff.mp (hs i) with h | h <;> simp [h]
  simp [reflect, ← mul_assoc, hsq]

@[simp] lemma l1Norm_reflect (hs : ∀ i, Int.natAbs (s i) = 1)
    (x : LatticePoint d) : l1Norm (reflect s x) = l1Norm x := by
  simp [l1Norm, reflect, Int.natAbs_mul, hs]

@[simp] lemma l1Dist_reflect (hs : ∀ i, Int.natAbs (s i) = 1)
    (x y : LatticePoint d) : l1Dist (reflect s x) (reflect s y) = l1Dist x y := by
  simp only [l1Dist]
  have hpoint : (fun i ↦ s i * x i - s i * y i) =
      reflect s (fun i ↦ x i - y i) := by
    funext i
    simp [reflect, mul_sub]
  change l1Norm (fun i ↦ s i * x i - s i * y i) = _
  rw [hpoint, l1Norm_reflect hs]

@[simp] lemma reflect_mem_sphere_iff (hs : ∀ i, Int.natAbs (s i) = 1)
    {n : ℕ} {x : LatticePoint d} : reflect s x ∈ sphere d n ↔ x ∈ sphere d n := by
  simp [sphere, l1Norm_reflect hs]

@[simp] lemma nearestNeighbor_reflect_iff (hs : ∀ i, Int.natAbs (s i) = 1)
    {x y : LatticePoint d} :
    NearestNeighbor (reflect s x) (reflect s y) ↔ NearestNeighbor x y := by
  simp [NearestNeighbor, l1Dist_reflect hs]

@[simp] lemma supportCard_reflect (hs : ∀ i, Int.natAbs (s i) = 1)
    (x : LatticePoint d) : supportCard (reflect s x) = supportCard x := by
  classical
  unfold supportCard
  apply congrArg Finset.card
  ext i
  simp [reflect, sign_ne_zero hs i]

lemma isAxisPoint_reflect_iff (hs : ∀ i, Int.natAbs (s i) = 1)
    {n : ℕ} {x : LatticePoint d} :
    IsAxisPoint n (reflect s x) ↔ IsAxisPoint n x := by
  have hforward : ∀ z : LatticePoint d, IsAxisPoint n z → IsAxisPoint n (reflect s z) := by
    intro z
    rintro ⟨i, hi | hi⟩
    · rcases Int.natAbs_eq_iff.mp (hs i) with hsign | hsign
      · refine ⟨i, Or.inl ?_⟩
        funext j
        rw [hi]
        by_cases hji : j = i <;> simp [reflect, hji, hsign]
      · refine ⟨i, Or.inr ?_⟩
        funext j
        rw [hi]
        by_cases hji : j = i <;> simp [reflect, hji, hsign]
    · rcases Int.natAbs_eq_iff.mp (hs i) with hsign | hsign
      · refine ⟨i, Or.inr ?_⟩
        funext j
        rw [hi]
        by_cases hji : j = i <;> simp [reflect, hji, hsign]
      · refine ⟨i, Or.inl ?_⟩
        funext j
        rw [hi]
        by_cases hji : j = i <;> simp [reflect, hji, hsign]
  constructor
  · intro h
    have h' := hforward (reflect s x) h
    simpa [reflect_reflect hs] using h'
  · exact hforward x

@[simp] lemma pathCountAtInner_reflect (hs : ∀ i, Int.natAbs (s i) = 1)
    (n : ℕ) (x : LatticePoint d) :
    pathCountAtInner n (reflect s x) = pathCountAtInner n x := by
  classical
  rw [pathCountAtInner, pathCountAtInner, supportCard_reflect hs]
  exact if_congr (isAxisPoint_reflect_iff hs) rfl rfl

@[simp] lemma pathCountAtOuter_reflect (hs : ∀ i, Int.natAbs (s i) = 1)
    (n : ℕ) (x : LatticePoint d) :
    pathCountAtOuter n (reflect s x) = pathCountAtOuter n x := by
  classical
  rw [pathCountAtOuter, pathCountAtOuter, supportCard_reflect hs]
  exact if_congr (isAxisPoint_reflect_iff hs) rfl rfl

def LatticePath.reflect (hs : ∀ i, Int.natAbs (s i) = 1)
    (p : LatticePath d) : LatticePath d where
  vertices := p.vertices.map (DisjointPaths.reflect s)
  nonempty := by simpa using p.nonempty
  adjacent := by
    have hmap : ∀ l : List (LatticePoint d), l.IsChain NearestNeighbor →
        (l.map (DisjointPaths.reflect s)).IsChain NearestNeighbor := by
      intro l hl
      induction l with
      | nil => simp
      | cons a tail ih =>
          cases tail with
          | nil => simp
          | cons b rest =>
              change List.IsChain NearestNeighbor
                (DisjointPaths.reflect s a :: DisjointPaths.reflect s b ::
                  rest.map (DisjointPaths.reflect s))
              rw [List.isChain_cons_cons]
              rw [List.isChain_cons_cons] at hl
              exact ⟨(nearestNeighbor_reflect_iff hs).mpr hl.1, ih hl.2⟩
    exact hmap p.vertices p.adjacent
  nodup := p.nodup.map (reflect_injective hs)

namespace LatticePath

@[simp] lemma vertices_reflect (hs : ∀ i, Int.natAbs (s i) = 1)
    (p : LatticePath d) : (p.reflect hs).vertices = p.vertices.map (DisjointPaths.reflect s) := rfl

@[simp] lemma start_reflect (hs : ∀ i, Int.natAbs (s i) = 1)
    (p : LatticePath d) : (p.reflect hs).start = DisjointPaths.reflect s p.start := by
  simp [LatticePath.reflect, start]

@[simp] lemma finish_reflect (hs : ∀ i, Int.natAbs (s i) = 1)
    (p : LatticePath d) : (p.reflect hs).finish = DisjointPaths.reflect s p.finish := by
  simp [LatticePath.reflect, finish]

@[simp] lemma edgeLength_reflect (hs : ∀ i, Int.natAbs (s i) = 1)
    (p : LatticePath d) : (p.reflect hs).edgeLength = p.edgeLength := by
  simp [LatticePath.reflect, edgeLength]

lemma mem_vertices_reflect_iff (hs : ∀ i, Int.natAbs (s i) = 1)
    (p : LatticePath d) (x : LatticePoint d) :
    x ∈ (p.reflect hs).vertices ↔ DisjointPaths.reflect s x ∈ p.vertices := by
  constructor
  · intro hx
    rcases List.mem_map.mp hx with ⟨y, hy, rfl⟩
    simpa [reflect_reflect hs] using hy
  · intro hx
    apply List.mem_map.mpr
    exact ⟨DisjointPaths.reflect s x, hx, reflect_reflect hs x⟩

lemma edgeSet_reflect_iff (hs : ∀ i, Int.natAbs (s i) = 1)
    (p : LatticePath d) (e : LatticePoint d × LatticePoint d) :
    e ∈ (p.reflect hs).edgeSet ↔
      (DisjointPaths.reflect s e.1, DisjointPaths.reflect s e.2) ∈ p.edgeSet := by
  have hzip : ∀ (l : List (LatticePoint d)) (e : LatticePoint d × LatticePoint d),
      e ∈ (l.map (DisjointPaths.reflect s)).zip
          (l.map (DisjointPaths.reflect s)).tail ↔
        ∃ a b, (a, b) ∈ l.zip l.tail ∧
          e = (DisjointPaths.reflect s a, DisjointPaths.reflect s b) := by
    intro l
    induction l with
    | nil => simp
    | cons a tail ih =>
        cases tail with
        | nil => simp
        | cons b rest =>
            intro e
            simp only [List.map_cons, List.tail_cons, List.zip_cons_cons, List.mem_cons]
            constructor
            · intro he
              rcases he with rfl | he
              · exact ⟨a, b, by simp, rfl⟩
              · rcases (ih e).mp he with ⟨u, v, huv, rfl⟩
                exact ⟨u, v, Or.inr huv, rfl⟩
            · rintro ⟨u, v, huv, rfl⟩
              rcases huv with huv | huv
              · have hu : u = a := congrArg Prod.fst huv
                have hv : v = b := congrArg Prod.snd huv
                simp [hu, hv]
              · exact Or.inr ((ih _).mpr ⟨u, v, huv, rfl⟩)
  simp only [edgeSet, orientedEdges, vertices_reflect]
  constructor
  · rintro (he | he)
    · rcases (hzip p.vertices e).mp he with ⟨a, b, hab, heq⟩
      left
      have h1 := congrArg Prod.fst heq
      have h2 := congrArg Prod.snd heq
      have h1' : DisjointPaths.reflect s e.1 = a := by
        rw [h1, reflect_reflect hs]
      have h2' : DisjointPaths.reflect s e.2 = b := by
        rw [h2, reflect_reflect hs]
      simpa [h1', h2'] using hab
    · rcases (hzip p.vertices e.swap).mp he with ⟨a, b, hab, heq⟩
      right
      have h1 := congrArg Prod.fst heq
      have h2 := congrArg Prod.snd heq
      have h1c : e.2 = DisjointPaths.reflect s a := by simpa using h1
      have h2c : e.1 = DisjointPaths.reflect s b := by simpa using h2
      have h1' : DisjointPaths.reflect s e.2 = a := by
        rw [h1c, reflect_reflect hs]
      have h2' : DisjointPaths.reflect s e.1 = b := by
        rw [h2c, reflect_reflect hs]
      simpa [h1', h2'] using hab
  · intro he
    rcases he with he | he
    · left
      apply (hzip p.vertices e).mpr
      exact ⟨DisjointPaths.reflect s e.1, DisjointPaths.reflect s e.2,
        he, by simp [reflect_reflect hs]⟩
    · right
      apply (hzip p.vertices e.swap).mpr
      exact ⟨DisjointPaths.reflect s e.2, DisjointPaths.reflect s e.1,
        he, by cases e; simp [reflect_reflect hs, Prod.swap]⟩

lemma edgeDisjoint_reflect_iff (hs : ∀ i, Int.natAbs (s i) = 1)
    (p q : LatticePath d) :
    Disjoint (p.reflect hs).edgeSet (q.reflect hs).edgeSet ↔ Disjoint p.edgeSet q.edgeSet := by
  constructor
  · intro hdisj
    apply Set.disjoint_left.mpr
    intro e hep heq
    have hd := Set.disjoint_left.mp hdisj
    let er : LatticePoint d × LatticePoint d :=
      (DisjointPaths.reflect s e.1, DisjointPaths.reflect s e.2)
    apply hd
    · exact (edgeSet_reflect_iff hs p er).mpr (by
        simpa [er, reflect_reflect hs] using hep)
    · exact (edgeSet_reflect_iff hs q er).mpr (by
        simpa [er, reflect_reflect hs] using heq)
  · intro hdisj
    apply Set.disjoint_left.mpr
    intro e hep heq
    exact (Set.disjoint_left.mp hdisj)
      ((edgeSet_reflect_iff hs p e).mp hep) ((edgeSet_reflect_iff hs q e).mp heq)

end LatticePath

end DisjointPaths
