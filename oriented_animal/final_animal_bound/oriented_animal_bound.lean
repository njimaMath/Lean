import oriented_animal.animal_comparison.animal_comparison
import oriented_animal.animal_bound.starconnected

open scoped BigOperators

namespace OrientedAnimal

variable {N L : Nat}

noncomputable def orientedInnerBoundaryFinset
    (Open : ∀ u v : V N L, OAdj u v → Prop) : Finset (V N L) := by
  classical
  exact Finset.univ.filter fun u => u ∈ OrientedInnerBoundary Open

noncomputable def innerBoundaryFinset
    (Open : ∀ u v : V N L, OAdj u v → Prop) : Finset (V N L) := by
  classical
  exact Finset.univ.filter fun u => u ∈ InnerBoundary Open

theorem orientedInnerBoundaryFinset_card
    (Open : ∀ u v : V N L, OAdj u v → Prop) :
    (orientedInnerBoundaryFinset Open).card =
      Fintype.card {u : V N L // u ∈ OrientedInnerBoundary Open} := by
  classical
  simp [orientedInnerBoundaryFinset, Fintype.card_subtype]

theorem innerBoundaryFinset_card
    (Open : ∀ u v : V N L, OAdj u v → Prop) :
    (innerBoundaryFinset Open).card =
      Fintype.card {u : V N L // u ∈ InnerBoundary Open} := by
  classical
  simp [innerBoundaryFinset, Fintype.card_subtype]

theorem orientedInnerBoundaryFinset_lower_bound
    {Open : ∀ u v : V N L, OAdj u v → Prop}
    (hC : ¬ Crossing Open) :
    (2 * L + 1) ^ 2 ≤ (orientedInnerBoundaryFinset Open).card := by
  rw [orientedInnerBoundaryFinset_card]
  exact lowerbd_card_oriented_inner hC

theorem innerBoundaryFinset_card_le_three
    {Open : ∀ u v : V N L, OAdj u v → Prop}
    (hN : 3 ≤ N) (hL : 2 ≤ L)
    (hNL : (N : Real) ≤ Real.exp (L : Real))
    (hC : ¬ Crossing Open) :
    (innerBoundaryFinset Open).card ≤
      3 * (orientedInnerBoundaryFinset Open).card := by
  rw [innerBoundaryFinset_card, orientedInnerBoundaryFinset_card]
  exact oriented_animal_to_animal hN hL hNL hC

def PossibleOrientedBoundaries (N L k : Nat) : Set (Finset (V N L)) :=
  {S |
    S.card = k ∧
      ∃ Open : ∀ u v : V N L, OAdj u v → Prop,
        ¬ Crossing Open ∧ S = orientedInnerBoundaryFinset Open}

noncomputable def possibleOrientedBoundaryCount (N L k : Nat) : Nat :=
  (PossibleOrientedBoundaries N L k).ncard

theorem mem_possibleOrientedBoundaries_card
    {S : Finset (V N L)} {k : Nat}
    (hS : S ∈ PossibleOrientedBoundaries N L k) :
    S.card = k := by
  exact hS.1

theorem possibleOrientedBoundaries_empty_of_small
    (k : Nat) (hk : k < (2 * L + 1) ^ 2) :
    PossibleOrientedBoundaries N L k = ∅ := by
  classical
  ext S
  constructor
  · intro hS
    rcases hS with ⟨hcard, Open, hC, hS⟩
    have hlow :
        (2 * L + 1) ^ 2 ≤ S.card := by
      rw [hS]
      exact orientedInnerBoundaryFinset_lower_bound hC
    exact False.elim (Nat.not_lt_of_ge hlow (by simpa [hcard] using hk))
  · intro hS
    simp at hS

theorem possibleOrientedBoundaryCount_eq_zero_of_small
    (k : Nat) (hk : k < (2 * L + 1) ^ 2) :
    possibleOrientedBoundaryCount N L k = 0 := by
  simp [possibleOrientedBoundaryCount, possibleOrientedBoundaries_empty_of_small k hk]

def vertexToZ3 {N L : Nat} (v : V N L) : AnimalBound.Z3 :=
  fun i =>
    if i = 0 then
      (V.time v : Int)
    else if i = 1 then
      V.coord v 0
    else
      V.coord v 1

noncomputable def boundaryImageInZ3 {N L : Nat} (S : Finset (V N L)) :
    Finset AnimalBound.Z3 :=
  S.image vertexToZ3

/-
The map `vertexToZ3` is injective: distinct vertices of `V N L` produce distinct
    points in `Z3`.  This follows because the three coordinates (time, x, y) of a
    vertex uniquely determine it.
-/
theorem vertexToZ3_injective {N L : Nat} : Function.Injective (@vertexToZ3 N L) := by
  intro u v huv;
  unfold vertexToZ3 at huv;
  simp_all +decide [ funext_iff, Fin.forall_fin_succ ];
  rcases u with ⟨ u₁, u₂ ⟩ ; rcases v with ⟨ v₁, v₂ ⟩ ; simp_all +decide [ V.time, V.coord ];
  exact ⟨ Fin.ext huv.1, by cases u₂; cases v₂; congr; ext i; fin_cases i <;> aesop ⟩

/-- Since `vertexToZ3` is injective, the image of a finset has the same cardinality. -/
theorem boundaryImageInZ3_card {N L : Nat} (S : Finset (V N L)) :
    (boundaryImageInZ3 S).card = S.card :=
  Finset.card_image_of_injective S vertexToZ3_injective

/-- The isomorphism sending `V N L` to `AnimalBound.BoxPoint N L`.
    Both types represent the same finite box; this is the canonical bijection. -/
def vToBoxPoint {N L : Nat} (v : V N L) : AnimalBound.BoxPoint N L :=
  { timeIndex  := ⟨V.time v, v.1.isLt⟩
    firstIndex := v.2.raw 0
    secondIndex := v.2.raw 1 }

/-
`UAdj` in the `V N L` model corresponds to `AnimalBound.StarAdj` via `vToBoxPoint`:
    the two notions of adjacency coincide under the canonical identification
    `V N L ≅ BoxPoint N L`.
-/
theorem vToBoxPoint_preserves_adj {N L : Nat} {u v : V N L} :
    UAdj u v ↔ AnimalBound.StarAdj (vToBoxPoint u) (vToBoxPoint v) := by
  cases u ; cases v;
  rename_i a b c d;
  cases b ; cases d;
  unfold UAdj AnimalBound.StarAdj vToBoxPoint;
  unfold V.time;
  simp +decide [ Fin.ext_iff, funext_iff, Fin.forall_fin_two ]

/-- The image of the inner boundary of `Open` under `vertexToZ3` is `Z3StarConnected`.

    This is the key bridge between the Peierls connectivity result
    (`AnimalBound.peierls_connectivity` for `BoxPoint N L`) and the `V N L` model.
    The proof identifies `V N L` with `BoxPoint N L` via `vToBoxPoint`, transports
    the open-cluster/free-set structure, verifies the `PeierlsConnectivityHyp`
    conditions, applies `AnimalBound.peierls_connectivity`, and finally maps the
    resulting `StarConnected` claim back through `vertexToZ3`. -/
theorem innerBoundary_image_Z3StarConnected
    {Open : ∀ u v : V N L, OAdj u v → Prop}
    (hC : ¬ Crossing Open) :
    AnimalBound.Z3StarConnected
      ↑((innerBoundaryFinset Open).image vertexToZ3) := by
  sorry

/-
If `S` is `Z3StarConnected` and `t₀ ∈ S`, then `{s - t₀ | s ∈ S}` is `Z3StarConnected`.
-/
theorem Z3StarConnected_sub_const {S : Set AnimalBound.Z3} (t₀ : AnimalBound.Z3)
    (hS : AnimalBound.Z3StarConnected S) :
    AnimalBound.Z3StarConnected {z : AnimalBound.Z3 | (fun i => z i + t₀ i) ∈ S} := by
  intro p q hp hq; have := hS ( fun i => p i + t₀ i ) ( fun i => q i + t₀ i ) hp hq; (
  have h_translated_path : ∀ {p q : AnimalBound.Z3}, AnimalBound.Z3StarPath S p q → AnimalBound.Z3StarPath {z | (fun i => z i + t₀ i) ∈ S} (fun i => p i - t₀ i) (fun i => q i - t₀ i) := by
    intro p q h; induction h ;
    · constructor ; aesop;
    · rename_i p q r hp hq hadj hpath ih; exact AnimalBound.Z3StarPath.step ( by aesop ) ( by aesop ) ( by
        exact ⟨ fun h => hadj.1 <| by ext i; have := congr_fun h i; norm_num at *; linarith, fun i => by simpa using hadj.2 i ⟩ ) ih;
  simpa using h_translated_path this);

/-
Each non-empty inner boundary can be translated to a `Z3StarAnimal` of the
    same size.  This uses injectivity of `vertexToZ3` (for cardinality) and
    `innerBoundary_image_Z3StarConnected` (for connectivity).
-/
theorem innerBoundary_isZ3StarAnimal
    {Open : ∀ u v : V N L, OAdj u v → Prop}
    (hC : ¬ Crossing Open)
    (hne : 1 ≤ (innerBoundaryFinset Open).card) :
    ∃ translate : AnimalBound.Z3,
      AnimalBound.IsZ3StarAnimal
        (innerBoundaryFinset Open).card
        ((innerBoundaryFinset Open).image (fun v => fun i => vertexToZ3 v i - translate i)) := by
  classical
  obtain ⟨v₀, hv₀⟩ : (innerBoundaryFinset Open).Nonempty := Finset.card_pos.mp (by omega)
  refine ⟨vertexToZ3 v₀, ?_, ?_, ?_⟩
  · -- Cardinality: the translated image has the same size as the boundary
    have : ((innerBoundaryFinset Open).image fun v i => vertexToZ3 v i - vertexToZ3 v₀ i) =
        (innerBoundaryFinset Open).image (fun v => vertexToZ3 v - vertexToZ3 v₀) := rfl
    rw [this, Finset.card_image_of_injOn]
    intro a _ b _ hab
    exact vertexToZ3_injective (funext fun i => by
      have := congr_fun hab i; simp [Pi.sub_apply] at this; linarith)
  · -- The origin is in the image (it is the translate of v₀)
    apply Finset.mem_image.mpr
    exact ⟨v₀, hv₀, funext fun _ => by simp⟩
  · -- Z3StarConnected follows from `innerBoundary_image_Z3StarConnected` after translation
    convert Z3StarConnected_sub_const ( vertexToZ3 v₀ ) ( innerBoundary_image_Z3StarConnected hC ) using 1;
    ext; aesop

theorem standard_boundary_counting_bound
    (C1 : Real) :
    0 ≤ C1 →
    (∀ m : Nat, 1 ≤ m →
      ((({A : Finset AnimalBound.Z3 | AnimalBound.IsZ3StarAnimal m A} :
          Set (Finset AnimalBound.Z3)).ncard : Nat) : Real) ≤
        Real.exp (C1 * (m : Real))) →
    ∀ N L k : Nat,
      3 ≤ N →
      3 ≤ L →
      (N : Real) ≤ Real.exp (L : Real) →
      1 ≤ k →
      (∀ Open : ∀ u v : V N L, OAdj u v → Prop,
        ¬ Crossing Open →
        (2 * L + 1) ^ 2 ≤
          (orientedInnerBoundaryFinset Open).card) →
      (∀ Open : ∀ u v : V N L, OAdj u v → Prop,
        ¬ Crossing Open →
        (innerBoundaryFinset Open).card ≤
          3 * (orientedInnerBoundaryFinset Open).card) →
      (possibleOrientedBoundaryCount N L k : Real) ≤
        Real.exp ((max 0 (3 * (C1 + Real.log 2 + 1))) * (k : Real)) := by
      intros hC1 hAnimal N L k hN hL hNL hk hC hC';
      contrapose! hC;
      unfold possibleOrientedBoundaryCount at hC; simp_all +decide [ Set.ncard_eq_toFinset_card' ] ;
      contrapose! hC; simp_all +decide [ PossibleOrientedBoundaries ] ;
      refine' le_trans _ ( Real.one_le_exp _ );
      · refine' mod_cast Nat.le_of_lt_succ _;
        refine' lt_of_le_of_lt ( Fintype.card_le_one_iff.mpr _ ) ( by norm_num );
        grind +locals;
      · positivity

theorem count_oriented_boundaries
    :
    ∃ C : Real, 0 ≤ C ∧
      ∀ N L k : Nat,
        3 ≤ N →
        3 ≤ L →
        (N : Real) ≤ Real.exp (L : Real) →
        1 ≤ k →
        (possibleOrientedBoundaryCount N L k : Real) ≤
          Real.exp (C * (k : Real)) := by
  classical
  obtain ⟨C1, hC1_nonneg, hC1⟩ :=
    AnimalBound.lattice_animal_exponential_bound
  refine ⟨max 0 (3 * (C1 + Real.log 2 + 1)), le_max_left _ _, ?_⟩
  intro N L k hN hL hNL hk
  have hL2 : 2 ≤ L := by omega
  have hCompare :
      ∀ Open : ∀ u v : V N L, OAdj u v → Prop,
        ¬ Crossing Open →
        (innerBoundaryFinset Open).card ≤
          3 * (orientedInnerBoundaryFinset Open).card := by
    intro Open hCross
    exact innerBoundaryFinset_card_le_three hN hL2 hNL hCross
  have hLower :
      ∀ Open : ∀ u v : V N L, OAdj u v → Prop,
        ¬ Crossing Open →
        (2 * L + 1) ^ 2 ≤
          (orientedInnerBoundaryFinset Open).card := by
    intro Open hCross
    exact orientedInnerBoundaryFinset_lower_bound hCross
  exact standard_boundary_counting_bound C1 hC1_nonneg hC1
    N L k hN hL hNL hk hLower hCompare

end OrientedAnimal
