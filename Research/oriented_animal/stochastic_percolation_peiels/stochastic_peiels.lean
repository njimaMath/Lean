import Mathlib
import oriented_animal.final_animal_bound.oriented_animal_bound

open MeasureTheory
open scoped BigOperators
open scoped ENNReal

namespace OrientedAnimal

noncomputable section

variable {N L : Nat}

def TimeLayer (N L m : Nat) : Set (V N L) :=
  T N L m

def LayerSize (L : Nat) : Nat :=
  (2 * L + 1) ^ 2

theorem layerSize_eq_card_spacePoint (L : Nat) :
    Fintype.card (SpacePoint L) = LayerSize L := by
  simpa [LayerSize] using card_spacePoint L

abbrev EdgeConfig (N L : Nat) :=
  OEdge N L → Bool

noncomputable instance instFintypeOEdge {N L : Nat} : Fintype (OEdge N L) := by
  classical
  exact Fintype.ofEquiv
    {p : V N L × V N L // OAdj p.1 p.2}
    { toFun := fun p => ⟨p.1.1, p.1.2, p.2⟩
      invFun := fun e => ⟨(e.tail, e.head), e.adj⟩
      left_inv := by
        intro p
        cases p
        rfl
      right_inv := by
        intro e
        cases e
        rfl }

namespace EdgeConfig

def ClosedOn (X : EdgeConfig N L) (Γ : Finset (OEdge N L)) : Prop :=
  ∀ e ∈ Γ, X e = false

end EdgeConfig

abbrev ClosedParameter :=
  {p : NNReal // p ≤ 1}

noncomputable def edgeBernoulliBoolMeasure (p : ClosedParameter) :
    Measure Bool :=
  (PMF.bernoulli (1 - p.1) (tsub_le_self)).toMeasure

noncomputable def productBernoulliEdgeMeasure (N L : Nat)
    (p : ClosedParameter) : Measure (EdgeConfig N L) :=
  Measure.pi fun _ : OEdge N L => edgeBernoulliBoolMeasure p

theorem productBernoulliEdgeMeasure_isProbability
    (N L : Nat) (p : ClosedParameter) :
    IsProbabilityMeasure (productBernoulliEdgeMeasure N L p) := by
  unfold productBernoulliEdgeMeasure edgeBernoulliBoolMeasure
  infer_instance

noncomputable def stochasticOpen (N L : Nat) :
    EdgeConfig N L → ∀ u v : V N L, OAdj u v → Prop :=
  fun X u v h => X ⟨u, v, h⟩ = true

def NoCrossingEvent (N L : Nat) : Set (EdgeConfig N L) :=
  {X | ¬ Crossing (stochasticOpen N L X)}

theorem mem_noCrossingEvent_iff (X : EdgeConfig N L) :
    X ∈ NoCrossingEvent N L ↔ ¬ Crossing (stochasticOpen N L X) := by
  rfl

def ClosedEvent {N L : Nat} (Γ : Finset (OEdge N L)) :
    Set (EdgeConfig N L) :=
  {X | EdgeConfig.ClosedOn X Γ}

theorem mem_closedEvent_iff (X : EdgeConfig N L)
    (Γ : Finset (OEdge N L)) :
    X ∈ ClosedEvent Γ ↔ EdgeConfig.ClosedOn X Γ := by
  rfl

theorem closedOn_empty (X : EdgeConfig N L) :
    EdgeConfig.ClosedOn X (∅ : Finset (OEdge N L)) := by
  intro e he
  simp at he

theorem closedEvent_empty :
    ClosedEvent (N := N) (L := L) (∅ : Finset (OEdge N L)) = Set.univ := by
  ext X
  simp [ClosedEvent, EdgeConfig.ClosedOn]

theorem closedOn_mono
    {X : EdgeConfig N L} {Γ Γ' : Finset (OEdge N L)}
    (hsub : Γ ⊆ Γ') (hclosed : EdgeConfig.ClosedOn X Γ') :
    EdgeConfig.ClosedOn X Γ := by
  intro e he
  exact hclosed e (hsub he)

theorem closedEvent_antitone
    {Γ Γ' : Finset (OEdge N L)} (hsub : Γ ⊆ Γ') :
    ClosedEvent Γ' ⊆ ClosedEvent Γ := by
  intro X hX
  exact closedOn_mono hsub hX

theorem closedOn_insert_iff
    [DecidableEq (OEdge N L)]
    (X : EdgeConfig N L) (e : OEdge N L)
    (Γ : Finset (OEdge N L)) :
    EdgeConfig.ClosedOn X (insert e Γ) ↔
      X e = false ∧ EdgeConfig.ClosedOn X Γ := by
  constructor
  · intro h
    exact ⟨h e (by simp), fun f hf => h f (by simp [hf])⟩
  · intro h f hf
    rw [Finset.mem_insert] at hf
    rcases hf with rfl | hf
    · exact h.1
    · exact h.2 f hf

def OpenOnEdge
    (Open : ∀ u v : V N L, OAdj u v → Prop) (e : OEdge N L) : Prop :=
  Open e.tail e.head e.adj

namespace OPath

def snoc {N L : Nat} (p : OPath N L) {v : V N L}
    (h : OAdj p.finish v) : OPath N L where
  len := p.len + 1
  vertex := fun i =>
    if hi : i.val ≤ p.len then
      p.vertex (Fin.mk i.val (Nat.lt_succ_of_le hi))
    else
      v
  edge := by
    intro i
    simp only [Fin.val_castSucc, Fin.val_succ]
    by_cases hi : i.val < p.len
    · have hleft : i.val ≤ p.len := by omega
      have hright : i.val + 1 ≤ p.len := by omega
      simp [hleft, hright]
      convert p.edge ⟨i.val, hi⟩ using 2
    · have hleft : i.val ≤ p.len := by omega
      have hright : ¬ i.val + 1 ≤ p.len := by omega
      have hilast : i.val = p.len := by omega
      simp [hilast]
      simpa [OPath.finish] using h

lemma snoc_start {N L : Nat} (p : OPath N L) {v : V N L}
    (h : OAdj p.finish v) :
    (p.snoc h).start = p.start := by
  simp [snoc, start]

lemma snoc_finish {N L : Nat} (p : OPath N L) {v : V N L}
    (h : OAdj p.finish v) :
    (p.snoc h).finish = v := by
  unfold snoc finish
  simp

lemma snoc_allOpen {N L : Nat} (p : OPath N L)
    {Open : ∀ u v : V N L, OAdj u v → Prop} {v : V N L}
    (h : OAdj p.finish v) (hp : p.AllOpen Open)
    (hopen : Open p.finish v h) :
    (p.snoc h).AllOpen Open := by
  intro i
  have ibound : i.val < p.len + 1 := by
    simpa [snoc] using i.isLt
  unfold snoc
  simp only [Fin.val_castSucc, Fin.val_succ]
  by_cases hi : i.val < p.len
  · have hleft : i.val ≤ p.len := by omega
    have hright : i.val + 1 ≤ p.len := by omega
    simp [hleft, hright]
    exact hp ⟨i.val, hi⟩
  · have hleft : i.val ≤ p.len := by omega
    have hright : ¬ i.val + 1 ≤ p.len := by omega
    have hilast : i.val = p.len := by omega
    simp [hilast]
    exact hopen

end OPath

lemma B_of_open_edge {Open : ∀ u v : V N L, OAdj u v → Prop}
    {u v : V N L} (huB : u ∈ B Open) (huv : OAdj u v)
    (hopen : Open u v huv) :
    v ∈ B Open := by
  rcases huB with ⟨t, ht, p, hpstart, hpfinish, hpopen⟩
  refine ⟨t, ht, ?_⟩
  have hlast : OAdj p.finish v := by
    simpa [hpfinish] using huv
  refine ⟨p.snoc hlast, ?_, ?_, ?_⟩
  · rw [OPath.snoc_start, hpstart]
  · rw [OPath.snoc_finish]
  · apply OPath.snoc_allOpen
    · exact hpopen
    · simpa [hpfinish] using hopen

theorem oriented_inner_boundary_edges_closed
    (Open : ∀ u v : V N L, OAdj u v → Prop) :
    ∀ e : OEdge N L,
      e ∈ OrientedInnerEdgeBoundary Open → ¬ OpenOnEdge Open e := by
  intro e he hopen
  exact F_disjoint_B he.2 (B_of_open_edge he.1 e.adj hopen)

noncomputable def chosenBoundaryEdge
    (Open : ∀ u v : V N L, OAdj u v → Prop)
    (u : {u : V N L // u ∈ OrientedInnerBoundary Open}) : OEdge N L := by
  classical
  let h : ∃ v : V N L, ∃ _ : OAdj u.1 v, v ∈ F Open := u.property.2
  let v : V N L := Classical.choose h
  let hv : ∃ _ : OAdj u.1 v, v ∈ F Open := Classical.choose_spec h
  let huv : OAdj u.1 v := Classical.choose hv
  exact ⟨u.1, v, huv⟩

set_option linter.unnecessarySimpa false in
noncomputable def attachedBoundaryEdges
    (Open : ∀ u v : V N L, OAdj u v → Prop) : Finset (OEdge N L) := by
  classical
  exact (orientedInnerBoundaryFinset Open).attach.image fun u =>
    chosenBoundaryEdge Open
      ⟨u.1, by
        have huFin : u.1 ∈ orientedInnerBoundaryFinset Open := u.2
        have huFilter :
            u.1 ∈ Finset.univ.filter
              (fun x : V N L => x ∈ OrientedInnerBoundary Open) := by
          simpa [orientedInnerBoundaryFinset] using huFin
        exact (Finset.mem_filter.mp huFilter).2⟩

theorem attachedBoundaryEdges_card
    (Open : ∀ u v : V N L, OAdj u v → Prop) :
    (attachedBoundaryEdges Open).card =
      (orientedInnerBoundaryFinset Open).card := by
  classical
  unfold attachedBoundaryEdges
  rw [Finset.card_image_of_injective]
  · exact Finset.card_attach
  · intro ⟨a, ha⟩ ⟨b, hb⟩ hab
    simp only [Subtype.mk.injEq]
    have htail := congr_arg OEdge.tail hab
    simp only [chosenBoundaryEdge] at htail
    exact htail

theorem chosenBoundaryEdge_tail
    (Open : ∀ u v : V N L, OAdj u v → Prop)
    (u : {u : V N L // u ∈ OrientedInnerBoundary Open}) :
    (chosenBoundaryEdge Open u).tail = u.1 := by
  rfl

theorem chosenBoundaryEdge_adj
    (Open : ∀ u v : V N L, OAdj u v → Prop)
    (u : {u : V N L // u ∈ OrientedInnerBoundary Open}) :
    OAdj (chosenBoundaryEdge Open u).tail
      (chosenBoundaryEdge Open u).head := by
  exact (chosenBoundaryEdge Open u).adj

theorem attachedBoundaryEdges_card_eq_boundary_card
    (Open : ∀ u v : V N L, OAdj u v → Prop) :
    (attachedBoundaryEdges Open).card =
      (orientedInnerBoundaryFinset Open).card :=
  attachedBoundaryEdges_card Open

theorem attachedBoundaryEdges_tail_image
    (Open : ∀ u v : V N L, OAdj u v → Prop) :
    (attachedBoundaryEdges Open).image OEdge.tail =
      orientedInnerBoundaryFinset Open := by
  classical
  ext u
  constructor
  · intro hu
    rcases Finset.mem_image.mp hu with ⟨e, he, htail⟩
    unfold attachedBoundaryEdges at he
    rcases Finset.mem_image.mp he with ⟨w, hw, rfl⟩
    have hwu : w.1 = u := by
      simpa [chosenBoundaryEdge_tail] using htail
    simpa [hwu] using w.2
  · intro hu
    have hboundary : u ∈ OrientedInnerBoundary Open := by
      simpa [orientedInnerBoundaryFinset] using hu
    refine Finset.mem_image.mpr ?_
    refine ⟨chosenBoundaryEdge Open ⟨u, hboundary⟩, ?_, ?_⟩
    · unfold attachedBoundaryEdges
      refine Finset.mem_image.mpr ?_
      exact ⟨⟨u, hu⟩, by simp, rfl⟩
    · simp [chosenBoundaryEdge_tail]

theorem attachedBoundaryEdges_closed_for_raw
    (X : EdgeConfig N L)
    (_hC : ¬ Crossing (stochasticOpen N L X)) :
    EdgeConfig.ClosedOn X
      (attachedBoundaryEdges (stochasticOpen N L X)) := by
  classical
  intro e he
  unfold attachedBoundaryEdges at he
  simp only [Finset.mem_image, Finset.mem_attach, true_and, Subtype.exists] at he
  obtain ⟨u, hu, rfl⟩ := he
  have hBdry : u ∈ OrientedInnerBoundary (stochasticOpen N L X) := by
    simp [orientedInnerBoundaryFinset] at hu
    exact hu
  set e := chosenBoundaryEdge (stochasticOpen N L X) ⟨u, hBdry⟩
  have hv_in_F : e.head ∈ F (stochasticOpen N L X) := by
    simp only [chosenBoundaryEdge, e]
    exact Classical.choose_spec (Classical.choose_spec hBdry.2)
  have hboundary_edge :
      e ∈ OrientedInnerEdgeBoundary (stochasticOpen N L X) := by
    exact ⟨by simpa [e, chosenBoundaryEdge] using hBdry.1, hv_in_F⟩
  have hnotopen :
      ¬ X e = true := by
    simpa [OpenOnEdge, stochasticOpen] using
      oriented_inner_boundary_edges_closed
        (stochasticOpen N L X) e hboundary_edge
  cases hxe : X e
  · rfl
  · exact False.elim (hnotopen hxe)

theorem boundary_large_on_no_crossing
    {Open : ∀ u v : V N L, OAdj u v → Prop}
    (hC : ¬ Crossing Open) :
    LayerSize L ≤ (orientedInnerBoundaryFinset Open).card := by
  simpa [LayerSize] using orientedInnerBoundaryFinset_lower_bound (L := L) hC

theorem attachedBoundaryEdges_large_on_no_crossing
    (X : EdgeConfig N L) (hX : X ∈ NoCrossingEvent N L) :
    LayerSize L ≤
      (attachedBoundaryEdges (stochasticOpen N L X)).card := by
  rw [attachedBoundaryEdges_card]
  exact boundary_large_on_no_crossing
    (Open := stochasticOpen N L X) hX

theorem orientedBoundary_mem_possible_for_card
    (Open : ∀ u v : V N L, OAdj u v → Prop)
    (hC : ¬ Crossing Open) :
    orientedInnerBoundaryFinset Open ∈
      PossibleOrientedBoundaries N L
        (orientedInnerBoundaryFinset Open).card := by
  exact ⟨rfl, Open, hC, rfl⟩

def AttachedEdgeCandidates (N L k : Nat) : Set (Finset (OEdge N L)) :=
  {Γ |
    Γ.card = k ∧
      ∃ X : EdgeConfig N L,
        ¬ Crossing (stochasticOpen N L X) ∧
          Γ = attachedBoundaryEdges (stochasticOpen N L X)}

noncomputable def attachedEdgeCandidateCount (N L k : Nat) : Nat :=
  (AttachedEdgeCandidates N L k).ncard

theorem mem_AttachedEdgeCandidates_iff
    (Γ : Finset (OEdge N L)) (k : Nat) :
    Γ ∈ AttachedEdgeCandidates N L k ↔
      Γ.card = k ∧
        ∃ X : EdgeConfig N L,
          ¬ Crossing (stochasticOpen N L X) ∧
            Γ = attachedBoundaryEdges (stochasticOpen N L X) := by
  rfl

theorem mem_AttachedEdgeCandidates_card
    {Γ : Finset (OEdge N L)} {k : Nat}
    (hΓ : Γ ∈ AttachedEdgeCandidates N L k) :
    Γ.card = k := by
  exact hΓ.1

theorem attachedBoundaryEdges_mem_candidates
    (X : EdgeConfig N L) (hX : X ∈ NoCrossingEvent N L) :
    attachedBoundaryEdges (stochasticOpen N L X) ∈
      AttachedEdgeCandidates N L
        (attachedBoundaryEdges (stochasticOpen N L X)).card := by
  exact ⟨rfl, X, hX, rfl⟩

theorem possible_boundary_of_attached_candidate
    {Γ : Finset (OEdge N L)} {k : Nat}
    (hΓ : Γ ∈ AttachedEdgeCandidates N L k) :
    ∃ X : EdgeConfig N L,
      orientedInnerBoundaryFinset (stochasticOpen N L X) ∈
        PossibleOrientedBoundaries N L k ∧
      Γ = attachedBoundaryEdges (stochasticOpen N L X) := by
  rcases hΓ with ⟨hcard, X, hC, hΓeq⟩
  refine ⟨X, ?_, hΓeq⟩
  have hboundary_card :
      (orientedInnerBoundaryFinset (stochasticOpen N L X)).card = k := by
    rw [← attachedBoundaryEdges_card (Open := stochasticOpen N L X)]
    rw [← hΓeq]
    exact hcard
  exact ⟨hboundary_card, stochasticOpen N L X, hC, rfl⟩

def CandidateClosedUnion (N L k : Nat) : Set (EdgeConfig N L) :=
  ⋃ Γ ∈ AttachedEdgeCandidates N L k, ClosedEvent Γ

def CandidateClosedTail (N L m : Nat) : Set (EdgeConfig N L) :=
  ⋃ k ≥ m, CandidateClosedUnion N L k

theorem mem_candidateClosedUnion_iff
    (X : EdgeConfig N L) (k : Nat) :
    X ∈ CandidateClosedUnion N L k ↔
      ∃ Γ ∈ AttachedEdgeCandidates N L k, X ∈ ClosedEvent Γ := by
  simp [CandidateClosedUnion]

theorem mem_candidateClosedTail_iff
    (X : EdgeConfig N L) (m : Nat) :
    X ∈ CandidateClosedTail N L m ↔
      ∃ k ≥ m, ∃ Γ ∈ AttachedEdgeCandidates N L k,
        X ∈ ClosedEvent Γ := by
  simp [CandidateClosedTail, CandidateClosedUnion]

theorem candidateClosedUnion_subset_tail
    {m k : Nat} (hmk : m ≤ k) :
    CandidateClosedUnion N L k ⊆ CandidateClosedTail N L m := by
  intro X hX
  rw [mem_candidateClosedTail_iff]
  rw [mem_candidateClosedUnion_iff] at hX
  rcases hX with ⟨Γ, hΓ, hclosed⟩
  exact ⟨k, hmk, Γ, hΓ, hclosed⟩

theorem candidateClosedTail_mono
    {m m' : Nat} (hmm' : m ≤ m') :
    CandidateClosedTail N L m' ⊆ CandidateClosedTail N L m := by
  intro X hX
  rw [mem_candidateClosedTail_iff] at hX ⊢
  rcases hX with ⟨k, hk, Γ, hΓ, hclosed⟩
  exact ⟨k, le_trans hmm' hk, Γ, hΓ, hclosed⟩

theorem candidateClosedUnion_mem_tail_self
    (k : Nat) :
    CandidateClosedUnion N L k ⊆ CandidateClosedTail N L k :=
  candidateClosedUnion_subset_tail le_rfl

theorem closedEvent_subset_candidateClosedUnion
    {Γ : Finset (OEdge N L)} {k : Nat}
    (hΓ : Γ ∈ AttachedEdgeCandidates N L k) :
    ClosedEvent Γ ⊆ CandidateClosedUnion N L k := by
  intro X hX
  rw [mem_candidateClosedUnion_iff]
  exact ⟨Γ, hΓ, hX⟩

theorem closedEvent_subset_candidateClosedTail
    {Γ : Finset (OEdge N L)} {m k : Nat}
    (hmk : m ≤ k) (hΓ : Γ ∈ AttachedEdgeCandidates N L k) :
    ClosedEvent Γ ⊆ CandidateClosedTail N L m := by
  exact subset_trans (closedEvent_subset_candidateClosedUnion hΓ)
    (candidateClosedUnion_subset_tail hmk)

theorem no_crossing_mem_candidateClosedTail
    (X : EdgeConfig N L) (hX : X ∈ NoCrossingEvent N L) :
    X ∈ CandidateClosedTail N L (LayerSize L) := by
  let Γ := attachedBoundaryEdges (stochasticOpen N L X)
  let k := Γ.card
  have hk : LayerSize L ≤ k := by
    simpa [Γ, k] using attachedBoundaryEdges_large_on_no_crossing X hX
  have hΓ : Γ ∈ AttachedEdgeCandidates N L k := by
    simpa [Γ, k] using attachedBoundaryEdges_mem_candidates X hX
  have hclosed : X ∈ ClosedEvent Γ := by
    simpa [ClosedEvent, Γ] using
      attachedBoundaryEdges_closed_for_raw X hX
  rw [mem_candidateClosedTail_iff]
  exact ⟨k, hk, Γ, hΓ, hclosed⟩

theorem candidateClosedTail_eq_closed_union :
    CandidateClosedTail N L (LayerSize L) =
      ⋃ k ≥ LayerSize L,
        ⋃ Γ ∈ AttachedEdgeCandidates N L k, ClosedEvent Γ := by
  rfl

theorem productBernoulli_closedEvent
    (p : ClosedParameter) (Γ : Finset (OEdge N L)) :
    productBernoulliEdgeMeasure N L p (ClosedEvent Γ) =
      (p.1 : ℝ≥0∞) ^ Γ.card := by
  convert MeasureTheory.Measure.pi_pi ( fun _ : OEdge N L => edgeBernoulliBoolMeasure p ) ( fun e => if e ∈ Γ then { Bool.false } else Set.univ ) using 1;
  rotate_left;
  rotate_left;
  rotate_left;
  exact fun e => Classical.propDecidable (e ∈ Γ);
  · congr with X ; simp +decide [ ClosedEvent, EdgeConfig.ClosedOn ];
    grind;
  · rw [ ← Finset.prod_subset ( Finset.subset_univ Γ ) ];
    · rw [ Finset.prod_congr rfl fun x hx => by aesop ];
      unfold edgeBernoulliBoolMeasure;
      simp +decide;
      rw [ ENNReal.sub_sub_cancel ] <;> norm_num;
      exact p.2;
    · unfold edgeBernoulliBoolMeasure; aesop;
  · intro i;
    use fun _ => Set.univ;
    · exact fun _ => Set.mem_univ _;
    · simp +decide [ edgeBernoulliBoolMeasure ];
    · exact Set.iUnion_const _

/-
The number of finsets of k edges with distinct tails all in a given boundary set
    is at most 9^k, since each vertex has at most 9 outgoing neighbors.
-/
set_option linter.unnecessarySimpa false in
theorem outgoing_edge_count_le (u : V N L) :
    Fintype.card {e : OEdge N L // e.tail = u} ≤ 9 := by
  classical
  let code : {e : OEdge N L // e.tail = u} → Fin 2 → Fin 3 :=
    fun e i =>
      if (e.1.head.2.raw i).val + 1 = (u.2.raw i).val then
        0
      else if (e.1.head.2.raw i).val = (u.2.raw i).val then
        1
      else
        2
  have hcode_inj : Function.Injective code := by
    intro a b hab
    apply Subtype.ext
    cases a with
    | mk ea ha =>
      cases b with
      | mk eb hb =>
        cases ea with
        | mk taila heada aadj =>
          cases eb with
          | mk tailb headb badj =>
            dsimp at ha hb
            subst taila
            subst tailb
            congr
            · cases heada with
              | mk timea spacea =>
                cases headb with
                | mk timeb spaceb =>
                  cases spacea with
                  | mk rawa =>
                    cases spaceb with
                    | mk rawb =>
                      congr
                      · apply Fin.ext
                        dsimp [OAdj, V.time] at aadj badj
                        omega
                      · funext i
                        apply Fin.ext
                        have hcode_i := congr_fun hab i
                        dsimp [code] at hcode_i
                        have ha_adj := aadj.2 i
                        have hb_adj := badj.2 i
                        dsimp [SpaceStarAdj, V.space, SpacePoint.coord] at ha_adj hb_adj
                        have ha_abs_int :
                            |((u.2.raw i).val : Int) - (L : Int) -
                              (((rawa i).val : Int) - (L : Int))| ≤
                              (1 : Int) := by
                          rw [← Int.natCast_natAbs]
                          exact_mod_cast ha_adj
                        have hb_abs_int :
                            |((u.2.raw i).val : Int) - (L : Int) -
                              (((rawb i).val : Int) - (L : Int))| ≤
                              (1 : Int) := by
                          rw [← Int.natCast_natAbs]
                          exact_mod_cast hb_adj
                        have ha_abs := abs_le.mp ha_abs_int
                        have hb_abs := abs_le.mp hb_abs_int
                        by_cases ha_low :
                            (rawa i).val + 1 = (u.2.raw i).val
                        · by_cases hb_low :
                              (rawb i).val + 1 = (u.2.raw i).val
                          · exact Nat.succ.inj (ha_low.trans hb_low.symm)
                          · by_cases hb_eq :
                                (rawb i).val = (u.2.raw i).val
                            · have hbad : (0 : Fin 3) = 1 := by
                                simpa [code, ha_low, hb_low, hb_eq] using hcode_i
                              exfalso
                              have hbadNat := congr_arg Fin.val hbad
                              norm_num at hbadNat
                            · have hbad : (0 : Fin 3) = 2 := by
                                simpa [code, ha_low, hb_low, hb_eq] using hcode_i
                              exfalso
                              have hbadNat := congr_arg Fin.val hbad
                              norm_num at hbadNat
                        · by_cases ha_eq :
                              (rawa i).val = (u.2.raw i).val
                          · by_cases hb_low :
                                (rawb i).val + 1 = (u.2.raw i).val
                            · have hbad : (1 : Fin 3) = 0 := by
                                simpa [code, ha_low, ha_eq, hb_low] using hcode_i
                              exfalso
                              have hbadNat := congr_arg Fin.val hbad
                              norm_num at hbadNat
                            · by_cases hb_eq :
                                  (rawb i).val = (u.2.raw i).val
                              · exact ha_eq.trans hb_eq.symm
                              · have hbad : (1 : Fin 3) = 2 := by
                                  simpa [code, ha_low, ha_eq, hb_low, hb_eq] using hcode_i
                                exfalso
                                have hbadNat := congr_arg Fin.val hbad
                                norm_num at hbadNat
                          · by_cases hb_low :
                                (rawb i).val + 1 = (u.2.raw i).val
                            · have hbad : (2 : Fin 3) = 0 := by
                                simpa [code, ha_low, ha_eq, hb_low] using hcode_i
                              exfalso
                              have hbadNat := congr_arg Fin.val hbad
                              norm_num at hbadNat
                            · by_cases hb_eq :
                                  (rawb i).val = (u.2.raw i).val
                              · have hbad : (2 : Fin 3) = 1 := by
                                  simpa [code, ha_low, ha_eq, hb_low, hb_eq] using hcode_i
                                exfalso
                                have hbadNat := congr_arg Fin.val hbad
                                norm_num at hbadNat
                              · have ha_high :
                                    (u.2.raw i).val + 1 = (rawa i).val := by
                                  omega
                                have hb_high :
                                    (u.2.raw i).val + 1 = (rawb i).val := by
                                  omega
                                exact ha_high.symm.trans hb_high
  refine le_trans (Fintype.card_le_of_injective code hcode_inj) ?_
  norm_num [Fintype.card_fun]

theorem edge_selection_count_le (B : Finset (V N L)) :
    {Γ : Finset (OEdge N L) | Γ.card = B.card ∧
      Γ.image OEdge.tail = B}.ncard ≤ 9 ^ B.card := by
  classical
  let S : Set (Finset (OEdge N L)) :=
    {Γ | Γ.card = B.card ∧ Γ.image OEdge.tail = B}
  have hS_finite : S.Finite := Set.toFinite _
  obtain ⟨Sfin, hSfin⟩ := hS_finite.exists_finset_coe
  have h_exists :
      ∀ Γ ∈ Sfin, ∀ v ∈ B, ∃! e, e ∈ Γ ∧ e.tail = v := by
    intro Γ hΓ v hv
    have hΓS : Γ ∈ S := by
      exact hSfin.subset hΓ
    have h_card : Γ.card = B.card := hΓS.1
    have h_image : Γ.image OEdge.tail = B := hΓS.2
    have h_image_card : (Γ.image OEdge.tail).card = Γ.card := by
      rw [h_image, h_card]
    have h_inj_tail :=
      Finset.card_image_iff.mp h_image_card
    have hv_image : v ∈ Γ.image OEdge.tail := by
      rw [h_image]
      exact hv
    rcases Finset.mem_image.mp hv_image with ⟨e, heΓ, he_tail⟩
    refine ⟨e, ⟨heΓ, he_tail⟩, ?_⟩
    intro f hf
    exact h_inj_tail hf.1 heΓ (hf.2.trans he_tail.symm)
  let pick (Γ : {Γ : Finset (OEdge N L) // Γ ∈ Sfin}) (v : B) :
      OEdge N L :=
    Classical.choose (h_exists Γ.1 Γ.2 v.1 v.2)
  have pick_mem
      (Γ : {Γ : Finset (OEdge N L) // Γ ∈ Sfin}) (v : B) :
      pick Γ v ∈ Γ.1 ∧ (pick Γ v).tail = v.1 :=
    (Classical.choose_spec (h_exists Γ.1 Γ.2 v.1 v.2)).1
  have pick_unique
      (Γ : {Γ : Finset (OEdge N L) // Γ ∈ Sfin}) (v : B)
      (e : OEdge N L) (he : e ∈ Γ.1 ∧ e.tail = v.1) :
      e = pick Γ v :=
    (Classical.choose_spec (h_exists Γ.1 Γ.2 v.1 v.2)).2 e he
  let encode :
      {Γ : Finset (OEdge N L) // Γ ∈ Sfin} →
        (Π v : B, {e : OEdge N L // e.tail = v.1}) :=
    fun Γ v => ⟨pick Γ v, (pick_mem Γ v).2⟩
  have h_encode_inj : Function.Injective encode := by
    intro Γ₁ Γ₂ h_eq
    apply Subtype.ext
    ext e
    constructor
    · intro he
      have hΓS : Γ₁.1 ∈ S := by
        exact hSfin.subset Γ₁.2
      have htailB : e.tail ∈ B := by
        rw [← hΓS.2]
        exact Finset.mem_image_of_mem _ he
      let v : B := ⟨e.tail, htailB⟩
      have hval :
          (encode Γ₁ v).1 = (encode Γ₂ v).1 := by
        exact congr_arg Subtype.val (congr_fun h_eq v)
      have hpick1 : pick Γ₁ v = e := by
        exact (pick_unique Γ₁ v e ⟨he, rfl⟩).symm
      have hpick2 : pick Γ₂ v = e := by
        exact hval.symm.trans hpick1
      have hmem2 : pick Γ₂ v ∈ Γ₂.1 := (pick_mem Γ₂ v).1
      simpa [hpick2] using hmem2
    · intro he
      have hΓS : Γ₂.1 ∈ S := by
        exact hSfin.subset Γ₂.2
      have htailB : e.tail ∈ B := by
        rw [← hΓS.2]
        exact Finset.mem_image_of_mem _ he
      let v : B := ⟨e.tail, htailB⟩
      have hval :
          (encode Γ₁ v).1 = (encode Γ₂ v).1 := by
        exact congr_arg Subtype.val (congr_fun h_eq v)
      have hpick2 : pick Γ₂ v = e := by
        exact (pick_unique Γ₂ v e ⟨he, rfl⟩).symm
      have hpick1 : pick Γ₁ v = e := by
        exact hval.trans hpick2
      have hmem1 : pick Γ₁ v ∈ Γ₁.1 := (pick_mem Γ₁ v).1
      simpa [hpick1] using hmem1
  have h_codomain_card : (Fintype.card (Π v : B, {e : OEdge N L // e.tail = v.val})) ≤ 9 ^ B.card := by
    rw [Fintype.card_pi]
    refine le_trans (Finset.prod_le_prod' fun x _ => outgoing_edge_count_le x.1) ?_
    simp
  rw [show {Γ : Finset (OEdge N L) | Γ.card = B.card ∧
        Γ.image OEdge.tail = B} = S from rfl]
  rw [← hSfin, Set.ncard_coe_finset]
  exact le_trans
    (by simpa using Fintype.card_le_of_injective encode h_encode_inj)
    h_codomain_card

/-
For each attached edge candidate, its tail set is a possible boundary.
-/
theorem attached_candidate_tail_image {k : Nat} (Γ : Finset (OEdge N L))
    (hΓ : Γ ∈ AttachedEdgeCandidates N L k) :
    Γ.image OEdge.tail ∈ PossibleOrientedBoundaries N L k := by
  obtain ⟨X, hpossible, hΓeq⟩ := possible_boundary_of_attached_candidate hΓ
  rw [hΓeq, attachedBoundaryEdges_tail_image]
  exact hpossible

theorem attachedEdgeCandidateCount_le_bound (N L k : Nat) :
    (attachedEdgeCandidateCount N L k : Real) ≤
      (possibleOrientedBoundaryCount N L k : Real) * (9 : Real) ^ k := by
  by_contra h_contra;
  -- Apply the lemma that states the number of attached edge candidates is bounded by the number of possible boundaries times 9^k.
  have h_bound : (AttachedEdgeCandidates N L k).ncard ≤ (PossibleOrientedBoundaries N L k).ncard * 9 ^ k := by
    have h_bound : (AttachedEdgeCandidates N L k).ncard ≤ ∑ B ∈ (PossibleOrientedBoundaries N L k).toFinset, {Γ : Finset (OEdge N L) | Γ.card = B.card ∧ Γ.image OEdge.tail = B}.ncard := by
      have h_bound : (AttachedEdgeCandidates N L k).ncard ≤ ∑ B ∈ (PossibleOrientedBoundaries N L k).toFinset, (Set.ncard (AttachedEdgeCandidates N L k ∩ {Γ : Finset (OEdge N L) | Γ.image OEdge.tail = B})) := by
        have h_bound : (AttachedEdgeCandidates N L k).ncard = (⋃ B ∈ (PossibleOrientedBoundaries N L k).toFinset, (AttachedEdgeCandidates N L k ∩ {Γ : Finset (OEdge N L) | Γ.image OEdge.tail = B})).ncard := by
          congr with Γ ; simp +decide;
          exact fun a => attached_candidate_tail_image Γ a;
        rw [h_bound];
        exact Finset.set_ncard_biUnion_le
          (PossibleOrientedBoundaries N L k).toFinset fun i =>
            AttachedEdgeCandidates N L k ∩
              {Γ : Finset (OEdge N L) | Γ.image OEdge.tail = i};
      refine le_trans h_bound <| Finset.sum_le_sum fun B hB => ?_;
      fapply Set.ncard_le_ncard;
      · simp +contextual [ Set.subset_def, AttachedEdgeCandidates ];
        unfold PossibleOrientedBoundaries at hB; aesop;
      · exact Set.toFinite _;
    refine le_trans h_bound ?_;
    refine' le_trans ( Finset.sum_le_sum fun x hx => show _ ≤ 9 ^ k from _ ) _;
    · convert edge_selection_count_le x using 1;
      unfold PossibleOrientedBoundaries at hx; aesop;
    · norm_num [ Set.ncard_eq_toFinset_card' ];
  exact h_contra <| mod_cast h_bound

theorem counting_candidates :
    ∃ C : Real, 0 ≤ C ∧
      ∀ N L k : Nat,
        3 ≤ N →
        3 ≤ L →
        (N : Real) ≤ Real.exp (L : Real) →
        1 ≤ k →
        (possibleOrientedBoundaryCount N L k : Real) ≤
          Real.exp (C * (k : Real)) ∧
        (attachedEdgeCandidateCount N L k : Real) ≤
          Real.exp ((C + Real.log 9) * (k : Real)) := by
  classical
  obtain ⟨C, hC0, hC⟩ := count_oriented_boundaries
  refine ⟨C, hC0, ?_⟩
  intro N L k hN hL hNL hk
  exact ⟨hC N L k hN hL hNL hk, by
    have h_exp_log : (9 : ℝ) ^ k = Real.exp (Real.log 9 * k) := by
      rw [ Real.exp_mul, Real.exp_log ] <;> norm_cast;
    convert le_trans ( attachedEdgeCandidateCount_le_bound N L k ) ( mul_le_mul_of_nonneg_right ( hC N L k hN hL hNL hk ) ( by positivity ) ) using 1 ; rw [ h_exp_log ] ; rw [ ← Real.exp_add ] ; ring_nf⟩

structure PeierlsMeasureHyp
    (μ : Measure (EdgeConfig N L)) (p : NNReal) : Prop where
  isProbability : IsProbabilityMeasure μ
  closed_edges :
    ∀ Γ : Finset (OEdge N L),
      μ (ClosedEvent Γ) = (p : ℝ≥0∞) ^ Γ.card

theorem productBernoulliEdgeMeasure_hyp
    (p : ClosedParameter) :
    PeierlsMeasureHyp (N := N) (L := L)
      (productBernoulliEdgeMeasure N L p) p.1 := by
  exact ⟨productBernoulliEdgeMeasure_isProbability N L p,
    productBernoulli_closedEvent p⟩

theorem closedEvent_measure_eq
    {μ : Measure (EdgeConfig N L)} {p : NNReal}
    (hμ : PeierlsMeasureHyp (N := N) (L := L) μ p)
    (Γ : Finset (OEdge N L)) :
    μ (ClosedEvent Γ) = (p : ℝ≥0∞) ^ Γ.card :=
  hμ.closed_edges Γ

theorem peierlsMeasure_univ
    {μ : Measure (EdgeConfig N L)} {p : NNReal}
    (hμ : PeierlsMeasureHyp (N := N) (L := L) μ p) :
    μ Set.univ = 1 := by
  haveI : IsProbabilityMeasure μ := hμ.isProbability
  simp

theorem peierlsMeasure_le_one
    {μ : Measure (EdgeConfig N L)} {p : NNReal}
    (hμ : PeierlsMeasureHyp (N := N) (L := L) μ p)
    (A : Set (EdgeConfig N L)) :
    μ A ≤ 1 := by
  rw [← peierlsMeasure_univ (N := N) (L := L) hμ]
  exact measure_mono (Set.subset_univ A)

theorem closedEvent_measure_eq_of_card
    {μ : Measure (EdgeConfig N L)} {p : NNReal}
    (hμ : PeierlsMeasureHyp (N := N) (L := L) μ p)
    {Γ : Finset (OEdge N L)} {k : Nat} (hcard : Γ.card = k) :
    μ (ClosedEvent Γ) = (p : ℝ≥0∞) ^ k := by
  rw [closedEvent_measure_eq hμ Γ, hcard]

theorem closedEvent_measure_eq_of_candidate
    {μ : Measure (EdgeConfig N L)} {p : NNReal}
    (hμ : PeierlsMeasureHyp (N := N) (L := L) μ p)
    {Γ : Finset (OEdge N L)} {k : Nat}
    (hΓ : Γ ∈ AttachedEdgeCandidates N L k) :
    μ (ClosedEvent Γ) = (p : ℝ≥0∞) ^ k := by
  exact closedEvent_measure_eq_of_card hμ (mem_AttachedEdgeCandidates_card hΓ)

theorem productBernoulli_closedEvent_eq_of_candidate
    (q : ClosedParameter) {Γ : Finset (OEdge N L)} {k : Nat}
    (hΓ : Γ ∈ AttachedEdgeCandidates N L k) :
    productBernoulliEdgeMeasure N L q (ClosedEvent Γ) =
      (q.1 : ℝ≥0∞) ^ k := by
  exact closedEvent_measure_eq_of_candidate
    (productBernoulliEdgeMeasure_hyp (N := N) (L := L) q) hΓ

theorem measure_noCrossing_le_candidateTail
    (μ : Measure (EdgeConfig N L)) :
    μ (NoCrossingEvent N L) ≤
      μ (CandidateClosedTail N L (LayerSize L)) := by
  exact measure_mono fun X hX => no_crossing_mem_candidateClosedTail X hX

theorem measure_noCrossing_le_candidateTail_from
    (μ : Measure (EdgeConfig N L)) {m : Nat}
    (hm : m ≤ LayerSize L) :
    μ (NoCrossingEvent N L) ≤ μ (CandidateClosedTail N L m) := by
  exact (measure_noCrossing_le_candidateTail (N := N) (L := L) μ).trans
    (measure_mono (candidateClosedTail_mono hm))

theorem measure_noCrossing_le_closed_union
    (μ : Measure (EdgeConfig N L)) :
    μ (NoCrossingEvent N L) ≤
      μ (⋃ k ≥ LayerSize L,
        ⋃ Γ ∈ AttachedEdgeCandidates N L k, ClosedEvent Γ) := by
  simpa [candidateClosedTail_eq_closed_union] using
    measure_noCrossing_le_candidateTail (N := N) (L := L) μ

theorem measure_candidateClosedUnion_le
    {μ : Measure (EdgeConfig N L)} {p : NNReal}
    (hμ : PeierlsMeasureHyp (N := N) (L := L) μ p)
    (k : Nat) :
    μ (CandidateClosedUnion N L k) ≤
      (attachedEdgeCandidateCount N L k : ℝ≥0∞) * (p : ℝ≥0∞) ^ k := by
  refine' le_trans ( MeasureTheory.measure_mono _ ) _;
  exact Set.iUnion fun Γ : { Γ : Finset ( OEdge N L ) // Γ ∈ AttachedEdgeCandidates N L k } => ClosedEvent Γ.val;
  · exact fun x hx => by rcases Set.mem_iUnion₂.1 hx with ⟨ Γ, hΓ, hx ⟩ ; exact Set.mem_iUnion.2 ⟨ ⟨ Γ, hΓ ⟩, hx ⟩ ;
  · refine' le_trans ( MeasureTheory.measure_iUnion_le _ ) _;
    rw [ tsum_congr fun x => closedEvent_measure_eq_of_candidate hμ x.2 ] ; norm_num [ attachedEdgeCandidateCount ];
    rw [ Set.ncard_eq_toFinset_card' ] ; norm_num

theorem measure_candidateClosedTail_le_tsum
    {μ : Measure (EdgeConfig N L)} {p : NNReal}
    (hμ : PeierlsMeasureHyp (N := N) (L := L) μ p)
    (m : Nat) :
    μ (CandidateClosedTail N L m) ≤
      ∑' k : Nat,
        if m ≤ k then
          (attachedEdgeCandidateCount N L k : ℝ≥0∞) * (p : ℝ≥0∞) ^ k
        else 0 := by
  refine' le_trans ( MeasureTheory.measure_iUnion_le _ ) _;
  refine' ENNReal.tsum_le_tsum _;
  intro k; split_ifs <;> simp_all +decide [ measure_candidateClosedUnion_le ] ;

theorem measure_noCrossing_le_tsum
    {μ : Measure (EdgeConfig N L)} {p : NNReal}
    (hμ : PeierlsMeasureHyp (N := N) (L := L) μ p) :
    μ (NoCrossingEvent N L) ≤
      ∑' k : Nat,
        if LayerSize L ≤ k then
          (attachedEdgeCandidateCount N L k : ℝ≥0∞) * (p : ℝ≥0∞) ^ k
        else 0 := by
  exact (measure_noCrossing_le_candidateTail (N := N) (L := L) μ).trans
    (measure_candidateClosedTail_le_tsum (N := N) (L := L) hμ (LayerSize L))

theorem productBernoulli_noCrossing_le_tsum
    (q : ClosedParameter) :
    productBernoulliEdgeMeasure N L q (NoCrossingEvent N L) ≤
      ∑' k : Nat,
        if LayerSize L ≤ k then
          (attachedEdgeCandidateCount N L k : ℝ≥0∞) * (q.1 : ℝ≥0∞) ^ k
        else 0 := by
  exact measure_noCrossing_le_tsum
    (productBernoulliEdgeMeasure_hyp (N := N) (L := L) q)

theorem closed_attached_edges_event
    (X : EdgeConfig N L)
    (hX : X ∈ NoCrossingEvent N L) :
    X ∈ ClosedEvent (attachedBoundaryEdges (stochasticOpen N L X)) := by
  exact attachedBoundaryEdges_closed_for_raw X hX

theorem no_crossing_event_subset_closed_union :
    NoCrossingEvent N L ⊆
      ⋃ k ≥ LayerSize L,
        ⋃ Γ ∈ AttachedEdgeCandidates N L k, ClosedEvent Γ := by
  intro X hX
  simpa [candidateClosedTail_eq_closed_union] using
    no_crossing_mem_candidateClosedTail X hX

theorem exp_condition_of_log_condition
    {N L : Nat} (hN : 1 ≤ N)
    (hlog : Real.log (N : Real) ≤ (L : Real)) :
    (N : Real) ≤ Real.exp (L : Real) := by
  calc (N : Real) ≤ Real.exp (Real.log (N : Real)) := by
        rw [Real.exp_log (by positivity)]
    _ ≤ Real.exp (L : Real) := Real.exp_le_exp.mpr hlog

theorem logslab_peierls
    (A : Real) (hA : 1 < A) :
    ∃ p0 : NNReal, 0 < p0 ∧ p0 < 1 ∧
      ∀ {N L : Nat},
        3 ≤ N →
        3 ≤ L →
        (N : Real) ≤ Real.exp (L : Real) →
        ∀ {p : NNReal},
          0 < p →
          p < p0 →
          ∀ μ : Measure (EdgeConfig N L),
            PeierlsMeasureHyp (N := N) (L := L) μ p →
              μ (NoCrossingEvent N L) ≤
                ENNReal.ofReal (Real.exp (-(A * (L : Real) ^ 2))) := by
  obtain ⟨ C, hC ⟩ := counting_candidates;
  refine' ⟨ ⟨ Real.exp ( - ( C + Real.log 9 + A + 1 ) ), _ ⟩, _, _, _ ⟩ <;> norm_num [ Real.exp_pos ];
  exact Real.exp_nonneg _;
  · exact Subtype.mk_lt_mk.mpr ( Real.exp_pos _ );
  · exact Subtype.mk_lt_mk.mpr ( Real.exp_lt_one_iff.mpr ( by linarith [ Real.log_pos ( by norm_num : ( 9 : ℝ ) > 1 ) ] ) );
  · intro N L hN hL hNL p hp hp' μ hμ
    have h_sum : μ (NoCrossingEvent N L) ≤ ∑' k : ℕ, (if LayerSize L ≤ k then (attachedEdgeCandidateCount N L k : ℝ≥0∞) * (p : ℝ≥0∞) ^ k else 0) := by
      convert measure_noCrossing_le_tsum hμ using 1;
    -- Apply the bound on the attached edge candidate count.
    have h_bound : ∀ k ≥ LayerSize L, (attachedEdgeCandidateCount N L k : ℝ≥0∞) * (p : ℝ≥0∞) ^ k ≤ ENNReal.ofReal (Real.exp (-(A + 1) * k)) := by
      intro k hk
      have h_bound : (attachedEdgeCandidateCount N L k : ℝ) * (p : ℝ) ^ k ≤ Real.exp ((C + Real.log 9) * k) * (Real.exp (-(C + Real.log 9 + A + 1))) ^ k := by
        gcongr;
        · exact hC.2 N L k hN hL hNL ( by linarith [ show LayerSize L ≥ 1 from Nat.one_le_pow _ _ ( by linarith ) ] ) |>.2;
        · exact le_trans ( NNReal.coe_le_coe.mpr hp'.le ) ( by ring_nf; norm_num );
      convert ENNReal.ofReal_le_ofReal h_bound using 1;
      · rw [ ENNReal.ofReal_mul ( Nat.cast_nonneg _ ), ENNReal.ofReal_pow ( NNReal.coe_nonneg _ ) ] ; norm_num;
      · rw [ ← Real.exp_nat_mul, ← Real.exp_add ] ; ring_nf;
    -- Apply the geometric series bound.
    have h_geo_series : ∑' k : ℕ, (if LayerSize L ≤ k then ENNReal.ofReal (Real.exp (-(A + 1) * k)) else 0) ≤ ENNReal.ofReal (Real.exp (-(A + 1) * LayerSize L) / (1 - Real.exp (-(A + 1)))) := by
      have h_geo_series : ∑' k : ℕ, (if LayerSize L ≤ k then Real.exp (-(A + 1) * k) else 0) ≤ Real.exp (-(A + 1) * LayerSize L) / (1 - Real.exp (-(A + 1))) := by
        have h_geo_series : ∑' k : ℕ, (if LayerSize L ≤ k then Real.exp (-(A + 1) * k) else 0) = ∑' k : ℕ, Real.exp (-(A + 1) * (k + LayerSize L)) := by
          rw [ ← Summable.sum_add_tsum_nat_add ( LayerSize L ) ];
          · rw [ Finset.sum_eq_zero ] <;> aesop;
          · rw [ ← summable_nat_add_iff ( LayerSize L ) ];
            norm_num [ Real.exp_add, Real.exp_neg, Real.exp_mul ];
            exact_mod_cast Summable.comp_injective ( summable_geometric_of_lt_one ( by positivity ) ( show ( Real.exp 1 ) ⁻¹ * ( Real.exp A ) ⁻¹ < 1 by exact lt_of_le_of_lt ( mul_le_of_le_one_right ( by positivity ) ( inv_le_one_of_one_le₀ ( Real.one_le_exp ( by linarith ) ) ) ) ( inv_lt_one_of_one_lt₀ ( by norm_num ) ) ) ) ( add_left_injective _ );
        rw [ h_geo_series, div_eq_mul_inv ];
        rw [ ← tsum_geometric_of_lt_one ( by positivity ) ( by rw [ Real.exp_lt_one_iff ] ; linarith ) ];
        rw [ ← tsum_mul_left ] ; exact le_of_eq <| tsum_congr fun n => by rw [ ← Real.exp_nat_mul ] ; rw [ ← Real.exp_add ] ; ring_nf;
      convert ENNReal.ofReal_le_ofReal h_geo_series using 1;
      rw [ ENNReal.ofReal_tsum_of_nonneg ];
      · exact tsum_congr fun n => by split_ifs <;> simp +decide [ * ] ;
      · exact fun n => by split_ifs <;> positivity;
      · have h_geo_series : Summable (fun k : ℕ => Real.exp (-(A + 1) * k)) := by
          have h_geo_series : Summable (fun k : ℕ => (Real.exp (-(A + 1))) ^ k) := by
            exact summable_geometric_of_lt_one ( by positivity ) ( by rw [ Real.exp_lt_one_iff ] ; linarith );
          exact h_geo_series.congr fun k => by rw [ ← Real.exp_nat_mul ] ; ring_nf;
        exact Summable.of_nonneg_of_le ( fun k => by split_ifs <;> positivity ) ( fun k => by split_ifs <;> first | positivity | aesop ) h_geo_series;
    refine' le_trans h_sum ( le_trans ( ENNReal.tsum_le_tsum fun k => _ ) ( le_trans h_geo_series _ ) );
    · split_ifs <;> [ exact h_bound k ‹_›; exact zero_le _ ];
    · refine' ENNReal.ofReal_le_ofReal _;
      rw [ div_le_iff₀ ] <;> norm_num [ LayerSize ];
      · refine' le_trans _ ( mul_le_mul_of_nonneg_left ( show 1 - Real.exp ( -1 + -A ) ≥ 1 / 2 by nlinarith [ Real.exp_pos ( -1 + -A ), Real.exp_neg ( -1 + -A ), mul_inv_cancel₀ ( ne_of_gt ( Real.exp_pos ( -1 + -A ) ) ), Real.add_one_le_exp ( -1 + -A ), Real.add_one_le_exp ( - ( -1 + -A ) ) ] ) ( by positivity ) );
        rw [ ← Real.log_le_log_iff ( by positivity ) ( by positivity ), Real.log_mul ( by positivity ) ( by positivity ), Real.log_exp, Real.log_exp ];
        rw [ Real.log_div ] <;> norm_num ; nlinarith [ show ( L : ℝ ) ≥ 3 by norm_cast, Real.log_le_sub_one_of_pos ( by positivity : 0 < ( 2 : ℝ ) ) ];
      · linarith

theorem logslab_peierls_of_log_le
    (A : Real) (hA : 1 < A) :
    ∃ p0 : NNReal, 0 < p0 ∧ p0 < 1 ∧
      ∀ {N L : Nat},
        3 ≤ N →
        3 ≤ L →
        Real.log (N : Real) ≤ (L : Real) →
        ∀ {p : NNReal},
          0 < p →
          p < p0 →
          ∀ μ : Measure (EdgeConfig N L),
            PeierlsMeasureHyp (N := N) (L := L) μ p →
              μ (NoCrossingEvent N L) ≤
                ENNReal.ofReal (Real.exp (-(A * (L : Real) ^ 2))) := by
  obtain ⟨p0, hp0_pos, hp0_lt, hmain⟩ := logslab_peierls A hA
  refine ⟨p0, hp0_pos, hp0_lt, ?_⟩
  intro N L hN hL hlog p hp_pos hp_lt μ hμ
  exact hmain hN hL
    (exp_condition_of_log_condition (N := N) (L := L) (by omega) hlog)
    hp_pos hp_lt μ hμ

theorem logslab_peierls_productBernoulli
    (A : Real) (hA : 1 < A) :
    ∃ p0 : NNReal, 0 < p0 ∧ p0 < 1 ∧
      ∀ {N L : Nat},
        3 ≤ N →
        3 ≤ L →
        (N : Real) ≤ Real.exp (L : Real) →
        ∀ p : ClosedParameter,
          0 < p.1 →
          p.1 < p0 →
          productBernoulliEdgeMeasure N L p (NoCrossingEvent N L) ≤
            ENNReal.ofReal (Real.exp (-(A * (L : Real) ^ 2))) := by
  obtain ⟨p0, hp0_pos, hp0_lt, hmain⟩ := logslab_peierls A hA
  refine ⟨p0, hp0_pos, hp0_lt, ?_⟩
  intro N L hN hL hNL p hp_pos hp_lt
  exact hmain hN hL hNL hp_pos hp_lt
    (productBernoulliEdgeMeasure N L p)
    (productBernoulliEdgeMeasure_hyp (N := N) (L := L) p)

end

end OrientedAnimal
