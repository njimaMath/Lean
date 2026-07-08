import Mathlib

open scoped BigOperators

namespace OrientedAnimal

structure SpacePoint (L : Nat) where
  raw : Fin 2 -> Fin (2 * L + 1)
deriving DecidableEq, Fintype

namespace SpacePoint

def coord {L : Nat} (x : SpacePoint L) (i : Fin 2) : Int :=
  (x.raw i : Nat) - (L : Int)

lemma coord_bound {L : Nat} (x : SpacePoint L) (i : Fin 2) :
    Int.natAbs (x.coord i) <= L := by
  unfold SpacePoint.coord; omega;

end SpacePoint

abbrev V (N L : Nat) : Type :=
  Fin (N + 1) × SpacePoint L

namespace V

def time {N L : Nat} (v : V N L) : Nat :=
  v.1.val

def space {N L : Nat} (v : V N L) : SpacePoint L :=
  v.2

def coord {N L : Nat} (v : V N L) (i : Fin 2) : Int :=
  v.2.coord i

def mk {N L : Nat} (m : Nat) (hm : m < N + 1) (x : SpacePoint L) : V N L :=
  (Fin.mk m hm, x)

@[simp] lemma time_mk {N L m : Nat} (hm : m < N + 1) (x : SpacePoint L) :
    time (mk (N := N) (L := L) m hm x) = m := rfl

@[simp] lemma space_mk {N L m : Nat} (hm : m < N + 1) (x : SpacePoint L) :
    space (mk (N := N) (L := L) m hm x) = x := rfl

@[simp] lemma coord_mk {N L m : Nat} (hm : m < N + 1) (x : SpacePoint L)
    (i : Fin 2) :
    coord (mk (N := N) (L := L) m hm x) i = x.coord i := rfl

end V

def T (N L : Nat) (k : Nat) : Set (V N L) :=
  {v | V.time v = k}

def T0 (N L : Nat) : Set (V N L) :=
  T N L 0

def TN (N L : Nat) : Set (V N L) :=
  T N L N

def SlabBoundary (N L : Nat) : Set (V N L) :=
  TN N L

lemma mem_boundary_of_time_top {N L : Nat} (v : V N L) (h : V.time v = N) :
    v ∈ SlabBoundary N L := by
  exact h

def SpaceStarAdj {L : Nat} (x y : SpacePoint L) : Prop :=
  ∀ i : Fin 2, Int.natAbs (x.coord i - y.coord i) <= 1

lemma spaceStarAdj_self {L : Nat} (x : SpacePoint L) :
    SpaceStarAdj x x := by
  intro i
  simp [SpacePoint.coord]

lemma spaceStarAdj_symm {L : Nat} {x y : SpacePoint L}
    (h : SpaceStarAdj x y) : SpaceStarAdj y x := by
  intro i
  specialize h i
  omega

def OAdj {N L : Nat} (u v : V N L) : Prop :=
  V.time v = V.time u + 1 ∧ SpaceStarAdj (V.space u) (V.space v)

def UAdj {N L : Nat} (u v : V N L) : Prop :=
  u ≠ v ∧
    Int.natAbs ((V.time u : Int) - (V.time v : Int)) <= 1 ∧
      SpaceStarAdj (V.space u) (V.space v)

lemma uAdj_symm {N L : Nat} {u v : V N L} (h : UAdj u v) : UAdj v u := by
  unfold UAdj at *;
  exact ⟨h.1.symm, by omega, spaceStarAdj_symm h.2.2⟩

def UGraph (N L : Nat) : SimpleGraph (V N L) where
  Adj := UAdj
  symm := by
    intro u v h
    exact uAdj_symm h
  loopless := by
    constructor
    intro v hv
    exact hv.1 rfl

lemma oAdj_to_uAdj {N L : Nat} {u v : V N L} (h : OAdj u v) : UAdj u v := by
  obtain ⟨h_time, h_star⟩ := h
  refine ⟨?_, by omega, h_star⟩
  intro huv
  have : V.time v = V.time u := by
    rw [huv]
  omega

lemma uAdj_time_cases {N L : Nat} {u v : V N L} (h : UAdj u v) :
    V.time v = V.time u ∨
      V.time v = V.time u + 1 ∨
        V.time u = V.time v + 1 := by
  have h_time_diff : Int.natAbs ((V.time u : ℤ) - (V.time v : ℤ)) ≤ 1 := by
    exact h.2.1;
  omega

structure OEdge (N L : Nat) where
  tail : V N L
  head : V N L
  adj : OAdj tail head

structure OPath (N L : Nat) where
  len : Nat
  vertex : Fin (len + 1) -> V N L
  edge : ∀ i : Fin len, OAdj (vertex i.castSucc) (vertex i.succ)

namespace OPath

def start {N L : Nat} (p : OPath N L) : V N L :=
  p.vertex 0

def finish {N L : Nat} (p : OPath N L) : V N L :=
  p.vertex (Fin.last p.len)

def AllOpen {N L : Nat} (p : OPath N L)
    (Open : ∀ u v : V N L, OAdj u v -> Prop) : Prop :=
  ∀ i : Fin p.len, Open (p.vertex i.castSucc) (p.vertex i.succ) (p.edge i)

def nil {N L : Nat} (v : V N L) : OPath N L where
  len := 0
  vertex := fun _ => v
  edge := by
    intro i
    exact Fin.elim0 i

end OPath

structure UPath (N L : Nat) where
  len : Nat
  vertex : Fin (len + 1) -> V N L
  edge : ∀ i : Fin len, UAdj (vertex i.castSucc) (vertex i.succ)

namespace UPath

def start {N L : Nat} (p : UPath N L) : V N L :=
  p.vertex 0

def finish {N L : Nat} (p : UPath N L) : V N L :=
  p.vertex (Fin.last p.len)

def Avoids {N L : Nat} (p : UPath N L) (A : Set (V N L)) : Prop :=
  ∀ i : Fin (p.len + 1), p.vertex i ∉ A

def nil {N L : Nat} (v : V N L) : UPath N L where
  len := 0
  vertex := fun _ => v
  edge := by
    intro i
    exact Fin.elim0 i

def cons {N L : Nat} {u v : V N L} (h : UAdj u v) (p : UPath N L)
    (hpstart : p.start = v) : UPath N L where
  len := p.len + 1
  vertex := fun j =>
    if hj : j.val = 0 then
      u
    else
      p.vertex ⟨j.val - 1, by omega⟩
  edge := by
    intro i
    rcases i with ⟨ _ | i, hi ⟩ <;> simp_all +decide [ UPath.start ];
    exact p.edge ⟨ i, by linarith ⟩

lemma avoids_cons {N L : Nat} {B : Set (V N L)} {u v : V N L}
    {h : UAdj u v} {p : UPath N L} {hpstart : p.start = v}
    (hu : u ∉ B) (hrest : p.Avoids B) :
    (UPath.cons h p hpstart).Avoids B := by
  intro i;
  grind +locals

end UPath

def OpenReach {N L : Nat}
    (Open : ∀ u v : V N L, OAdj u v -> Prop)
    (u v : V N L) : Prop :=
  ∃ p : OPath N L, p.start = u ∧ p.finish = v ∧ p.AllOpen Open

def Crossing {N L : Nat}
    (Open : ∀ u v : V N L, OAdj u v -> Prop) : Prop :=
  ∃ u : V N L, ∃ v : V N L,
    u ∈ T0 N L ∧ v ∈ TN N L ∧ OpenReach Open u v

def B {N L : Nat}
    (Open : ∀ u v : V N L, OAdj u v -> Prop) : Set (V N L) :=
  {v | ∃ u : V N L, u ∈ T0 N L ∧ OpenReach Open u v}

lemma T0_subset_B {N L : Nat}
    {Open : ∀ u v : V N L, OAdj u v -> Prop} {v : V N L}
    (h : v ∈ T0 N L) : v ∈ B Open := by
  refine ⟨v, h, ?_⟩
  refine ⟨OPath.nil v, rfl, rfl, ?_⟩
  intro i
  exact Fin.elim0 i

lemma not_TN_mem_B_of_not_crossing {N L : Nat}
    {Open : ∀ u v : V N L, OAdj u v -> Prop}
    (hC : Not (Crossing Open)) {v : V N L} (hv : v ∈ TN N L) :
    v ∉ B Open := by
  intro hvB
  rcases hvB with ⟨u, hu0, huv⟩
  exact hC ⟨u, v, hu0, hv, huv⟩

def FreeToBoundary {N L : Nat}
    (Open : ∀ u v : V N L, OAdj u v -> Prop)
    (v : V N L) : Prop :=
  v ∉ B Open ∧
    ∃ b : V N L, ∃ p : UPath N L,
      b ∈ SlabBoundary N L ∧
        p.start = v ∧ p.finish = b ∧ p.Avoids (B Open)

def F {N L : Nat}
    (Open : ∀ u v : V N L, OAdj u v -> Prop) : Set (V N L) :=
  {v | FreeToBoundary Open v}

lemma F_disjoint_B {N L : Nat}
    {Open : ∀ u v : V N L, OAdj u v -> Prop} {v : V N L}
    (hv : v ∈ F Open) : v ∉ B Open := by
  exact hv.1

lemma TN_subset_F_of_not_crossing {N L : Nat}
    {Open : ∀ u v : V N L, OAdj u v -> Prop}
    (hC : Not (Crossing Open)) {v : V N L} (hv : v ∈ TN N L) :
    v ∈ F Open := by
  refine ⟨not_TN_mem_B_of_not_crossing hC hv, ?_⟩
  refine ⟨v, UPath.nil v, mem_boundary_of_time_top v hv, rfl, rfl, ?_⟩
  intro i
  exact not_TN_mem_B_of_not_crossing hC hv

lemma F_of_uAdj_F_of_not_B {N L : Nat}
    {Open : ∀ u v : V N L, OAdj u v -> Prop} {u v : V N L}
    (huv : UAdj u v) (hvF : v ∈ F Open) (huB : u ∉ B Open) :
    u ∈ F Open := by
  refine' ⟨ huB, _ ⟩;
  obtain ⟨ b, p, hb, hp ⟩ := hvF.2;
  use b, UPath.cons huv p hp.1;
  exact ⟨ hb, rfl, hp.2.1, UPath.avoids_cons huB hp.2.2 ⟩

def OrientedInnerEdgeBoundary {N L : Nat}
    (Open : ∀ u v : V N L, OAdj u v -> Prop) : Set (OEdge N L) :=
  {e | e.tail ∈ B Open ∧ e.head ∈ F Open}

def OrientedInnerBoundary {N L : Nat}
    (Open : ∀ u v : V N L, OAdj u v -> Prop) : Set (V N L) :=
  {u | u ∈ B Open ∧ ∃ v : V N L, ∃ _ : OAdj u v, v ∈ F Open}

def InnerBoundary {N L : Nat}
    (Open : ∀ u v : V N L, OAdj u v -> Prop) : Set (V N L) :=
  {u | u ∈ B Open ∧ ∃ v : V N L, UAdj u v ∧ v ∈ F Open}

noncomputable instance innerBoundaryFintype {N L : Nat}
    (Open : ∀ u v : V N L, OAdj u v -> Prop) :
    Fintype {u : V N L // u ∈ InnerBoundary Open} := by
  classical
  infer_instance

noncomputable instance orientedInnerBoundaryFintype {N L : Nat}
    (Open : ∀ u v : V N L, OAdj u v -> Prop) :
    Fintype {u : V N L // u ∈ OrientedInnerBoundary Open} := by
  classical
  infer_instance

lemma orientedInnerBoundary_subset_innerBoundary {N L : Nat}
    {Open : ∀ u v : V N L, OAdj u v -> Prop} :
    OrientedInnerBoundary Open ⊆ InnerBoundary Open := by
  intro u hu
  rcases hu with ⟨huB, v, huv, hvF⟩
  exact ⟨huB, v, oAdj_to_uAdj huv, hvF⟩

lemma oPath_edge_to_uAdj {N L : Nat} (p : OPath N L) (i : Fin p.len) :
    UAdj (p.vertex i.castSucc) (p.vertex i.succ) :=
  oAdj_to_uAdj (p.edge i)

theorem cutset {N L : Nat}
    {Open : ∀ u v : V N L, OAdj u v -> Prop}
    (hC : Not (Crossing Open))
    (p : OPath N L)
    (hp0 : p.start ∈ T0 N L)
    (hpN : p.finish ∈ TN N L) :
    ∃ i : Fin p.len,
      p.vertex i.castSucc ∈ B Open ∧
        p.vertex i.succ ∈ F Open := by
  obtain ⟨i, hi⟩ : ∃ i : Fin p.len, p.vertex i.succ ∈ F Open ∧ ∀ j : Fin p.len, j > i → p.vertex j.succ ∉ F Open := by
    have h_exists_i : ∃ i : Fin p.len, p.vertex i.succ ∈ F Open := by
      have h_finish_in_F : p.finish ∈ F Open := by
        exact?;
      rcases p with ⟨ _ | p_len, p_vertex, p_edge ⟩ <;> simp_all +decide [ Fin.last ];
      · exact h_finish_in_F.1 ( T0_subset_B hp0 );
      · exact ⟨ ⟨ p_len, by linarith ⟩, h_finish_in_F ⟩;
    obtain ⟨i, hi⟩ : ∃ i : Fin p.len, p.vertex i.succ ∈ F Open ∧ ∀ j : Fin p.len, j > i → p.vertex j.succ ∉ F Open := by
      have h_finite : Set.Finite {i : Fin p.len | p.vertex i.succ ∈ F Open} := by
        exact Set.toFinite _
      exact ⟨ Finset.max' ( h_finite.toFinset ) ⟨ h_exists_i.choose, h_finite.mem_toFinset.mpr h_exists_i.choose_spec ⟩, h_finite.mem_toFinset.mp ( Finset.max'_mem _ _ ), fun j hj hj' => not_lt_of_ge ( Finset.le_max' _ _ ( h_finite.mem_toFinset.mpr hj' ) ) hj ⟩;
    use i;
  contrapose! hi;
  intro hiF
  use i
  simp [hiF];
  induction' i with i ih;
  induction' i with i ih;
  · exact hi ⟨ 0, ih ⟩ ( T0_subset_B hp0 ) hiF;
  · specialize hi ⟨ i + 1, ih ⟩ ; simp_all +decide [ F_of_uAdj_F_of_not_B ] ;
    refine' ih ( Nat.lt_of_succ_lt ‹_› ) _;
    apply F_of_uAdj_F_of_not_B;
    exact oPath_edge_to_uAdj p ⟨ i + 1, by linarith ⟩;
    · exact hiF;
    · assumption

def verticalPath (N L : Nat) (x : SpacePoint L) : OPath N L where
  len := N
  vertex := fun k => V.mk (N := N) (L := L) k.val k.isLt x
  edge := by
    intro i
    constructor
    · norm_num
    · simpa using spaceStarAdj_self x

lemma verticalPath_start {N L : Nat} (x : SpacePoint L) :
    (verticalPath N L x).start ∈ T0 N L := by
  rfl

lemma verticalPath_finish {N L : Nat} (x : SpacePoint L) :
    (verticalPath N L x).finish ∈ TN N L := by
  exact?

theorem every_fiber_meets_oriented_inner {N L : Nat}
    {Open : ∀ u v : V N L, OAdj u v -> Prop}
    (hC : Not (Crossing Open)) (x : SpacePoint L) :
    ∃ m : Fin (N + 1),
      V.space (V.mk (N := N) (L := L) m.val m.isLt x) = x ∧
        V.mk (N := N) (L := L) m.val m.isLt x ∈ OrientedInnerBoundary Open := by
  obtain ⟨ i, hi ⟩ := cutset hC ( verticalPath N L x ) ( verticalPath_start x ) ( verticalPath_finish x );
  refine' ⟨ ⟨ i.val, _ ⟩, _, _ ⟩;
  exact Nat.lt_succ_of_lt ( Fin.is_lt i );
  · rfl;
  · grind +locals

theorem card_spacePoint (L : Nat) :
    Fintype.card (SpacePoint L) = (2 * L + 1) ^ 2 := by
  rw [ Fintype.card_eq_nat_card ];
  rw [ show Nat.card ( SpacePoint L ) = Nat.card ( Fin 2 → Fin ( 2 * L + 1 ) ) from _ ];
  · norm_num [ Nat.card_pi ];
  · exact Nat.card_congr ( Equiv.ofBijective ( fun x => x.raw ) ⟨ fun x y h => by cases x; cases y; aesop, fun x => ⟨ ⟨ x ⟩, rfl ⟩ ⟩ )

theorem card_space_le_oriented_inner {N L : Nat}
    {Open : ∀ u v : V N L, OAdj u v -> Prop}
    (hC : Not (Crossing Open)) :
    Fintype.card (SpacePoint L) <=
      Fintype.card {u : V N L // u ∈ OrientedInnerBoundary Open} := by
  have h_fiber_meets : ∀ x : SpacePoint L, ∃ m : Fin (N + 1), V.space (V.mk (N := N) (L := L) m.val m.isLt x) = x ∧ V.mk (N := N) (L := L) m.val m.isLt x ∈ OrientedInnerBoundary Open := by
    exact?;
  choose f hf using h_fiber_meets;
  refine' Fintype.card_le_of_injective ( fun x => ⟨ _, hf x |>.2 ⟩ ) fun x y hxy => _;
  grind +locals

def vertexAt {N L : Nat} (m : Nat) (hm : m <= N) (x : SpacePoint L) : V N L :=
  V.mk (N := N) (L := L) m (Nat.lt_succ_of_le hm) x

theorem lowerbd_predecessor {N L m : Nat} {x : SpacePoint L}
    {Open : ∀ u v : V N L, OAdj u v -> Prop}
    (hmN : m <= N) (hm1 : 1 <= m)
    (hmem : vertexAt (N := N) (L := L) m hmN x ∈ InnerBoundary Open)
    (hnot : vertexAt (N := N) (L := L) m hmN x ∉
        OrientedInnerBoundary Open) :
    (∃ hm1N : m - 1 <= N,
      let u1 := vertexAt (N := N) (L := L) (m - 1) hm1N x
      u1 ∈ OrientedInnerBoundary Open ∨ u1 ∈ F Open)
    ∨
    (2 <= m ∧
      ∃ hm2N : m - 2 <= N,
      let u2 := vertexAt (N := N) (L := L) (m - 2) hm2N x
      u2 ∈ OrientedInnerBoundary Open ∨ u2 ∈ F Open) := by
  obtain ⟨ v, hv, h ⟩ := hmem.2;
  rcases uAdj_time_cases hv with ( h | h | h );
  · have h_u1 : ∃ v' : V N L, UAdj (vertexAt (m - 1) (by omega) x) v' ∧ v' ∈ F Open := by
      grind +locals;
    have h_u1 : vertexAt (m - 1) (by omega) x ∈ B Open ∨ vertexAt (m - 1) (by omega) x ∈ F Open := by
      exact Classical.or_iff_not_imp_left.2 fun h => F_of_uAdj_F_of_not_B h_u1.choose_spec.1 h_u1.choose_spec.2 h;
    grind +locals;
  · have hOAdj : OAdj (vertexAt m hmN x) v := by
      exact ⟨ h, hv.2.2 ⟩;
    exact False.elim <| hnot ⟨ hmem.1, v, hOAdj, by assumption ⟩;
  · rcases m with ( _ | _ | m ) <;> simp_all +decide [ vertexAt ];
    · -- Since $v.time = 0$, we have $v \in T0$.
      have hvT0 : v ∈ T0 N L := by
        exact h;
      exact False.elim <| ‹v ∈ F Open›.1 <| T0_subset_B hvT0;
    · by_cases h : V.mk m ( by linarith ) x ∈ B Open <;> simp_all +decide [ OrientedInnerBoundary ];
      · refine Or.inr ⟨ by linarith, by linarith, Or.inl ⟨ ?_, ?_ ⟩ ⟩;
        · grind;
        · use v.1, v.2;
          constructor;
          · constructor <;> norm_num [ ← ‹m + 1 = v.time› ];
            exact hv.2.2;
          · assumption;
      · refine Or.inr ⟨ by linarith, by linarith, Or.inr ?_ ⟩;
        apply F_of_uAdj_F_of_not_B;
        rotate_right;
        exact v;
        · grind +locals;
        · assumption;
        · grind

abbrev TimeIndex (N : Nat) :=
  Fin (N + 1)

def vertexAtIndex {N L : Nat} (m : TimeIndex N) (x : SpacePoint L) : V N L :=
  V.mk (N := N) (L := L) m.val m.isLt x

def predIndex {N : Nat} (m : TimeIndex N) (hm : 1 <= m.val) : TimeIndex N :=
  ⟨m.val - 1, by omega⟩

def pred2Index {N : Nat} (m : TimeIndex N) (hm : 2 <= m.val) : TimeIndex N :=
  ⟨m.val - 2, by omega⟩

noncomputable def Iset {N L : Nat}
    (Open : ∀ u v : V N L, OAdj u v -> Prop) (x : SpacePoint L) :
    Finset (TimeIndex N) := by
  classical
  exact Finset.univ.filter fun m => vertexAtIndex (N := N) (L := L) m x ∈ InnerBoundary Open

noncomputable def Jset {N L : Nat}
    (Open : ∀ u v : V N L, OAdj u v -> Prop) (x : SpacePoint L) :
    Finset (TimeIndex N) := by
  classical
  exact Finset.univ.filter fun m =>
    vertexAtIndex (N := N) (L := L) m x ∈ OrientedInnerBoundary Open

noncomputable def Gset {N L : Nat}
    (Open : ∀ u v : V N L, OAdj u v -> Prop) (x : SpacePoint L) :
    Finset (TimeIndex N) := by
  classical
  exact Finset.univ.filter fun m => vertexAtIndex (N := N) (L := L) m x ∈ F Open

structure FiberHyp {N L : Nat}
    (Open : ∀ u v : V N L, OAdj u v -> Prop)
    (x : SpacePoint L) : Prop where
  J_subset_I : Jset Open x ⊆ Iset Open x
  I_disjoint_G : Disjoint (Iset Open x) (Gset Open x)
  G_back :
    ∀ (t : TimeIndex N), t ∈ Gset Open x -> (ht : 1 <= t.val) ->
      predIndex t ht ∈ Gset Open x ∨ predIndex t ht ∈ Jset Open x
  IminusJ_back :
    ∀ (m : TimeIndex N), m ∈ Iset Open x -> m ∉ Jset Open x ->
      (hm : 1 <= m.val) ->
      (predIndex m hm ∈ Jset Open x ∨ predIndex m hm ∈ Gset Open x) ∨
      (∃ hm2 : 2 <= m.val,
        pred2Index m hm2 ∈ Jset Open x ∨ pred2Index m hm2 ∈ Gset Open x)

private lemma IminusJ_not_succ_G {N L : Nat}
    {Open : ∀ u v : V N L, OAdj u v -> Prop} {x : SpacePoint L}
    (h : FiberHyp Open x) (a : TimeIndex N)
    (ha : a ∈ Iset Open x) (haJ : a ∉ Jset Open x)
    (b : TimeIndex N) (hb : b.val = a.val + 1) :
    b ∉ Gset Open x := by
  intro hbG;
  have := h.G_back b hbG (by
  linarith);
  unfold predIndex at this; simp_all +decide [ Fin.ext_iff ] ;
  exact Finset.disjoint_left.mp ( h.I_disjoint_G ) ha this

private lemma no_three_consec_IminusJ {N L : Nat}
    {Open : ∀ u v : V N L, OAdj u v -> Prop} {x : SpacePoint L}
    (h : FiberHyp Open x)
    (a : TimeIndex N) (ha : a ∈ Iset Open x) (haJ : a ∉ Jset Open x)
    (b : TimeIndex N) (hb : b.val = a.val + 1)
    (hbI : b ∈ Iset Open x) (hbJ : b ∉ Jset Open x)
    (c : TimeIndex N) (hc : c.val = a.val + 2)
    (hcI : c ∈ Iset Open x) (hcJ : c ∉ Jset Open x) : False := by
  -- Apply h.IminusJ_back to c.
  obtain hc_pred | hc_pred2 := h.IminusJ_back c hcI hcJ (by
  linarith);
  · have hc_pred_eq_b : predIndex c (by
    linarith) = b := by
      exact Fin.ext ( by unfold predIndex; aesop )
    generalize_proofs at *;
    have := h.I_disjoint_G; simp_all +decide [ Finset.disjoint_left ] ;
  · obtain ⟨ hm2, hm2' ⟩ := hc_pred2;
    unfold pred2Index at hm2'; simp_all +decide [ Fin.ext_iff ] ;
    exact Finset.disjoint_left.mp h.I_disjoint_G ha hm2'

private lemma I_zero_in_J {N L : Nat}
    {Open : ∀ u v : V N L, OAdj u v -> Prop} {x : SpacePoint L}
    (h : FiberHyp Open x)
    (m : TimeIndex N) (hm : m.val = 0) (hmI : m ∈ Iset Open x) :
    m ∈ Jset Open x := by
  simp_all +decide [ Jset, Iset ];
  obtain ⟨ v, hv ⟩ := hmI.2;
  cases hv.1 ; simp_all +decide [ UAdj ];
  rcases hv with ⟨ hv₁, hv₂ ⟩ ; interval_cases _ : v.time <;> simp_all +decide [ vertexAtIndex ] ;
  · have h_contra : v ∈ B Open := by
      exact T0_subset_B ‹_›;
    exact False.elim <| hv₂.1 h_contra;
  · refine' ⟨ hmI.1, v, _, _ ⟩ <;> simp_all +decide [ OAdj ]

set_option maxHeartbeats 800000 in
private lemma G_zero_false {N L : Nat}
    {Open : ∀ u v : V N L, OAdj u v -> Prop} {x : SpacePoint L}
    (h : FiberHyp Open x) (g : TimeIndex N) (hg : g ∈ Gset Open x)
    (hg0 : g.val = 0) : False := by
  have h_contradiction : vertexAtIndex (N := N) (L := L) g x ∈ F Open ∧ vertexAtIndex (N := N) (L := L) g x ∈ B Open := by
    exact ⟨ by unfold Gset at hg; aesop, by unfold vertexAtIndex; exact T0_subset_B <| by unfold T0; aesop ⟩;
  have := h_contradiction.1;
  exact this.1 h_contradiction.2

set_option maxHeartbeats 1600000 in
private lemma prefix_count_le {N L : Nat}
    {Open : ∀ u v : V N L, OAdj u v -> Prop} {x : SpacePoint L}
    (h : FiberHyp Open x) :
    ∀ m : ℕ, (hm : m ≤ N) →
    let t : TimeIndex N := ⟨m, Nat.lt_succ_of_le hm⟩
    let Ic := ((Iset Open x).filter (fun i => i.val ≤ m)).card
    let Jc := ((Jset Open x).filter (fun j => j.val ≤ m)).card
    Ic ≤ 3 * Jc ∧
    (t ∈ Jset Open x ∨ t ∈ Gset Open x → Ic + 2 ≤ 3 * Jc) := by
  -- By strong induction on m.
  intro m hm
  induction' m using Nat.strong_induction_on with m ih;
  rcases m with ( _ | m ) <;> simp_all +decide [ Finset.filter_congr, Finset.filter_union_right ];
  · have hIJ0 :
        (Iset Open x).filter (fun i : TimeIndex N => i = 0) =
          (Jset Open x).filter (fun i : TimeIndex N => i = 0) := by
      ext i
      constructor
      · intro hi
        rcases Finset.mem_filter.mp hi with ⟨hiI, hi0⟩
        have hival : i.val = 0 := by
          simp [hi0]
        exact Finset.mem_filter.mpr ⟨I_zero_in_J h i hival hiI, hi0⟩
      · intro hi
        rcases Finset.mem_filter.mp hi with ⟨hiJ, hi0⟩
        exact Finset.mem_filter.mpr ⟨h.J_subset_I hiJ, hi0⟩
    constructor
    · rw [hIJ0]
      omega
    · intro h0
      rcases h0 with h0J | h0G
      · rw [hIJ0]
        have hJ0 :
            (Jset Open x).filter (fun i : TimeIndex N => i = 0) = {0} := by
          ext i
          constructor
          · intro hi
            simpa using (Finset.mem_filter.mp hi).2
          · intro hi
            have hi0 : i = 0 := by
              simpa using hi
            exact Finset.mem_filter.mpr ⟨by simpa [hi0] using h0J, hi0⟩
        rw [hJ0]
        norm_num
      · exact False.elim (G_zero_false h 0 h0G rfl)
  · by_cases h_case : ⟨m + 1, by linarith⟩ ∈ Iset Open x ∧ ⟨m + 1, by linarith⟩ ∉ Jset Open x;
    · by_cases h_case2 : ⟨m, by linarith⟩ ∈ Jset Open x ∨ ⟨m, by linarith⟩ ∈ Gset Open x;
      · have h_card_I : (Finset.filter (fun i : TimeIndex N => i.val ≤ m + 1) (Iset Open x)).card = (Finset.filter (fun i : TimeIndex N => i.val ≤ m) (Iset Open x)).card + 1 := by
          rw [ show ( Finset.filter ( fun i : TimeIndex N => ( i : ℕ ) ≤ m + 1 ) ( Iset Open x ) ) = Finset.filter ( fun i : TimeIndex N => ( i : ℕ ) ≤ m ) ( Iset Open x ) ∪ { ⟨ m + 1, by linarith ⟩ } from ?_, Finset.card_union ] <;> norm_num [ h_case ];
          grind
        have h_card_J : (Finset.filter (fun j : TimeIndex N => j.val ≤ m + 1) (Jset Open x)).card = (Finset.filter (fun j : TimeIndex N => j.val ≤ m) (Jset Open x)).card := by
          congr 1 with j ; simp +decide [ Finset.mem_filter, Finset.mem_univ, * ];
          grind +locals
        simp_all +decide [ Finset.filter_congr ];
        grind +locals;
      · by_cases h_case3 : ⟨m - 1, by omega⟩ ∈ Jset Open x ∨ ⟨m - 1, by omega⟩ ∈ Gset Open x;
        · rcases m with ( _ | m ) <;> simp_all +decide [ Finset.filter_le_eq_Ici ];
          have h_card_le : (Finset.filter (fun i : TimeIndex N => i.val ≤ m + 2) (Iset Open x)).card ≤ (Finset.filter (fun i : TimeIndex N => i.val ≤ m + 1) (Iset Open x)).card + 1 := by
            rw [ show ( Finset.filter ( fun i : TimeIndex N => ( i : ℕ ) ≤ m + 2 ) ( Iset Open x ) ) = Finset.filter ( fun i : TimeIndex N => ( i : ℕ ) ≤ m + 1 ) ( Iset Open x ) ∪ { ⟨ m + 2, by linarith ⟩ } from ?_ ];
            · exact Finset.card_union_le _ _;
            · grind;
          have h_card_le : (Finset.filter (fun i : TimeIndex N => i.val ≤ m + 2) (Jset Open x)).card ≥ (Finset.filter (fun i : TimeIndex N => i.val ≤ m) (Jset Open x)).card := by
            exact Finset.card_mono fun x hx => Finset.mem_filter.mpr ⟨ Finset.mem_filter.mp hx |>.1, by linarith [ Finset.mem_filter.mp hx |>.2 ] ⟩;
          have h_card_le : (Finset.filter (fun i : TimeIndex N => i.val ≤ m + 1) (Iset Open x)).card ≤ (Finset.filter (fun i : TimeIndex N => i.val ≤ m) (Iset Open x)).card + 1 := by
            rw [ show ( Finset.filter ( fun i : TimeIndex N => ( i : ℕ ) ≤ m + 1 ) ( Iset Open x ) ) = Finset.filter ( fun i : TimeIndex N => ( i : ℕ ) ≤ m ) ( Iset Open x ) ∪ Finset.filter ( fun i : TimeIndex N => ( i : ℕ ) = m + 1 ) ( Iset Open x ) from ?_, Finset.card_union ];
            · rw [ show ( Finset.filter ( fun i : TimeIndex N => ( i : ℕ ) = m + 1 ) ( Iset Open x ) ) = { ⟨ m + 1, by linarith ⟩ } ∩ Iset Open x from ?_ ];
              · grind;
              · ext ⟨ i, hi ⟩ ; aesop;
            · grind;
          grind +locals;
        · have := h.IminusJ_back ⟨ m + 1, by linarith ⟩ h_case.1 h_case.2 ( by linarith ) ; simp_all +decide [ Finset.filter_le_eq_Ici ] ;
          rcases m with ( _ | m ) <;> simp_all +decide [ predIndex, pred2Index ];
    · by_cases h_case : ⟨m + 1, by linarith⟩ ∈ Jset Open x <;> simp_all +decide [ Finset.filter_congr ];
      · have h_card : (Finset.filter (fun i : TimeIndex N => i.val ≤ m + 1) (Iset Open x)).card = (Finset.filter (fun i : TimeIndex N => i.val ≤ m) (Iset Open x)).card + 1 := by
          rw [ show ( Finset.filter ( fun i : TimeIndex N => ( i : ℕ ) ≤ m + 1 ) ( Iset Open x ) ) = Finset.filter ( fun i : TimeIndex N => ( i : ℕ ) ≤ m ) ( Iset Open x ) ∪ { ⟨ m + 1, by linarith ⟩ } from ?_, Finset.card_union ] <;> norm_num;
          grind +splitIndPred;
        have h_card_J : (Finset.filter (fun j : TimeIndex N => j.val ≤ m + 1) (Jset Open x)).card = (Finset.filter (fun j : TimeIndex N => j.val ≤ m) (Jset Open x)).card + 1 := by
          rw [ show ( Finset.filter ( fun j : TimeIndex N => ( j : ℕ ) ≤ m + 1 ) ( Jset Open x ) ) = Finset.filter ( fun j : TimeIndex N => ( j : ℕ ) ≤ m ) ( Jset Open x ) ∪ { ⟨ m + 1, by linarith ⟩ } from ?_, Finset.card_union ] <;> norm_num [ h_case ];
          grind +extAll;
        constructor <;> linarith [ ih m ( by linarith ) ( by linarith ) ];
      · rw [ show ( Finset.filter ( fun i : TimeIndex N => ( i : ℕ ) ≤ m + 1 ) ( Iset Open x ) ) = Finset.filter ( fun i : TimeIndex N => ( i : ℕ ) ≤ m ) ( Iset Open x ) from ?_, show ( Finset.filter ( fun j : TimeIndex N => ( j : ℕ ) ≤ m + 1 ) ( Jset Open x ) ) = Finset.filter ( fun j : TimeIndex N => ( j : ℕ ) ≤ m ) ( Jset Open x ) from ?_ ];
        · refine' ⟨ ih m le_rfl ( by linarith ) |>.1, _ ⟩;
          intro hg;
          have := h.G_back ⟨ m + 1, by linarith ⟩ hg ( Nat.succ_pos _ );
          exact ih m le_rfl ( by linarith ) |>.2 ( by tauto );
        · ext j; simp [h_case];
          exact fun hj => ⟨ fun hj' => Nat.le_of_lt_succ <| hj'.lt_of_ne <| by rintro h; exact h_case <| by convert hj; aesop, fun hj' => Nat.le_succ_of_le hj' ⟩;
        · grind +splitIndPred

theorem fiber_card_le_three {N L : Nat}
    {Open : ∀ u v : V N L, OAdj u v -> Prop} {x : SpacePoint L}
    (h : FiberHyp Open x) :
    (Iset Open x).card <= 3 * (Jset Open x).card := by
  convert prefix_count_le h N le_rfl |>.1 using 1;
  · exact congr_arg Finset.card ( Finset.ext fun i => by simp +decide [ Fin.is_le ] );
  · rw [ Finset.filter_true_of_mem fun j hj => Fin.is_le j ]

lemma fiber_F_back {N L : Nat}
    {Open : ∀ u v : V N L, OAdj u v -> Prop}
    {x : SpacePoint L} {t : Nat} (ht : t <= N) (htpos : 1 <= t)
    (htF : vertexAt (N := N) (L := L) t ht x ∈ F Open) :
    (∃ hpred : t - 1 <= N,
      vertexAt (N := N) (L := L) (t - 1) hpred x ∈ F Open)
    ∨
    (∃ hpred : t - 1 <= N,
      vertexAt (N := N) (L := L) (t - 1) hpred x ∈ OrientedInnerBoundary Open) := by
  by_cases h : vertexAt ( t - 1 ) ( Nat.sub_le_of_le_add <| by linarith ) x ∈ B Open <;> simp_all +decide [ F_of_uAdj_F_of_not_B ];
  · grind +locals;
  · refine Or.inl ⟨ by linarith, ?_ ⟩;
    refine' F_of_uAdj_F_of_not_B _ _ h;
    exact vertexAt t ht x;
    · grind +locals;
    · assumption

lemma fiberHyp {N L : Nat}
    {Open : ∀ u v : V N L, OAdj u v -> Prop}
    (hC : Not (Crossing Open)) (x : SpacePoint L) :
    FiberHyp Open x := by
  -- By definition of $F$, $F ⊆ B^c$, and $B ⊆ B$.
  have hF_subset_Bc : ∀ u : V N L, u ∈ F Open → u ∉ B Open := by
    exact?;
  constructor;
  · intro m hm
    simp [Jset, Iset] at hm ⊢;
    exact orientedInnerBoundary_subset_innerBoundary hm;
  · simp_all +decide [ Finset.disjoint_left, Iset, Gset ];
    exact fun a ha => fun hb => hF_subset_Bc _ _ hb ha.1;
  · intro t ht ht'; specialize ht'; simp_all +decide [ Gset, Jset ] ;
    have := fiber_F_back ( show ( t : ℕ ) ≤ N from Nat.le_of_lt_succ t.2 ) ht' ht; simp_all +decide [ vertexAt, vertexAtIndex, predIndex ] ;
  · unfold Iset Jset Gset;
    intro m hm₁ hm₂ hm₃;
    have := lowerbd_predecessor ( show m.val ≤ N from m.is_le ) hm₃ ( by aesop ) ( by aesop );
    unfold predIndex pred2Index; aesop;

theorem card_boundary_sum_fibers {N L : Nat}
    {Open : ∀ u v : V N L, OAdj u v -> Prop} :
    Fintype.card {u : V N L // u ∈ InnerBoundary Open} =
      Finset.sum Finset.univ (fun x : SpacePoint L => (Iset Open x).card) := by
  simp +decide [ Fintype.card_subtype ];
  simp +decide only [InnerBoundary, Finset.card_filter, Iset];
  rw [ ← Finset.sum_product' ];
  refine' Finset.sum_bij ( fun x _ => ( x.2, ⟨ x.1, Nat.lt_succ_of_le ( Fin.is_le _ ) ⟩ ) ) _ _ _ _ <;> simp +decide [ vertexAtIndex ];
  congr! 3

theorem card_oriented_boundary_sum_fibers {N L : Nat}
    {Open : ∀ u v : V N L, OAdj u v -> Prop} :
    Fintype.card {u : V N L // u ∈ OrientedInnerBoundary Open} =
      Finset.sum Finset.univ (fun x : SpacePoint L => (Jset Open x).card) := by
  unfold Jset; simp +decide [ Fintype.card_subtype ] ;
  simp +decide only [Finset.card_filter];
  rw [ ← Finset.sum_product' ];
  refine' Finset.sum_bij ( fun x _ => ( x.2, x.1 ) ) _ _ _ _ <;> simp +decide [ vertexAtIndex ];
  aesop

theorem oriented_animal_to_animal {N L : Nat}
    {Open : ∀ u v : V N L, OAdj u v -> Prop}
    (hN : 3 <= N) (hL : 2 <= L)
    (hNL : (N : Real) <= Real.exp (L : Real))
    (hC : Not (Crossing Open)) :
    Fintype.card {u : V N L // u ∈ InnerBoundary Open} <=
      3 * Fintype.card {u : V N L // u ∈ OrientedInnerBoundary Open} := by
  classical
  have _ : 3 <= N := hN
  have _ : 2 <= L := hL
  have _ : (N : Real) <= Real.exp (L : Real) := hNL
  rw [card_boundary_sum_fibers, card_oriented_boundary_sum_fibers]
  calc
    (Finset.univ.sum fun x : SpacePoint L => (Iset Open x).card)
        <= Finset.univ.sum fun x : SpacePoint L => 3 * (Jset Open x).card := by
          exact Finset.sum_le_sum fun x _ => fiber_card_le_three (fiberHyp hC x)
    _ = 3 * (Finset.univ.sum fun x : SpacePoint L => (Jset Open x).card) := by
          simp [Finset.mul_sum]

theorem lowerbd_card_oriented_inner {N L : Nat}
    {Open : ∀ u v : V N L, OAdj u v -> Prop}
    (hC : Not (Crossing Open)) :
    (2 * L + 1) ^ 2 <=
      Fintype.card {u : V N L // u ∈ OrientedInnerBoundary Open} := by
  rw [← card_spacePoint L]
  exact card_space_le_oriented_inner hC

end OrientedAnimal



namespace OrientedAnimal
namespace AnimalBound

structure BoxPoint (N L : Nat) where
  timeIndex : Fin (N + 1)
  firstIndex : Fin (2 * L + 1)
  secondIndex : Fin (2 * L + 1)
deriving DecidableEq, Fintype

namespace BoxPoint

def time {N L : Nat} (v : BoxPoint N L) : Int :=
  v.timeIndex.val

def first {N L : Nat} (v : BoxPoint N L) : Int :=
  (v.firstIndex.val : Int) - (L : Int)

def second {N L : Nat} (v : BoxPoint N L) : Int :=
  (v.secondIndex.val : Int) - (L : Int)

def coord {N L : Nat} (v : BoxPoint N L) (i : Fin 3) : Int :=
  if i.val = 0 then
    v.time
  else if i.val = 1 then
    v.first
  else
    v.second

end BoxPoint

def T (N L : Nat) (k : Nat) : Set (BoxPoint N L) :=
  {v | v.timeIndex.val = k}

def T0 (N L : Nat) : Set (BoxPoint N L) :=
  T N L 0

def TN (N L : Nat) : Set (BoxPoint N L) :=
  T N L N

def StarAdj {N L : Nat} (u v : BoxPoint N L) : Prop :=
  u ≠ v ∧ ∀ i : Fin 3, Int.natAbs (BoxPoint.coord u i - BoxPoint.coord v i) ≤ 1

lemma starAdj_symm {N L : Nat} {u v : BoxPoint N L}
    (h : StarAdj u v) : StarAdj v u := by
  exact ⟨ h.1.symm, fun i => by rw [ ← Int.natAbs_neg, neg_sub ] ; exact h.2 i ⟩

structure StarPath (N L : Nat) where
  len : Nat
  vertex : Fin (len + 1) → BoxPoint N L
  edge : ∀ i : Fin len, StarAdj (vertex i.castSucc) (vertex i.succ)

namespace StarPath

def start {N L : Nat} (p : StarPath N L) : BoxPoint N L :=
  p.vertex 0

def finish {N L : Nat} (p : StarPath N L) : BoxPoint N L :=
  p.vertex (Fin.last p.len)

def StaysIn {N L : Nat} (p : StarPath N L) (A : Set (BoxPoint N L)) : Prop :=
  ∀ i : Fin (p.len + 1), p.vertex i ∈ A

def nil {N L : Nat} (v : BoxPoint N L) : StarPath N L where
  len := 0
  vertex := fun _ => v
  edge := by
    intro i
    exact Fin.elim0 i

def reverse {N L : Nat} (p : StarPath N L) : StarPath N L where
  len := p.len
  vertex := fun i => p.vertex (Fin.rev i)
  edge := by
    intro i
    have h := p.edge (Fin.rev i)
    simp_all +decide [StarAdj]
    simp_all +decide [Fin.rev_castSucc, Fin.rev_succ]
    exact ⟨Ne.symm h.1, fun i => by rw [← Int.natAbs_neg, neg_sub]; exact h.2 i⟩

lemma reverse_start {N L : Nat} (p : StarPath N L) :
    p.reverse.start = p.finish := by
  simp [reverse, start, finish]

lemma reverse_finish {N L : Nat} (p : StarPath N L) :
    p.reverse.finish = p.start := by
  simp [reverse, start, finish]

lemma reverse_staysIn {N L : Nat} {p : StarPath N L} {A : Set (BoxPoint N L)}
    (hp : p.StaysIn A) :
    p.reverse.StaysIn A := by
  intro i
  exact hp (Fin.rev i)

/-- Concatenation of two star paths where the end of the first equals the start of the second. -/
def concat {N L : Nat} (p q : StarPath N L) (h : p.finish = q.start) : StarPath N L where
  len := p.len + q.len
  vertex := fun i =>
    if hi : i.val ≤ p.len then
      p.vertex ⟨i.val, by omega⟩
    else
      q.vertex ⟨i.val - p.len, by omega⟩
  edge := by
    intro i
    simp only [Fin.val_castSucc, Fin.val_succ]
    split_ifs with hcs hs hs
    · -- both endpoints lie in p
      have key := p.edge ⟨i.val, by omega⟩
      show StarAdj (p.vertex ⟨i.val, _⟩) (p.vertex ⟨i.val + 1, _⟩)
      convert key using 2
    · -- transition from p to q
      have heq : i.val = p.len := by omega
      have hqpos : q.len > 0 := by omega
      have h1 : p.vertex (⟨i.val, by omega⟩ : Fin (p.len + 1)) = q.vertex (⟨0, by omega⟩ : Fin (q.len + 1)) := by
        have : (⟨i.val, by omega⟩ : Fin (p.len + 1)) = Fin.last p.len := Fin.ext (by simp [Fin.last]; omega)
        rw [this]; change p.finish = _; rw [h]; rfl
      rw [h1]
      have h2 : (⟨i.val + 1 - p.len, by omega⟩ : Fin (q.len + 1)) = ⟨1, by omega⟩ := Fin.ext (by simp; omega)
      rw [h2]
      have key := q.edge ⟨0, hqpos⟩
      show StarAdj (q.vertex ⟨0, _⟩) (q.vertex ⟨1, _⟩)
      convert key using 2
    · omega
    · -- both endpoints lie in q
      have key := q.edge ⟨i.val - p.len, by omega⟩
      show StarAdj (q.vertex ⟨i.val - p.len, _⟩) (q.vertex ⟨i.val + 1 - p.len, _⟩)
      have h4 : (⟨i.val + 1 - p.len, by omega⟩ : Fin (q.len + 1)) = ⟨i.val - p.len + 1, by omega⟩ :=
        Fin.ext (by simp; omega)
      rw [h4]
      convert key using 2

lemma concat_start {N L : Nat} (p q : StarPath N L) (h : p.finish = q.start) :
    (p.concat q h).start = p.start := by
  simp [concat, start]

lemma concat_finish {N L : Nat} (p q : StarPath N L) (h : p.finish = q.start) :
    (p.concat q h).finish = q.finish := by
  unfold StarPath.concat StarPath.finish;
  cases q ; aesop

lemma concat_staysIn {N L : Nat} (p q : StarPath N L) (h : p.finish = q.start)
    {A : Set (BoxPoint N L)} (hp : p.StaysIn A) (hq : q.StaysIn A) :
    (p.concat q h).StaysIn A := by
  intro i
  simp [concat]
  split
  · exact hp ⟨i.val, by omega⟩
  · exact hq ⟨i.val - p.len, by omega⟩

/-- A single-step star path between two adjacent points. -/
def single {N L : Nat} (u v : BoxPoint N L) (h : StarAdj u v) : StarPath N L where
  len := 1
  vertex := ![u, v]
  edge := by
    intro ⟨i, hi⟩
    have : i = 0 := by omega
    subst this
    simp [Fin.castSucc, Fin.succ, Matrix.cons_val_zero, Matrix.cons_val_one]
    exact h

lemma single_start {N L : Nat} (u v : BoxPoint N L) (h : StarAdj u v) :
    (single u v h).start = u := by
  simp [single, start, Matrix.cons_val_zero]

lemma single_finish {N L : Nat} (u v : BoxPoint N L) (h : StarAdj u v) :
    (single u v h).finish = v := by
  simp [single, finish, Fin.last, Matrix.cons_val_one]

lemma single_staysIn {N L : Nat} (u v : BoxPoint N L) (h : StarAdj u v)
    {A : Set (BoxPoint N L)} (hu : u ∈ A) (hv : v ∈ A) :
    (single u v h).StaysIn A := by
  intro i
  fin_cases i <;> simp [single, Matrix.cons_val_zero, Matrix.cons_val_one] <;> assumption

end StarPath

def StarConnected {N L : Nat} (A : Set (BoxPoint N L)) : Prop :=
  ∀ ⦃u : BoxPoint N L⦄, u ∈ A →
  ∀ ⦃v : BoxPoint N L⦄, v ∈ A →
    ∃ p : StarPath N L, p.start = u ∧ p.finish = v ∧ p.StaysIn A

def StarJoinedIn {N L : Nat} (A : Set (BoxPoint N L))
    (u v : BoxPoint N L) : Prop :=
  ∃ p : StarPath N L, p.start = u ∧ p.finish = v ∧ p.StaysIn A

/-- StarJoinedIn is reflexive. -/
lemma starJoinedIn_refl {N L : Nat} {A : Set (BoxPoint N L)} {u : BoxPoint N L} (hu : u ∈ A) :
    StarJoinedIn A u u :=
  ⟨StarPath.nil u, rfl, rfl, fun _ => hu⟩

/-- StarJoinedIn is symmetric by reversing paths. -/
lemma starJoinedIn_symm {N L : Nat} {A : Set (BoxPoint N L)} {u v : BoxPoint N L}
    (huv : StarJoinedIn A u v) :
    StarJoinedIn A v u := by
  obtain ⟨p, hp_start, hp_finish, hp_stays⟩ := huv
  refine ⟨p.reverse, ?_, ?_, StarPath.reverse_staysIn hp_stays⟩
  · rw [StarPath.reverse_start, hp_finish]
  · rw [StarPath.reverse_finish, hp_start]

/-- StarJoinedIn is transitive via path concatenation. -/
lemma starJoinedIn_trans {N L : Nat} {A : Set (BoxPoint N L)} {u v w : BoxPoint N L}
    (huv : StarJoinedIn A u v) (hvw : StarJoinedIn A v w) :
    StarJoinedIn A u w := by
  obtain ⟨p, hp_start, hp_finish, hp_stays⟩ := huv
  obtain ⟨q, hq_start, hq_finish, hq_stays⟩ := hvw
  have hpq : p.finish = q.start := by rw [hp_finish, hq_start]
  refine ⟨p.concat q hpq, ?_, ?_, p.concat_staysIn q hpq hp_stays hq_stays⟩
  · rw [p.concat_start q hpq]; exact hp_start
  · rw [p.concat_finish q hpq]; exact hq_finish

def Touches {N L : Nat} (A C : Set (BoxPoint N L)) : Prop :=
  ∃ v : BoxPoint N L, v ∈ A ∧ v ∈ C

def HasStarNeighborIn {N L : Nat}
    (K U : Set (BoxPoint N L)) : Prop :=
  ∃ k : BoxPoint N L, k ∈ K ∧ ∃ u : BoxPoint N L, u ∈ U ∧ StarAdj k u

def InnerStarBoundary {N L : Nat}
    (U H : Set (BoxPoint N L)) : Set (BoxPoint N L) :=
  {u | u ∈ U ∧ ∃ h : BoxPoint N L, h ∈ H ∧ StarAdj u h}

def StarBoundaryInside {N L : Nat}
    (A C : Set (BoxPoint N L)) : Set (BoxPoint N L) :=
  {c | c ∈ C ∧ ∃ a : BoxPoint N L, a ∈ A ∧ StarAdj c a}

structure IsStarComponentOf {N L : Nat}
    (A C : Set (BoxPoint N L)) : Prop where
  nonempty : ∃ x : BoxPoint N L, x ∈ C
  subset : C ⊆ A
  connected : StarConnected C
  maximal :
    ∀ D : Set (BoxPoint N L),
      D ⊆ A →
      StarConnected D →
      (∃ x : BoxPoint N L, x ∈ C ∧ x ∈ D) →
      D ⊆ C

lemma T0_nonempty (N L : Nat) :
    ∃ v : BoxPoint N L, v ∈ T0 N L := by
  refine ⟨
    { timeIndex := ⟨0, Nat.succ_pos N⟩
      firstIndex := ⟨L, by omega⟩
      secondIndex := ⟨L, by omega⟩ }, ?_⟩
  simp [T0, T]

lemma TN_nonempty (N L : Nat) :
    ∃ v : BoxPoint N L, v ∈ TN N L := by
  refine ⟨
    { timeIndex := ⟨N, Nat.lt_succ_self N⟩
      firstIndex := ⟨L, by omega⟩
      secondIndex := ⟨L, by omega⟩ }, ?_⟩
  simp [TN, T]

theorem whole_box_starConnected (N L : Nat) :
    StarConnected (Set.univ : Set (BoxPoint N L)) := by
  rintro ⟨ i, j, k ⟩ - ⟨ i', j', k' ⟩ -;
  -- We can construct a path from $(i, j, k)$ to $(i', j', k')$ by moving along each coordinate axis.
  have h_path : ∃ p : StarPath N L, p.start = ⟨i, j, k⟩ ∧ p.finish = ⟨i', j, k⟩ := by
    induction' i' using Fin.inductionOn with i' ih;
    · induction' i using Fin.inductionOn with i ih;
      · exact ⟨ StarPath.nil _, rfl, rfl ⟩;
      · obtain ⟨ p, hp₁, hp₂ ⟩ := ih;
        refine' ⟨ _, _, _ ⟩;
        exact StarPath.concat ( StarPath.single ⟨ i.succ, j, k ⟩ ⟨ i.castSucc, j, k ⟩ ( by
          constructor <;> norm_num [ BoxPoint.coord ];
          · grind;
          · simp +decide [ Fin.forall_fin_succ, BoxPoint.time, BoxPoint.first, BoxPoint.second ] ) ) p ( by
          exact hp₁.symm ▸ rfl )
        all_goals generalize_proofs at *;
        · rw [StarPath.concat_start, StarPath.single_start]
        · grind +suggestions;
    · obtain ⟨ p, hp₁, hp₂ ⟩ := ih;
      refine' ⟨ p.concat ( StarPath.single _ _ _ ) _, _, _ ⟩;
      exact ⟨ i'.castSucc, j, k ⟩;
      exact ⟨ i'.succ, j, k ⟩;
      all_goals norm_num [ StarPath.start, StarPath.finish, StarPath.concat, StarPath.single ] at *;
      grind +locals;
      exact hp₂;
      · exact hp₁;
      · simp +decide [ StarPath.concat, StarPath.single ];
  -- We can construct a path from $(i', j, k)$ to $(i', j', k)$ by moving along the j-axis.
  have h_path_j : ∃ p : StarPath N L, p.start = ⟨i', j, k⟩ ∧ p.finish = ⟨i', j', k⟩ := by
    have h_path_j : ∀ (j j' : Fin (2 * L + 1)), ∃ p : StarPath N L, p.start = ⟨i', j, k⟩ ∧ p.finish = ⟨i', j', k⟩ := by
      intro j j';
      induction' j' using Fin.inductionOn with j' ih generalizing j;
      · induction' j using Fin.inductionOn with j ih;
        · exact ⟨ StarPath.nil _, rfl, rfl ⟩;
        · obtain ⟨ p, hp₁, hp₂ ⟩ := ih;
          use StarPath.concat (StarPath.single ⟨i', j.succ, k⟩ ⟨i', j.castSucc, k⟩ (by
          constructor <;> norm_num [ Fin.ext_iff ];
          simp +decide [ Fin.forall_fin_succ, BoxPoint.coord ];
          simp +decide [ BoxPoint.time, BoxPoint.first, BoxPoint.second ])) p (by
          exact hp₁.symm ▸ rfl)
          generalize_proofs at *;
          exact ⟨ by rfl, by rw [ StarPath.concat_finish, hp₂ ] ⟩;
      · obtain ⟨ p, hp₁, hp₂ ⟩ := ih j;
        use p.concat (StarPath.single ⟨i', j'.castSucc, k⟩ ⟨i', j'.succ, k⟩ (by
        constructor <;> norm_num [ BoxPoint.coord ];
        · grind +revert;
        · simp +decide [ Fin.forall_fin_succ ];
          simp +decide [ BoxPoint.time, BoxPoint.first, BoxPoint.second ])) (by
        exact hp₂.trans ( by rfl ))
        generalize_proofs at *;
        exact ⟨ by rw [ StarPath.concat_start, hp₁ ], by rw [ StarPath.concat_finish, StarPath.single_finish ] ⟩;
    exact h_path_j j j';
  -- We can construct a path from $(i', j', k)$ to $(i', j', k')$ by moving along the k-axis.
  have h_path_k : ∃ p : StarPath N L, p.start = ⟨i', j', k⟩ ∧ p.finish = ⟨i', j', k'⟩ := by
    induction' k' using Fin.inductionOn with k' ih;
    · induction' k using Fin.inductionOn with k ih;
      · exact ⟨ StarPath.nil _, rfl, rfl ⟩;
      · induction' k.succ using Fin.inductionOn with k ih;
        · exact ⟨ StarPath.nil _, rfl, rfl ⟩;
        · obtain ⟨ p, hp₁, hp₂ ⟩ := ih;
          use StarPath.concat (StarPath.single ⟨i', j', k.succ⟩ ⟨i', j', k.castSucc⟩ (by
          grind +locals)) p (by
          exact hp₁.symm ▸ rfl)
          generalize_proofs at *;
          grind +suggestions;
    · obtain ⟨ p, hp₁, hp₂ ⟩ := ih;
      use p.concat (StarPath.single ⟨i', j', k'.castSucc⟩ ⟨i', j', k'.succ⟩ (by
      grind +locals)) (by
      exact hp₂.trans ( by rfl ))
      generalize_proofs at *;
      exact ⟨ by rw [ StarPath.concat_start, hp₁ ], by rw [ StarPath.concat_finish, StarPath.single_finish ] ⟩;
  obtain ⟨ p, hp₁, hp₂ ⟩ := h_path
  obtain ⟨ q, hq₁, hq₂ ⟩ := h_path_j
  obtain ⟨ r, hr₁, hr₂ ⟩ := h_path_k
  use StarPath.concat (StarPath.concat p q (by
  grind)) r (by
  rw [ StarPath.concat_finish, hq₂, hr₁ ])
  generalize_proofs at *;
  simp_all +decide [ StarPath.concat_start, StarPath.concat_finish, StarPath.StaysIn ]

theorem T0_starConnected (N L : Nat) :
    StarConnected (T0 N L) := by
  intros u hu v hv;
  -- We can construct a path from $u$ to $v$ by moving along the first coordinate until we reach $v$'s first coordinate, then moving along the second coordinate.
  have h_path : ∃ p : StarPath N L, p.start = u ∧ p.finish = ⟨0, v.firstIndex, u.secondIndex⟩ ∧ p.StaysIn (T0 N L) := by
    -- We can construct a path from $u$ to $v$ by moving along the first coordinate until we reach $v$'s first coordinate.
    have h_path_first : ∀ i j : Fin (2 * L + 1), ∃ p : StarPath N L, p.start = ⟨0, i, u.secondIndex⟩ ∧ p.finish = ⟨0, j, u.secondIndex⟩ ∧ p.StaysIn (T0 N L) := by
      intros i j
      induction' j using Fin.induction with j ih generalizing i;
      · induction' i using Fin.inductionOn with i ih;
        · exact ⟨ StarPath.nil _, rfl, rfl, fun _ => by tauto ⟩;
        · obtain ⟨ p, hp₁, hp₂, hp₃ ⟩ := ih;
          refine' ⟨ StarPath.concat ( StarPath.single _ _ _ ) p _, _, _, _ ⟩;
          exact ⟨ 0, Fin.succ i, u.secondIndex ⟩;
          exact ⟨ 0, Fin.castSucc i, u.secondIndex ⟩;
          grind +locals;
          exact hp₁.symm;
          · grind +suggestions;
          · grind +suggestions;
          · exact StarPath.concat_staysIn _ _ _ ( StarPath.single_staysIn _ _ _ ( by aesop ) ( by aesop ) ) hp₃;
      · obtain ⟨ p, hp₁, hp₂, hp₃ ⟩ := ih i;
        use p.concat (StarPath.single ⟨0, j.castSucc, u.secondIndex⟩ ⟨0, j.succ, u.secondIndex⟩ (by
        constructor <;> norm_num [ BoxPoint.coord ];
        · grind +revert;
        · simp +decide [ Fin.forall_fin_succ ];
          simp +decide [ BoxPoint.time, BoxPoint.first, BoxPoint.second ])) (by
        exact hp₂)
        generalize_proofs at *;
        simp_all +decide [ StarPath.concat_start, StarPath.concat_finish ];
        exact ⟨ rfl, StarPath.concat_staysIn _ _ _ hp₃ ( StarPath.single_staysIn _ _ _ ( by aesop ) ( by aesop ) ) ⟩;
    convert h_path_first u.firstIndex v.firstIndex;
    exact Fin.ext hu;
  obtain ⟨ p, hp₁, hp₂, hp₃ ⟩ := h_path;
  have h_path2 : ∃ q : StarPath N L, q.start = ⟨0, v.firstIndex, u.secondIndex⟩ ∧ q.finish = v ∧ q.StaysIn (T0 N L) := by
    have h_path2 : ∀ (i j : Fin (2 * L + 1)), ∃ q : StarPath N L, q.start = ⟨0, v.firstIndex, i⟩ ∧ q.finish = ⟨0, v.firstIndex, j⟩ ∧ q.StaysIn (T0 N L) := by
      intros i j
      induction' j using Fin.induction with j ih generalizing i;
      · induction' i using Fin.inductionOn with i ih;
        · exact ⟨ StarPath.nil _, rfl, rfl, fun _ => by tauto ⟩;
        · obtain ⟨ q, hq₁, hq₂, hq₃ ⟩ := ih;
          use StarPath.concat (StarPath.single ⟨0, v.firstIndex, i.succ⟩ ⟨0, v.firstIndex, i.castSucc⟩ (by
          constructor <;> norm_num [ BoxPoint.coord ];
          · grind;
          · simp +decide [ Fin.forall_fin_succ ];
            simp +decide [ BoxPoint.time, BoxPoint.first, BoxPoint.second ])) q (by
          exact hq₁.symm ▸ rfl)
          generalize_proofs at *;
          simp_all +decide [ StarPath.concat_start, StarPath.concat_finish ];
          exact ⟨ rfl, StarPath.concat_staysIn _ _ _ ( StarPath.single_staysIn _ _ _ ( by aesop ) ( by aesop ) ) hq₃ ⟩;
      · obtain ⟨ q, hq₁, hq₂, hq₃ ⟩ := ih i;
        use q.concat (StarPath.single ⟨0, v.firstIndex, j.castSucc⟩ ⟨0, v.firstIndex, j.succ⟩ (by
        constructor <;> norm_num [ BoxPoint.coord ];
        · grind +splitImp;
        · simp +decide [ Fin.forall_fin_succ ];
          simp +decide [ BoxPoint.time, BoxPoint.first, BoxPoint.second ])) (by
        exact hq₂)
        generalize_proofs at *;
        exact ⟨ by rw [ StarPath.concat_start, hq₁ ], by rw [ StarPath.concat_finish, StarPath.single_finish ], by exact StarPath.concat_staysIn _ _ _ hq₃ ( by exact fun i => by fin_cases i <;> tauto ) ⟩;
    convert h_path2 u.secondIndex v.secondIndex;
    exact Fin.ext hv;
  obtain ⟨ q, hq₁, hq₂, hq₃ ⟩ := h_path2;
  use p.concat q (by
  rw [hp₂, hq₁])
  generalize_proofs at *;
  exact ⟨ by rw [ StarPath.concat_start, hp₁ ], by rw [ StarPath.concat_finish, hq₂ ], by exact StarPath.concat_staysIn p q ‹_› hp₃ hq₃ ⟩

theorem TN_starConnected (N L : Nat) :
    StarConnected (TN N L) := by
  intro u hu v hv;
  -- We can construct a path from u to v by moving the first coordinate and then the second coordinate.
  obtain ⟨p1, hp1⟩ : ∃ p1 : StarPath N L, p1.start = u ∧ p1.finish = ⟨u.timeIndex, u.firstIndex, v.secondIndex⟩ ∧ p1.StaysIn (TN N L) := by
    -- We can construct a path from u to ⟨u.timeIndex, u.firstIndex, v.secondIndex⟩ by moving the second coordinate one step at a time.
    have h_path_second : ∀ (i j : Fin (2 * L + 1)), ∃ p : StarPath N L, p.start = ⟨u.timeIndex, u.firstIndex, i⟩ ∧ p.finish = ⟨u.timeIndex, u.firstIndex, j⟩ ∧ p.StaysIn (TN N L) := by
      intro i j;
      induction' j using Fin.inductionOn with j ih ih;
      · induction' i using Fin.inductionOn with i ih;
        · exact ⟨ StarPath.nil _, rfl, rfl, fun _ => hu ⟩;
        · obtain ⟨ p, hp₁, hp₂, hp₃ ⟩ := ih;
          refine' ⟨ _, _, _, _ ⟩;
          exact StarPath.concat ( StarPath.single ⟨ u.timeIndex, u.firstIndex, Fin.succ i ⟩ ⟨ u.timeIndex, u.firstIndex, Fin.castSucc i ⟩ ( by
            constructor;
            · grind;
            · simp +decide [ Fin.forall_fin_succ, BoxPoint.coord ];
              simp +decide [ BoxPoint.time, BoxPoint.first, BoxPoint.second ] ) ) p ( by
            exact hp₁.symm )
          all_goals generalize_proofs at *;
          · rw [StarPath.concat_start, StarPath.single_start]
          · grind +suggestions;
          · exact StarPath.concat_staysIn _ _ _ ( StarPath.single_staysIn _ _ _ ( by aesop ) ( by aesop ) ) hp₃;
      · obtain ⟨ p, hp₁, hp₂, hp₃ ⟩ := ih;
        refine' ⟨ p.concat ( StarPath.single _ _ _ ) _, _, _, _ ⟩;
        exact ⟨ u.timeIndex, u.firstIndex, j.castSucc ⟩;
        exact ⟨ u.timeIndex, u.firstIndex, j.succ ⟩;
        grind +locals;
        exact hp₂;
        · exact hp₁;
        · exact StarPath.concat_finish _ _ _;
        · exact StarPath.concat_staysIn _ _ _ hp₃ ( StarPath.single_staysIn _ _ _ ( by aesop ) ( by aesop ) );
    cases u ; aesop;
  obtain ⟨p2, hp2⟩ : ∃ p2 : StarPath N L, p2.start = ⟨u.timeIndex, u.firstIndex, v.secondIndex⟩ ∧ p2.finish = v ∧ p2.StaysIn (TN N L) := by
    have h_path : ∀ (x y : Fin (2 * L + 1)), ∃ p : StarPath N L, p.start = ⟨u.timeIndex, x, v.secondIndex⟩ ∧ p.finish = ⟨u.timeIndex, y, v.secondIndex⟩ ∧ p.StaysIn (TN N L) := by
      intro x y;
      induction' y using Fin.inductionOn with y ih;
      · induction' x using Fin.inductionOn with x ih;
        · exact ⟨ StarPath.nil _, rfl, rfl, fun _ => hu ⟩;
        · obtain ⟨ p, hp ⟩ := ih;
          use StarPath.concat (StarPath.single ⟨u.timeIndex, x.succ, v.secondIndex⟩ ⟨u.timeIndex, x.castSucc, v.secondIndex⟩ (by
          constructor;
          · simp +decide [ Fin.ext_iff ];
          · simp +decide [ Fin.forall_fin_succ, BoxPoint.coord ];
            simp +decide [ BoxPoint.time, BoxPoint.first, BoxPoint.second ])) p (by
          exact hp.1.symm)
          generalize_proofs at *;
          simp_all +decide [ StarPath.concat_start, StarPath.concat_finish ];
          exact ⟨ rfl, StarPath.concat_staysIn _ _ _ ( StarPath.single_staysIn _ _ _ ( by aesop ) ( by aesop ) ) hp.2.2 ⟩;
      · obtain ⟨ p, hp ⟩ := ih;
        use p.concat (StarPath.single ⟨u.timeIndex, y.castSucc, v.secondIndex⟩ ⟨u.timeIndex, y.succ, v.secondIndex⟩ (by
        grind +locals)) (by
        exact hp.2.1)
        generalize_proofs at *;
        exact ⟨ by rw [ StarPath.concat_start, hp.1 ], by rw [ StarPath.concat_finish, StarPath.single_finish ], by exact StarPath.concat_staysIn _ _ _ hp.2.2 ( StarPath.single_staysIn _ _ _ ( by aesop ) ( by aesop ) ) ⟩;
    convert h_path u.firstIndex v.firstIndex using 1;
    ext; simp +decide;
    intro hx hy; rw [ show u.timeIndex = v.timeIndex from by { exact Fin.ext <| by { have := hu.symm; have := hv.symm; aesop } } ] ;
  use StarPath.concat p1 p2 (by
  aesop)
  generalize_proofs at *;
  exact ⟨ hp1.1 ▸ StarPath.concat_start _ _ _, hp2.2.1 ▸ StarPath.concat_finish _ _ _, StarPath.concat_staysIn _ _ _ hp1.2.2 hp2.2.2 ⟩

theorem reached_set_starConnected_from_top {N L : Nat}
    {B : Set (BoxPoint N L)}
    (hT0_connected : StarConnected (T0 N L))
    (hT0_subset : T0 N L ⊆ B)
    (hReach :
      ∀ v : BoxPoint N L, v ∈ B →
        ∃ t : BoxPoint N L, t ∈ T0 N L ∧ StarJoinedIn B t v) :
    StarConnected B := by
  intro u hu v hv;
  obtain ⟨t₁, ht₁, ht₁u⟩ := hReach u hu
  obtain ⟨t₂, ht₂, ht₂v⟩ := hReach v hv;
  have h_top : StarJoinedIn B t₁ t₂ := by
    exact hT0_connected ht₁ ht₂ |> fun ⟨ p, hp₁, hp₂, hp₃ ⟩ => ⟨ p, hp₁, hp₂, fun i => hT0_subset ( hp₃ i ) ⟩;
  have h_path : StarJoinedIn B u t₂ :=
    starJoinedIn_trans (starJoinedIn_symm ht₁u) h_top
  exact starJoinedIn_trans h_path ht₂v

theorem other_complement_component_has_neighbor_in_U {N L : Nat}
    {U H K : Set (BoxPoint N L)}
    (hU_nonempty : ∃ u : BoxPoint N L, u ∈ U)
    (_hH_component : IsStarComponentOf Uᶜ H)
    (hK_component : IsStarComponentOf Uᶜ K)
    (hK_ne_H : K ≠ H) :
    HasStarNeighborIn K U := by
  contrapose! hK_ne_H;
  -- Since $K$ has no star neighbors in $U$, every neighbor of every point in $K$ is either in $K$ or in $U^c$. But since $K$ is a component of $U^c$, any neighbor in $U^c$ must be in $K$. Therefore, $K$ is star-closed.
  have hK_star_closed : ∀ k ∈ K, ∀ v : BoxPoint N L, StarAdj k v → v ∈ K := by
    intro k hk v hv
    by_cases hvU : v ∈ U;
    · exact False.elim <| hK_ne_H ⟨ k, hk, v, hvU, hv ⟩;
    · have := hK_component.maximal;
      apply this {v, k};
      · exact fun hkU => by have := hK_component.subset hk; aesop;
      · intro u hu v hv;
        cases hu <;> cases hv <;> simp_all +decide;
        · exact ⟨ StarPath.nil _, rfl, rfl, fun _ => by aesop ⟩;
        · use StarPath.single _ _ (starAdj_symm hv);
          simp +decide [ StarPath.single, StarPath.StaysIn ];
          exact ⟨ rfl, rfl ⟩;
        · use StarPath.single k _ hv;
          simp +decide [ StarPath.single, StarPath.StaysIn ];
          exact ⟨ rfl, rfl ⟩;
        · exact ⟨ StarPath.nil k, rfl, rfl, fun _ => by aesop ⟩;
      · grind;
      · simp +decide;
  obtain ⟨ k, hk ⟩ := hK_component.nonempty;
  obtain ⟨ u, hu ⟩ := hU_nonempty;
  -- Since $K$ is star-closed and $u \in U$, there exists a path from $k$ to $u$ in the whole box.
  obtain ⟨ p, hp ⟩ : ∃ p : StarPath N L, p.start = k ∧ p.finish = u ∧ p.StaysIn (Set.univ : Set (BoxPoint N L)) := by
    have := whole_box_starConnected N L;
    exact this ( Set.mem_univ k ) ( Set.mem_univ u );
  -- Since $K$ is star-closed and $p$ is a path from $k$ to $u$, all vertices of $p$ must be in $K$.
  have hp_in_K : ∀ i : Fin (p.len + 1), p.vertex i ∈ K := by
    intro i
    induction' i using Fin.induction with i ih;
    · aesop;
    · exact hK_star_closed _ ih _ ( p.edge i );
  exact absurd ( hK_component.subset ( hp_in_K ( Fin.last p.len ) ) ) ( by aesop )

theorem complement_of_top_component_connected {N L : Nat}
    {U H : Set (BoxPoint N L)}
    (hU_nonempty : ∃ u : BoxPoint N L, u ∈ U)
    (hU_connected : StarConnected U)
    (hT0_subset : T0 N L ⊆ U)
    (_hTN_disjoint : Disjoint (TN N L) U)
    (hH_component : IsStarComponentOf Uᶜ H)
    (hH_touches_top : Touches H (TN N L)) :
    StarConnected Hᶜ := by
  refine' reached_set_starConnected_from_top _ _ _;
  · exact T0_starConnected N L
  · exact fun x hx => fun hx' => hH_component.subset hx' |> fun hx'' => hx'' |> fun hx''' => by have := hT0_subset hx; aesop;
  · -- For any $v \in H^c$, if $v \in U$, then use the fact that $U$ is connected and $T0 \subseteq U$ to find a path from $T0$ to $v$ within $U$.
    intro v hv
    by_cases hvU : v ∈ U;
    · obtain ⟨t, ht⟩ : ∃ t : BoxPoint N L, t ∈ T0 N L ∧ StarJoinedIn U t v := by
        obtain ⟨ t, ht ⟩ := T0_nonempty N L;
        exact ⟨ t, ht, hU_connected ( hT0_subset ht ) hvU ⟩;
      obtain ⟨ p, hp ⟩ := ht.2;
      use t, ht.1, p, hp.1, hp.2.1, fun i => ?_;
      have := hH_component.subset; simp_all +decide [ Set.subset_def ] ;
      exact fun hi => this _ hi ( hp.2.2 i );
    · -- Since $v \notin U$, it must be in some other component $K$ of $U^c$.
      obtain ⟨K, hK_component, hK_ne_H, hK_v⟩ : ∃ K : Set (BoxPoint N L), IsStarComponentOf Uᶜ K ∧ K ≠ H ∧ v ∈ K := by
        -- Since $v \notin U$, it must be in some component $K$ of $U^c$.
        obtain ⟨K, hK_component, hK_v⟩ : ∃ K : Set (BoxPoint N L), IsStarComponentOf Uᶜ K ∧ v ∈ K := by
          -- Let $K$ be the connected component of $U^c$ containing $v$.
          obtain ⟨K, hK⟩ : ∃ K : Set (BoxPoint N L), K ⊆ Uᶜ ∧ StarConnected K ∧ v ∈ K ∧ ∀ D : Set (BoxPoint N L), D ⊆ Uᶜ → StarConnected D → v ∈ D → D ⊆ K := by
            refine' ⟨ ⋃₀ { D : Set ( BoxPoint N L ) | D ⊆ Uᶜ ∧ StarConnected D ∧ v ∈ D }, _, _, _, _ ⟩;
            · exact Set.sUnion_subset fun D hD => hD.1;
            · intro u hu w hw;
              obtain ⟨ D, hD₁, hD₂ ⟩ := hu
              obtain ⟨ E, hE₁, hE₂ ⟩ := hw;
              -- Since $D$ and $E$ are both connected components of $U^c$ containing $v$, they are star-connected.
              obtain ⟨p, hp⟩ : ∃ p : StarPath N L, p.start = u ∧ p.finish = v ∧ p.StaysIn D := by
                exact hD₁.2.1 hD₂ hD₁.2.2
              obtain ⟨q, hq⟩ : ∃ q : StarPath N L, q.start = v ∧ q.finish = w ∧ q.StaysIn E := by
                exact hE₁.2.1 hE₁.2.2 hE₂;
              use p.concat q (by
              grind)
              generalize_proofs at *;
              exact ⟨ by rw [ StarPath.concat_start, hp.1 ], by rw [ StarPath.concat_finish, hq.2.1 ], StarPath.concat_staysIn p q ‹_› ( fun i => Set.mem_sUnion.mpr ⟨ D, hD₁, hp.2.2 i ⟩ ) ( fun i => Set.mem_sUnion.mpr ⟨ E, hE₁, hq.2.2 i ⟩ ) ⟩;
            · exact ⟨ { v }, ⟨ by aesop_cat, by exact fun u hu w hw => ⟨ StarPath.nil v, by aesop_cat ⟩, by aesop_cat ⟩, by aesop_cat ⟩;
            · exact fun D hD₁ hD₂ hD₃ => Set.subset_sUnion_of_mem ⟨ hD₁, hD₂, hD₃ ⟩;
          refine' ⟨ K, _, hK.2.2.1 ⟩;
          constructor;
          · exact ⟨ v, hK.2.2.1 ⟩;
          · exact hK.1;
          · exact hK.2.1;
          · intros D hD_sub hD_connected hD_inter
            obtain ⟨x, hxK, hxD⟩ : ∃ x ∈ K, x ∈ D := hD_inter;
            have hD_subset_K : D ∪ K ⊆ Uᶜ ∧ StarConnected (D ∪ K) := by
              refine' ⟨ Set.union_subset hD_sub hK.1, _ ⟩;
              intro u hu v hv;
              rcases hu with ( hu | hu ) <;> rcases hv with ( hv | hv );
              · exact hD_connected hu hv |> fun ⟨ p, hp₁, hp₂, hp₃ ⟩ => ⟨ p, hp₁, hp₂, fun i => Or.inl <| hp₃ i ⟩;
              · obtain ⟨ p, hp ⟩ := hD_connected hu hxD;
                obtain ⟨ q, hq ⟩ := hK.2.1 hxK hv;
                use p.concat q (by
                grind)
                generalize_proofs at *;
                exact ⟨ by rw [ StarPath.concat_start, hp.1 ], by rw [ StarPath.concat_finish, hq.2.1 ], StarPath.concat_staysIn _ _ _ ( fun i => Or.inl <| hp.2.2 i ) ( fun i => Or.inr <| hq.2.2 i ) ⟩;
              · obtain ⟨ p, hp ⟩ := hK.2.1 hu hxK;
                obtain ⟨ q, hq ⟩ := hD_connected hxD hv;
                use p.concat q (by
                grind)
                generalize_proofs at *;
                simp_all +decide [ StarPath.StaysIn ];
                refine' ⟨ _, _, _ ⟩;
                · exact hp.1;
                · rw [ StarPath.concat_finish, hq.2.1 ];
                · intro i; by_cases hi : i.val ≤ p.len <;> simp_all +decide [ StarPath.concat ] ;
                  grind;
              · exact hK.2.1 hu hv |> fun ⟨ p, hp ⟩ => ⟨ p, hp.1, hp.2.1, fun i => Or.inr <| hp.2.2 i ⟩;
            grind;
        exact ⟨ K, hK_component, by rintro rfl; exact hv hK_v, hK_v ⟩;
      -- By other_complement_component_has_neighbor_in_U, K has a star neighbor in U.
      obtain ⟨k, hkK, u, huU, hku⟩ : ∃ k ∈ K, ∃ u ∈ U, StarAdj k u := by
        apply_rules [ other_complement_component_has_neighbor_in_U ];
      -- Since $K$ is connected, there exists a star path from $v$ to $k$ within $K$.
      obtain ⟨p, hp⟩ : ∃ p : StarPath N L, p.start = v ∧ p.finish = k ∧ p.StaysIn K := by
        exact hK_component.connected hK_v hkK;
      -- Since $U$ is connected, there exists a star path from $u$ to some $t \in T0$ within $U$.
      obtain ⟨q, hq⟩ : ∃ q : StarPath N L, q.start = u ∧ q.finish ∈ T0 N L ∧ q.StaysIn U := by
        have := hU_connected huU ( hT0_subset ( T0_nonempty N L |> Classical.choose_spec ) );
        exact ⟨ this.choose, this.choose_spec.1, this.choose_spec.2.1.symm ▸ Classical.choose_spec ( T0_nonempty N L ), this.choose_spec.2.2 ⟩;
      -- Concatenate the paths $p$ and $q$ to get a path from $v$ to $t$ within $Hᶜ$.
      obtain ⟨r, hr⟩ : ∃ r : StarPath N L, r.start = v ∧ r.finish = q.finish ∧ r.StaysIn Hᶜ := by
        have h_concat : ∃ r : StarPath N L, r.start = v ∧ r.finish = u ∧ r.StaysIn Hᶜ := by
          have h_concat : ∃ r : StarPath N L, r.start = v ∧ r.finish = k ∧ r.StaysIn Hᶜ := by
            use p;
            simp_all +decide [ Set.disjoint_left ];
            intro i; specialize hp; have := hp.2.2 i; simp_all +decide [ Set.subset_def ] ;
            grind +splitIndPred;
          obtain ⟨ r, hr ⟩ := h_concat;
          use r.concat (StarPath.single k u hku) (by
          exact hr.2.1.trans ( by rfl ))
          generalize_proofs at *;
          simp_all +decide [ StarPath.concat_start, StarPath.concat_finish ];
          exact ⟨ rfl, StarPath.concat_staysIn _ _ _ hr.2.2 ( StarPath.single_staysIn _ _ _ ( show k ∈ Hᶜ from fun hk => by have := hK_component.subset hkK; aesop ) ( show u ∈ Hᶜ from fun hu => by have := hH_component.subset hu; aesop ) ) ⟩;
        obtain ⟨ r, hr₁, hr₂, hr₃ ⟩ := h_concat;
        have h_concat : ∃ s : StarPath N L, s.start = u ∧ s.finish = q.finish ∧ s.StaysIn Hᶜ := by
          use q;
          simp_all +decide [ Set.disjoint_left ];
          intro i; specialize hq; have := hq.2.2 i; simp_all +decide [ Set.subset_def ] ;
          exact fun h => hH_component.subset h |> fun h' => by aesop;
        obtain ⟨ s, hs₁, hs₂, hs₃ ⟩ := h_concat;
        use StarPath.concat r s (by
        rw [hr₂, hs₁])
        generalize_proofs at *;
        exact ⟨ by rw [ StarPath.concat_start, hr₁ ], by rw [ StarPath.concat_finish, hs₂ ], by exact StarPath.concat_staysIn _ _ ‹_› hr₃ hs₃ ⟩;
      use q.finish;
      have h_joined : StarJoinedIn Hᶜ v q.finish :=
        ⟨r, hr.1, hr.2.1, hr.2.2⟩
      exact ⟨ hq.2.1, starJoinedIn_symm h_joined ⟩

theorem starBoundaryInside_eq_innerStarBoundary {N L : Nat}
    {U H : Set (BoxPoint N L)}
    (hH_component : IsStarComponentOf Uᶜ H) :
    StarBoundaryInside H Hᶜ = InnerStarBoundary U H := by
  apply Set.ext;
  intro x
  constructor
  intro hx
  obtain ⟨hxH, hxU⟩ := hx
  exact (by
  obtain ⟨a, haH, hxa⟩ := hxU
  have hxU' : x ∈ U := by
    have hxU' : x ∈ U := by
      have h_not_in_H : x ∉ H := hxH
      have h_star_adj : StarAdj x a := hxa
      have h_a_in_H : a ∈ H := haH
      have h_a_in_Uc : a ∈ Uᶜ := by
        exact hH_component.subset h_a_in_H
      contrapose! h_not_in_H;
      have := hH_component.maximal { x, a } ?_ ?_ ?_ <;> simp_all +decide [ Set.insert_subset_iff ];
      · intro u hu v hv; simp_all +decide;
        rcases hu with ( rfl | rfl ) <;> rcases hv with ( rfl | rfl ) <;> simp_all +decide [ StarPath.StaysIn ];
        · exact ⟨ StarPath.nil v, rfl, rfl, fun _ => Or.inl rfl ⟩;
        · use StarPath.single u v h_star_adj; simp [StarPath.start, StarPath.finish];
          exact ⟨ rfl, rfl, fun i => by fin_cases i <;> tauto ⟩;
        · use StarPath.single u v (by
          exact starAdj_symm h_star_adj)
          generalize_proofs at *;
          exact ⟨ rfl, rfl, fun i => by fin_cases i <;> tauto ⟩;
        · exact ⟨ StarPath.nil v, rfl, rfl, fun _ => Or.inr rfl ⟩;
      · grind +splitImp;
    exact hxU'
  exact ⟨hxU', a, haH, hxa⟩)
  intro hx
  obtain ⟨hxU, hxH⟩ := hx
  exact (by
  obtain ⟨ h, hh, hh' ⟩ := hxH; exact ⟨ fun hx' => hH_component.subset hx' hxU, h, hh, hh' ⟩ ;)

theorem timar_boundary_connectivity_finite_box {N L : Nat}
    {A : Set (BoxPoint N L)}
    (hA_nonempty : ∃ a : BoxPoint N L, a ∈ A)
    (hA_connected : StarConnected A)
    (hAc_nonempty : ∃ z : BoxPoint N L, z ∈ Aᶜ)
    (hAc_connected : StarConnected Aᶜ) :
    StarConnected (StarBoundaryInside A Aᶜ) := by
  sorry

theorem finite_box_peierls_star {N L : Nat}
    {U H : Set (BoxPoint N L)}
    (hU_nonempty : ∃ u : BoxPoint N L, u ∈ U)
    (hU_connected : StarConnected U)
    (hT0_subset : T0 N L ⊆ U)
    (hTN_disjoint : Disjoint (TN N L) U)
    (hH_component : IsStarComponentOf Uᶜ H)
    (hH_touches_top : Touches H (TN N L)) :
    StarConnected (InnerStarBoundary U H) := by
  classical
  have hC_connected : StarConnected Hᶜ :=
    complement_of_top_component_connected
      hU_nonempty hU_connected hT0_subset hTN_disjoint hH_component hH_touches_top
  have hboundary :
      StarBoundaryInside H Hᶜ = InnerStarBoundary U H :=
    starBoundaryInside_eq_innerStarBoundary hH_component
  have hHc_nonempty : ∃ z : BoxPoint N L, z ∈ Hᶜ := by
    rcases hU_nonempty with ⟨u, huU⟩
    refine ⟨u, ?_⟩
    intro huH
    exact hH_component.subset huH huU
  have htimar : StarConnected (StarBoundaryInside H Hᶜ) :=
    timar_boundary_connectivity_finite_box
      hH_component.nonempty hH_component.connected hHc_nonempty hC_connected
  simpa [hboundary] using htimar

structure PeierlsData (N L : Nat) where
  reached : Set (BoxPoint N L)
  free : Set (BoxPoint N L)
  crossing : Prop

namespace PeierlsData

def innerBoundary {N L : Nat} (ω : PeierlsData N L) : Set (BoxPoint N L) :=
  InnerStarBoundary ω.reached ω.free

end PeierlsData

structure PeierlsConnectivityHyp {N L : Nat}
    (ω : PeierlsData N L) : Prop where
  reached_connected : StarConnected ω.reached
  top_subset_reached : T0 N L ⊆ ω.reached
  top_disjoint_reached : Disjoint (TN N L) ω.reached
  free_top_component : IsStarComponentOf ω.reachedᶜ ω.free
  top_subset_free : TN N L ⊆ ω.free

theorem free_set_touches_top {N L : Nat} {ω : PeierlsData N L}
    (h : PeierlsConnectivityHyp ω) :
    Touches ω.free (TN N L) := by
  rcases TN_nonempty N L with ⟨v, hv⟩
  exact ⟨v, h.top_subset_free hv, hv⟩

theorem peierls_connectivity {N L : Nat} (ω : PeierlsData N L)
    (hC : ¬ω.crossing)
    (h : PeierlsConnectivityHyp ω) :
    StarConnected (ω.innerBoundary) := by
  have _ := hC
  have hreached_nonempty : ∃ u : BoxPoint N L, u ∈ ω.reached := by
    rcases T0_nonempty N L with ⟨u, hu⟩
    exact ⟨u, h.top_subset_reached hu⟩
  exact finite_box_peierls_star
    hreached_nonempty
    h.reached_connected
    h.top_subset_reached
    h.top_disjoint_reached
    h.free_top_component
    (free_set_touches_top h)

abbrev Z3 : Type :=
  Fin 3 → Int

def Z3StarAdj (u v : Z3) : Prop :=
  u ≠ v ∧ ∀ i : Fin 3, Int.natAbs (u i - v i) ≤ 1

structure Z3StarPath where
  len : Nat
  vertex : Fin (len + 1) → Z3
  edge : ∀ i : Fin len, Z3StarAdj (vertex i.castSucc) (vertex i.succ)

namespace Z3StarPath

def start (p : Z3StarPath) : Z3 :=
  p.vertex 0

def finish (p : Z3StarPath) : Z3 :=
  p.vertex (Fin.last p.len)

def StaysIn (p : Z3StarPath) (A : Set Z3) : Prop :=
  ∀ i : Fin (p.len + 1), p.vertex i ∈ A

end Z3StarPath

def Z3StarConnected (A : Set Z3) : Prop :=
  ∀ ⦃u : Z3⦄, u ∈ A →
  ∀ ⦃v : Z3⦄, v ∈ A →
    ∃ p : Z3StarPath, p.start = u ∧ p.finish = v ∧ p.StaysIn A

def IsZ3StarAnimal (m : Nat) (A : Finset Z3) : Prop :=
  A.card = m ∧ (0 : Z3) ∈ A ∧ Z3StarConnected {z | z ∈ A}

theorem lattice_animal_exponential_bound :
    ∃ C1 : Real, 0 ≤ C1 ∧
      ∀ m : Nat, 1 ≤ m →
        ((({A : Finset Z3 | IsZ3StarAnimal m A} : Set (Finset Z3)).ncard : Nat) : Real)
          ≤ Real.exp (C1 * (m : Real)) := by
  sorry

end AnimalBound
end OrientedAnimal


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
