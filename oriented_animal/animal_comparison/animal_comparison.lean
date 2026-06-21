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
