import Mathlib

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
