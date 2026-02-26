import Mathlib

open scoped BigOperators ENNReal

namespace Scratch

noncomputable section

variable {d : ℕ}

abbrev Zd (d : ℕ) : Type := Fin d → ℤ

def IsNN (x y : Zd d) : Prop :=
  ∃ i : Fin d, (∀ j : Fin d, j ≠ i → x j = y j) ∧ (y i = x i + 1 ∨ y i = x i - 1)

abbrev Weights (d : ℕ) : Type := Zd d → Zd d → ℝ≥0∞

structure SAPath (d : ℕ) where
  verts : List (Zd d)
  nonempty : verts ≠ []
  adj : verts.Chain' (IsNN (d := d))
  nodup : verts.Nodup

namespace SAPath

variable {d : ℕ}

def start (γ : SAPath d) : Zd d := γ.verts.head!

def finish (γ : SAPath d) : Zd d := γ.verts.getLast γ.nonempty

def edges (γ : SAPath d) : List (Zd d × Zd d) := γ.verts.zip γ.verts.tail

def time (w : Weights d) (γ : SAPath d) : ℝ≥0∞ := (γ.edges.map (fun e => w e.1 e.2)).sum

def Between (x y : Zd d) : Set (SAPath d) := {γ | γ.start = x ∧ γ.finish = y}

end SAPath


def passageTimeZd (w : Weights d) (x y : Zd d) : ℝ≥0∞ :=
  sInf (Set.image (SAPath.time (d := d) w) (SAPath.Between (d := d) x y))

namespace FPP

open SAPath

private def NNGraph (d : ℕ) : SimpleGraph (Zd d) where
  Adj := IsNN (d := d)
  symm := by
    intro x y h
    rcases h with ⟨i, hij, hi⟩
    refine ⟨i, ?_, ?_⟩
    · intro j hj
      symm
      exact hij j hj
    · rcases hi with hpos | hneg
      · right
        linarith
      · left
        linarith
  loopless := by
    intro x h
    rcases h with ⟨i, -, hi⟩
    rcases hi with hpos | hneg <;> linarith

-- Build a walk whose support is exactly a given nonempty chain list.
private def walkOfList (d : ℕ) :
    ∀ (l : List (Zd d)) (hne : l ≠ []) (hchain : l.Chain' (IsNN (d := d))),
      (NNGraph d).Walk l.head! (l.getLast hne)
  | [], hne, _ => (hne rfl).elim
  | a :: [], _, _ => by
      simpa using (SimpleGraph.Walk.nil : (NNGraph d).Walk a a)
  | a :: b :: tl, _, hchain => by
      -- extract adjacency a~b
      have hab : (NNGraph d).Adj a b := (show IsNN (d := d) a b from (by
        -- `Chain'` unfolds to an `And` in the cons-cons case.
        simpa using (And.left (by simpa using hchain) : IsNN (d := d) a b)))
      -- chain on the tail
      have hchain' : (b :: tl).Chain' (IsNN (d := d)) := by
        simpa using (And.right (by simpa using hchain) : (b :: tl).Chain' (IsNN (d := d)))
      have hne' : (b :: tl) ≠ [] := by simp
      exact SimpleGraph.Walk.cons hab (walkOfList d (b :: tl) hne' hchain')

private lemma support_walkOfList (d : ℕ) :
    ∀ (l : List (Zd d)) (hne : l ≠ []) (hchain : l.Chain' (IsNN (d := d))),
      (walkOfList d l hne hchain).support = l
  | [], hne, _ => (hne rfl).elim
  | a :: [], _, _ => by
      simp [walkOfList]
  | a :: b :: tl, _, hchain => by
      -- unfold walkOfList; support of cons is cons of support
      simp [walkOfList, support_walkOfList, hchain]

private def walkTime (d : ℕ) (w : Weights d) {u v : Zd d} (p : (NNGraph d).Walk u v) : ℝ≥0∞ :=
  (p.darts.map (fun d' => w d'.fst d'.snd)).sum

private lemma walkTime_cons (d : ℕ) (w : Weights d) {u v t : Zd d}
    (h : (NNGraph d).Adj u v) (p : (NNGraph d).Walk v t) :
    walkTime d w (SimpleGraph.Walk.cons h p) = w u v + walkTime d w p := by
  simp [walkTime]

private lemma walkTime_append (d : ℕ) (w : Weights d) {u v t : Zd d}
    (p : (NNGraph d).Walk u v) (q : (NNGraph d).Walk v t) :
    walkTime d w (p.append q) = walkTime d w p + walkTime d w q := by
  simp [walkTime, List.map_append, List.sum_append]

private lemma walkTime_dropUntil_le (d : ℕ) (w : Weights d) {u v : Zd d}
    (p : (NNGraph d).Walk u v) (x : Zd d) (hx : x ∈ p.support) :
    walkTime d w (p.dropUntil x hx) ≤ walkTime d w p := by
  have hs : p = (p.takeUntil x hx).append (p.dropUntil x hx) := by
    simpa using (SimpleGraph.Walk.take_spec (p := p) (u := x) hx).symm
  have htime : walkTime d w p =
      walkTime d w (p.takeUntil x hx) + walkTime d w (p.dropUntil x hx) := by
    -- rewrite using hs then apply walkTime_append
    simpa [hs, walkTime_append] using (walkTime_append d w (p.takeUntil x hx) (p.dropUntil x hx))
  have hnonneg : 0 ≤ walkTime d w (p.takeUntil x hx) := by exact bot_le
  calc
    walkTime d w (p.dropUntil x hx)
        ≤ walkTime d w (p.takeUntil x hx) + walkTime d w (p.dropUntil x hx) := by
              simpa [zero_add] using (le_add_of_nonneg_left hnonneg)
    _ = walkTime d w p := by
          simpa [htime, add_comm, add_left_comm, add_assoc]

private lemma walkTime_bypass_le (d : ℕ) (w : Weights d) {u v : Zd d}
    (p : (NNGraph d).Walk u v) : walkTime d w p.bypass ≤ walkTime d w p := by
  classical
  induction p with
  | nil =>
      simp [SimpleGraph.Walk.bypass, walkTime]
  | cons ha p ih =>
      by_cases hs : u ∈ p.bypass.support
      ·
        have h1 : walkTime d w (p.bypass.dropUntil u hs) ≤ walkTime d w p.bypass :=
          walkTime_dropUntil_le d w (p := p.bypass) (x := u) hs
        have h3 : walkTime d w p ≤ walkTime d w (SimpleGraph.Walk.cons ha p) := by
          simp [walkTime_cons, le_add_of_nonneg_left]
        have : walkTime d w (p.bypass.dropUntil u hs) ≤ walkTime d w p := le_trans h1 ih
        -- unfold bypass under `hs`
        simpa [SimpleGraph.Walk.bypass, hs] using le_trans this h3
      ·
        have h2 : w u v + walkTime d w p.bypass ≤ w u v + walkTime d w p :=
          add_le_add_left ih (w u v)
        simpa [SimpleGraph.Walk.bypass, hs, walkTime_cons] using h2

end FPP

end

end Scratch