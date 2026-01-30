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

private def walkOfList (d : ℕ) :
    ∀ (l : List (Zd d)) (hne : l ≠ []) (hchain : l.Chain' (IsNN (d := d))),
      (NNGraph d).Walk l.head! (l.getLast hne)
  | [], hne, _ => (hne rfl).elim
  | a :: [], _, _ => by
      simpa using (SimpleGraph.Walk.nil : (NNGraph d).Walk a a)
  | a :: b :: tl, _, hchain => by
      have hchain' : List.IsChain (IsNN (d := d)) (a :: b :: tl) :=
        (show List.IsChain (IsNN (d := d)) (a :: b :: tl) from hchain)
      have hab : (NNGraph d).Adj a b := List.IsChain.rel_head hchain'
      have htail : List.IsChain (IsNN (d := d)) (b :: tl) := List.IsChain.tail hchain'
      have htail' : (b :: tl).Chain' (IsNN (d := d)) :=
        (show (b :: tl).Chain' (IsNN (d := d)) from htail)
      have hne' : (b :: tl) ≠ [] := by simp
      exact SimpleGraph.Walk.cons hab (walkOfList d (b :: tl) hne' htail')

private lemma support_walkOfList (d : ℕ) :
    ∀ (l : List (Zd d)) (hne : l ≠ []) (hchain : l.Chain' (IsNN (d := d))),
      (walkOfList d l hne hchain).support = l
  | [], hne, _ => (hne rfl).elim
  | a :: [], _, _ => by
      simp [walkOfList]
  | a :: b :: tl, _, hchain => by
      simp [walkOfList, support_walkOfList]

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
  have ht : walkTime d w ((p.takeUntil x hx).append (p.dropUntil x hx)) = walkTime d w p := by
    simpa using congrArg (fun q => walkTime d w q)
      (SimpleGraph.Walk.take_spec (p := p) (u := x) hx)
  have happ : walkTime d w ((p.takeUntil x hx).append (p.dropUntil x hx)) =
      walkTime d w (p.takeUntil x hx) + walkTime d w (p.dropUntil x hx) :=
    walkTime_append d w (p.takeUntil x hx) (p.dropUntil x hx)
  have htime : walkTime d w p = walkTime d w (p.takeUntil x hx) + walkTime d w (p.dropUntil x hx) :=
    ht.symm.trans happ
  have hnonneg : 0 ≤ walkTime d w (p.takeUntil x hx) := by exact bot_le
  calc
    walkTime d w (p.dropUntil x hx)
        ≤ walkTime d w (p.takeUntil x hx) + walkTime d w (p.dropUntil x hx) := by
              simpa [zero_add] using (le_add_of_nonneg_left hnonneg)
    _ = walkTime d w p := by
          simpa [htime, add_comm, add_left_comm, add_assoc]

private lemma walkTime_bypass_le (d : ℕ) (w : Weights d) :
    ∀ {u v : Zd d} (p : (NNGraph d).Walk u v), walkTime d w p.bypass ≤ walkTime d w p
  | _, _, SimpleGraph.Walk.nil => by
      simp [SimpleGraph.Walk.bypass, walkTime]
  | _, _, SimpleGraph.Walk.cons ha p => by
      classical
      -- unfold bypass and split on the internal `if`
      simp [SimpleGraph.Walk.bypass]
      split_ifs with hs
      ·
        have h1 : walkTime d w (p.bypass.dropUntil _ hs) ≤ walkTime d w p.bypass :=
          walkTime_dropUntil_le d w (p := p.bypass) (x := _) hs
        have h3 : walkTime d w p ≤ walkTime d w (SimpleGraph.Walk.cons ha p) := by
          simp [walkTime_cons, le_add_of_nonneg_left]
        exact le_trans (le_trans h1 (walkTime_bypass_le d w p)) h3
      ·
        have h2 : walkTime d w p.bypass ≤ walkTime d w p := walkTime_bypass_le d w p
        simpa [walkTime_cons, add_comm, add_left_comm, add_assoc] using
          (add_le_add_left h2 (w _ _))

end FPP

end

end Scratch