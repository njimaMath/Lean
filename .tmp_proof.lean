import Mathlib

open scoped BigOperators
open scoped ENNReal

namespace Scratch

noncomputable section

variable {d : ℕ}

/-- The vertex set `Z^d`, represented as functions `Fin d → ℤ`. -/
abbrev Zd (d : ℕ) : Type := Fin d → ℤ

/-- Nearest-neighbor relation on `Z^d`. -/
def IsNN (x y : Zd d) : Prop :=
  ∃ i : Fin d, (∀ j : Fin d, j ≠ i → x j = y j) ∧ (y i = x i + 1 ∨ y i = x i - 1)

/-- Edge weights on oriented pairs of vertices (no symmetry assumed). -/
abbrev Weights (d : ℕ) : Type := Zd d → Zd d → ℝ≥0∞

structure SAPath (d : ℕ) where
  verts : List (Zd d)
  nonempty : verts ≠ []
  adj : verts.Chain' (IsNN (d := d))
  nodup : verts.Nodup

namespace SAPath

variable {d : ℕ}

/-- Start vertex of a path. -/
def start (γ : SAPath d) : Zd d := γ.verts.head!

/-- End vertex of a path. -/
def finish (γ : SAPath d) : Zd d := γ.verts.getLast γ.nonempty

/-- The oriented edge list of consecutive vertex pairs. -/
def edges (γ : SAPath d) : List (Zd d × Zd d) :=
  γ.verts.zip γ.verts.tail

/-- Passage time of a path for a given weight function. -/
def time (w : Weights d) (γ : SAPath d) : ℝ≥0∞ :=
  (γ.edges.map (fun e => w e.1 e.2)).sum

/-- The set of self-avoiding paths from `x` to `y`. -/
def Between (x y : Zd d) : Set (SAPath d) :=
  {γ | γ.start = x ∧ γ.finish = y}

end SAPath

/-- First-passage time on `Z^d`: infimum of passage times over self-avoiding paths. -/
def passageTimeZd (w : Weights d) (x y : Zd d) : ℝ≥0∞ :=
  sInf (Set.image (SAPath.time (d := d) w) (SAPath.Between (d := d) x y))

namespace FPP

open SAPath

-- Helper: NNGraph
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
    rcases hi with hpos | hneg
    · linarith
    · linarith

-- Build a walk whose support is exactly a given nonempty chain list.
private def walkOfList :
    ∀ {d : ℕ} (l : List (Zd d)), l ≠ [] → l.Chain' (IsNN (d := d)) →
      (NNGraph d).Walk l.head! (l.getLast (by simpa using (show l ≠ [] from by intro h; cases h)))
  := by
    intro d l hne hchain
    -- We'll define this by recursion on l
    induction l with
    | nil => cases hne rfl
    | cons a tl ih =>
      -- cases on tl
      cases tl with
      | nil =>
        -- l = [a]
        simpa using (SimpleGraph.Walk.nil : (NNGraph d).Walk a a)
      | cons b tl' =>
        -- l = a :: b :: tl'
        have hab : (NNGraph d).Adj a b := by
          -- from chain
          simpa [NNGraph, IsNN] using (hchain.rel_head : IsNN (d := d) a b)
        -- chain on tail
        have hchain' : (b :: tl').Chain' (IsNN (d := d)) := by
          simpa using hchain.tail
        -- nonempty of tail
        have hne' : (b :: tl') ≠ [] := by simp
        -- build tail walk
        have p := ih (l := b :: tl') hne' hchain'
        -- cons
        exact SimpleGraph.Walk.cons hab p

private lemma support_walkOfList {d : ℕ} :
    ∀ (l : List (Zd d)) (hne : l ≠ []) (hchain : l.Chain' (IsNN (d := d))),
      (walkOfList (d := d) l hne hchain).support = l := by
  intro l hne hchain
  induction l with
  | nil => cases hne rfl
  | cons a tl ih =>
    cases tl with
    | nil =>
      simp [walkOfList]
    | cons b tl' =>
      -- simplify walkOfList
      simp [walkOfList, support_walkOfList, ih, hchain, hchain.tail]

-- Define time on walks using darts.
private def walkTime {d : ℕ} (w : Weights d) {u v : Zd d} ((p : (NNGraph d).Walk u v)) : ℝ≥0∞ :=
  (p.darts.map (fun d' => w d'.fst d'.snd)).sum

private lemma walkTime_nil {d : ℕ} (w : Weights d) (u : Zd d) :
    walkTime (d := d) w (SimpleGraph.Walk.nil : (NNGraph d).Walk u u) = 0 := by
  simp [walkTime]

private lemma walkTime_cons {d : ℕ} (w : Weights d) {u v t : Zd d}
    (h : (NNGraph d).Adj u v) (p : (NNGraph d).Walk v t) :
    walkTime (d := d) w (SimpleGraph.Walk.cons h p) = w u v + walkTime (d := d) w p := by
  simp [walkTime]

private lemma walkTime_append {d : ℕ} (w : Weights d) {u v t : Zd d}
    (p : (NNGraph d).Walk u v) (q : (NNGraph d).Walk v t) :
    walkTime (d := d) w (p.append q) = walkTime (d := d) w p + walkTime (d := d) w q := by
  simp [walkTime, List.map_append, List.sum_append]

-- Compare dropUntil time
private lemma walkTime_dropUntil_le {d : ℕ} (w : Weights d) {u v : Zd d}
    (p : (NNGraph d).Walk u v) (x : Zd d) (hx : x ∈ p.support) :
    walkTime (d := d) w (p.dropUntil x hx) ≤ walkTime (d := d) w p := by
  -- Use take_spec: takeUntil ++ dropUntil = p
  have hs := (SimpleGraph.Walk.take_spec (p := p) (u := x) hx)
  -- rewrite time(p) as time(takeUntil)+time(dropUntil)
  -- using append
  -- from hs: (p.takeUntil ...).append (p.dropUntil ...) = p
  -- so p = ...; rewrite
  have : walkTime (d := d) w p =
      walkTime (d := d) w (p.takeUntil x hx) + walkTime (d := d) w (p.dropUntil x hx) := by
    -- start from append formula
    --
    simpa [hs, walkTime_append] using (walkTime_append (d := d) w (p.takeUntil x hx) (p.dropUntil x hx))
  -- Now dropUntil time ≤ sum
  -- Use le_add_of_nonneg_left since first term is ≥0
  have hnonneg : 0 ≤ walkTime (d := d) w (p.takeUntil x hx) := by
    -- ENNReal is nonnegative
    exact bot_le
  -- from this: walkTime dropUntil ≤ walkTime takeUntil + walkTime dropUntil = walkTime p
  --
  --
  --
  calc
    walkTime (d := d) w (p.dropUntil x hx)
        ≤ walkTime (d := d) w (p.takeUntil x hx) + walkTime (d := d) w (p.dropUntil x hx) := by
              simpa [zero_add] using (le_add_of_nonneg_left hnonneg)
    _ = walkTime (d := d) w p := by
          simpa [this, add_comm, add_left_comm, add_assoc]

-- Prove bypass time ≤ original time.
private lemma walkTime_bypass_le {d : ℕ} (w : Weights d) {u v : Zd d}
    [DecidableEq (Zd d)] (p : (NNGraph d).Walk u v) :
    walkTime (d := d) w p.bypass ≤ walkTime (d := d) w p := by
  -- Induction on p
  induction p with
  | nil =>
    simp [SimpleGraph.Walk.bypass, walkTime]
  | cons ha p ih =>
    simp [SimpleGraph.Walk.bypass] at *
    -- p.bypass = if u ∈ p.bypass.support then ... else cons ha p.bypass
    -- simp produced let p' := p.bypass
    -- We'll split on membership
    by_cases hs : u ∈ (SimpleGraph.Walk.bypass p).support
    · -- then bypass = dropUntil
      --
      --
      -- We need show time(dropUntil) ≤ time(cons ha p)
      -- Use dropUntil ≤ time p.bypass, then ih, then ≤ cons
      have h1 : walkTime (d := d) w ((SimpleGraph.Walk.bypass p).dropUntil u hs) ≤
          walkTime (d := d) w (SimpleGraph.Walk.bypass p) :=
        walkTime_dropUntil_le (d := d) w (p := SimpleGraph.Walk.bypass p) (x := u) hs
      have h2 : walkTime (d := d) w (SimpleGraph.Walk.bypass p) ≤ walkTime (d := d) w p := ih
      have h3 : walkTime (d := d) w p ≤ walkTime (d := d) w (SimpleGraph.Walk.cons ha p) := by
        -- cons adds nonnegative weight
        --
        -- from walkTime_cons
        simp [walkTime_cons, le_add_of_nonneg_left]  -- maybe
      -- Now
      --
      have : walkTime (d := d) w ((SimpleGraph.Walk.bypass p).dropUntil u hs) ≤ walkTime (d := d) w p :=
        le_trans h1 h2
      -- show ≤ time(cons)
      exact le_trans this h3
    · -- else bypass = cons ha p.bypass
      --
      --
      -- use ih and add monotone
      --
      have : walkTime (d := d) w (SimpleGraph.Walk.bypass p) ≤ walkTime (d := d) w p := ih
      --
      --
      --
      --
      --
      --
      --
      --
      --
      --
      --
      --
      --
      --
      --
      --
      -- We'll simp bypass under hs false
      simp [SimpleGraph.Walk.bypass, hs, walkTime_cons, this, add_le_add_left]  -- hmm

end FPP

end Scratch