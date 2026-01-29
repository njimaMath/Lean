open Classical
variable {A : Type} (P Q : A → Prop)

theorem E4: ( ∃ (a : A), (P a ∨Q a) ) ↔ ( ∃ (a : A), P  a) ∨ ( ∃ (a : A), Q a):= by
  constructor
  rintro ⟨a, ha | ha⟩
  exact Or.inl (Exists.intro a ha)
  exact Or.inr (Exists.intro a ha)
  rintro ( ⟨a, ha⟩| ⟨ a, ha⟩)
  exact ⟨a, Or.inl ha⟩
  exact ⟨a, Or.inr ha⟩




theorem E5: (∀ (a:A),P a) ↔ ¬ (∃ (a:A), (¬ P a)) := by
  constructor
  intro ha
  rintro ⟨ a, hb⟩
  exact hb (ha a)
  intro ha
  intro a
  have hc (h: ¬ P a): (∃ b, ¬ (P b)):= by
    exact Exists.intro a h
  apply byContradiction
  intro hd
  exact ha (hc hd)

theorem E11 {R:Prop}: (∃ (a:A), R → P a) → (R → ∃ (a:A), P a) := by
  intro ha
  intro hR
  cases ha
  rename_i b hb
  exact Exists.intro b (hb hR)



theorem TEqRW {a b : A} (h1: a = b) : P b ↔ P a := by
  constructor
  intro hb
  rewrite [h1]
  exact hb
  intro ha
  rw [h1] at ha
  apply ha


variable {B:Type}

def injective (f: A→ B): Prop := ∀ (a b:A), (f a = f b) → a = b

def monomorphism (f: A→ B): Prop := ∀{C:Type}, ∀{g h:C→ A}, (f∘ g = f∘ h) → g = h


theorem E15 (f:A→ B): injective f ↔ monomorphism f:= by
  constructor
  intro h1
  intro C g h
  intro h2
  funext c
  apply h1
  exact congrFun h2 c
  intro h1
  intro b c h3
  let g : PUnit → A := fun _ => b
  let h : PUnit → A := fun _ => c
  have hfg : f ∘ g = f ∘ h := by
    funext _
    simpa [g, h] using h3
  have hgh : g = h := h1 (C := PUnit) (g := g) (h := h) hfg
  have : b = c := by
    simpa [g, h] using congrFun hgh PUnit.unit
  exact this



inductive N : Type where
| z:N
| s: N→ N
deriving Repr

open N

def Eqzero: N → Bool := by
  intro n
  cases n
  exact true
  exact false

open N

theorem TInJ: ∀ (n:N), z ≠ s n := by
  intro n
  intro h
  cases h

theorem TSuccInj : injective s:= by
  intro b c h
  cases h
  rfl

theorem TInd {P: N → Prop} (h0 : P z) (hi: ∀ (n:N), P n → P (s n) ): ∀ (n:N), P n := by
 intro n
 induction n
 apply h0
 rename_i n h
 apply hi
 exact h

def max : N → N → N := by
  intro n m
  match n, m with
    | (z), m => exact m
    | n, z => exact n
    | (s n), (s m) => exact s (max n m)

def addN: N → N → N := by
  intro n m
  match n, m with
  | z, m => exact m
  | (s n), m => exact s (addN n m)

theorem addCommN (n: N) : ∀ (m: N), addN n m = addN m n := by
  induction n with
  | z =>
      intro m
      induction m
      simp
      rename_i m h
      rw [addN]
      simp [addN]
      have h1: m = addN z m := by simp [addN]
      -- next step will be added below
      exact Eq.trans h1 h
  | s n hi =>
      intro m
      induction m with
      | z =>
        simp [addN]
        have h2: addN z n = n := by simp [addN]
        exact Eq.trans (hi z) h2
      | s m hii =>
        simp [addN]
        rw [hi]
        simp [addN]
        rw [← hii]
        rw [← hi]
        simp [addN]


theorem addAss (n: N) : ∀ (m k: N), addN (addN n m) k = addN n (addN m k) := by
  induction n with
  | z => simp [addN]
  | s n hn =>
    intro m k
    simp [addN]
    rw [hn m k]

def mul: N → N → N := by
  intro n m
  match n with
    | z => exact z
    | s n => exact addN (mul n m) m

theorem mulComm (n:N): ∀ m:N, mul n m = mul m n := by
  induction n with
    | z =>
      intro m
      induction m with
        | z => simp [mul]
        | s m hm =>
          simp [mul]
          rw [addCommN (mul m z) z]
          rw [← hm]
          simp [mul]
          simp [addN]
    | s n =>
      rename_i hn
      intro m
      induction m with
      | z =>
        simp [mul]
        rw [addCommN (mul n z) z]
        simp [addN]
        rw [hn z]
        simp [mul]
      | s m hm =>
        simp [mul]
        rw [← hm]
        rw [addCommN _ m.s]
        rw [addCommN _ n.s]
        simp [addN]
        rw [hn m.s]
        simp [mul]
        rw [← addAss m _ _]
        rw [addCommN n _]
        rw [addCommN _ m]
        rw [hn m]










def divisible_by_two : N → Prop
| N.z => True
| N.s N.z => False
| N.s (N.s n) => divisible_by_two n
