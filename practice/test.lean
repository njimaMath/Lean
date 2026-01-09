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
