import Mathlib.Analysis.SpecialFunctions.Artanh
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Tactic

open Real

namespace SpinGlass
namespace GeneralizedLatala

/-!
# Kearns--Saul inequality

This file states the scalar form of the Kearns--Saul inequality needed at the
independent endpoint of the generalized Latała argument.  It has no dependency
on the spin-glass development.
-/

/-- The sharp sub-Gaussian coefficient for a random sign of mean `q`.

The separate value at `q = 0` is the continuous extension of
`q / artanh q`.
-/
noncomputable def ksCoefficient (q : ℝ) : ℝ :=
  if q = 0 then 1 else q / Real.artanh q

/-
A convenient form of the elementary inequality `x ≤ sinh x`.
-/
private lemma le_sinh_mul_cosh {x : ℝ} (hx : 0 ≤ x) :
    x ≤ Real.sinh x * Real.cosh x := by
  have h_subst : ∀ y : ℝ, 0 ≤ y → y ≤ Real.sinh y := by
    by_contra h_contra;
    -- Apply the fact that $y \leq \sinh y$ for all $y \geq 0$.
    have h_le : ∀ y : ℝ, 0 ≤ y → y ≤ Real.sinh y := by
      intro y hy; rw [ Real.sinh_eq ] ; ring_nf; norm_num [ hy ] ;
      -- Apply the inequality $e^y \geq 1 + y + \frac{y^2}{2}$ for $y \geq 0$.
      have h_exp_ineq : ∀ y : ℝ, 0 ≤ y → Real.exp y ≥ 1 + y + y^2 / 2 :=
        fun _ hy => Real.quadratic_le_exp_of_nonneg hy
      nlinarith [ h_exp_ineq y hy, Real.exp_pos y, Real.exp_neg y, mul_inv_cancel₀ ( ne_of_gt ( Real.exp_pos y ) ), Real.add_one_le_exp y, Real.add_one_le_exp ( -y ) ];
    contradiction;
  have := h_subst ( 2 * x ) ( mul_nonneg zero_le_two hx ) ; rw [ Real.sinh_two_mul ] at this; nlinarith [ Real.cosh_sq' x, Real.cosh_pos x ] ;

/-
The derivative of `tanh x / x` is nonpositive for positive `x`.
-/
private lemma deriv_tanh_div_nonpos {x : ℝ} (hx : 0 < x) :
    deriv (fun y : ℝ => Real.tanh y / y) x ≤ 0 := by
  -- Compute the derivative of `tanh x / x` using the quotient rule.
  have h_deriv : deriv (fun y => Real.tanh y / y) x = ((1 - Real.tanh x ^ 2) * x - Real.tanh x) / x ^ 2 := by
    unfold Real.tanh; ring;
    norm_num [ Complex.tanh, Complex.sinh, Complex.cosh, hx.ne' ];
    norm_cast ; norm_num [ Real.exp_ne_zero, Real.exp_neg, Real.differentiableAt_exp, hx.ne', div_eq_mul_inv, differentiableAt_inv ] ; ring;
    norm_num [ Real.exp_ne_zero, Real.differentiableAt_exp, differentiableAt_inv, ne_of_gt ( add_pos ( Real.exp_pos _ ) ( inv_pos.mpr ( Real.exp_pos _ ) ) ), ne_of_gt hx ] ; ring;
    -- Combine like terms and simplify the expression.
    field_simp
    ring;
  rw [ h_deriv, div_le_iff₀ ] <;> norm_num [ Real.tanh_eq_sinh_div_cosh ];
  · field_simp;
    simpa [ Real.cosh_sq' ] using le_sinh_mul_cosh hx.le;
  · positivity

/-- The quotient `tanh x / x` decreases on the positive half-line. -/
private lemma antitoneOn_tanh_div :
    AntitoneOn (fun x : ℝ => Real.tanh x / x) (Set.Ioi 0) := by
  have ht : Differentiable ℝ Real.tanh := by
    rw [show Real.tanh = fun x => Real.sinh x / Real.cosh x by
      funext x
      exact Real.tanh_eq_sinh_div_cosh x]
    exact Real.differentiable_sinh.div Real.differentiable_cosh
      fun x => (Real.cosh_pos x).ne'
  apply antitoneOn_of_deriv_nonpos (convex_Ioi 0)
  · apply ContinuousOn.div ht.continuous.continuousOn continuous_id.continuousOn
    intro x hx
    exact hx.ne'
  · rw [interior_Ioi]
    apply DifferentiableOn.div ht.differentiableOn differentiable_id.differentiableOn
    intro x hx
    exact hx.ne'
  · rw [interior_Ioi]
    intro x hx
    exact deriv_tanh_div_nonpos hx

/-
The logarithm of `cosh` lies below its tangent when regarded as a
function of the squared argument.
-/
private lemma log_cosh_le_quadratic_tangent {a : ℝ} (ha : 0 < a) (x : ℝ) :
    Real.log (Real.cosh x) - Real.log (Real.cosh a) ≤
      Real.tanh a / (2 * a) * (x ^ 2 - a ^ 2) := by
  by_cases hx : x = 0 <;> simp_all +decide [ ← Real.log_div, ne_of_gt, Real.cosh_pos ];
  · rw [ div_mul_eq_mul_div, div_le_iff₀ ] <;> try positivity;
    -- We'll use the fact that $\log(\cosh(a)) \geq \frac{a \tanh(a)}{2}$ for all $a > 0$.
    have h_log_cosh : ∀ a > 0, Real.log (Real.cosh a) ≥ a * Real.tanh a / 2 := by
      intro a ha
      have h_deriv : ∀ x > 0, deriv (fun x => Real.log (Real.cosh x) - x * Real.tanh x / 2) x ≥ 0 := by
        intro x hx; norm_num [ Real.tanh_eq_sinh_div_cosh, Real.differentiableAt_sinh, Real.differentiableAt_cosh, ne_of_gt ( Real.cosh_pos _ ) ] ; ring_nf; norm_num [ Real.sinh_sq, ne_of_gt ( Real.cosh_pos _ ) ] ;
        field_simp;
        nlinarith [ le_sinh_mul_cosh hx.le, Real.sinh_sq x, Real.cosh_pos x ];
      -- Apply the mean value theorem to the interval $[0, a]$.
      obtain ⟨c, hc⟩ : ∃ c ∈ Set.Ioo 0 a, deriv (fun x => Real.log (Real.cosh x) - x * Real.tanh x / 2) c = (Real.log (Real.cosh a) - a * Real.tanh a / 2 - (Real.log (Real.cosh 0) - 0 * Real.tanh 0 / 2)) / (a - 0) := by
        have := exists_deriv_eq_slope ( f := fun x => Real.log ( Real.cosh x ) - x * Real.tanh x / 2 ) ha;
        exact this ( ContinuousOn.sub ( ContinuousOn.log ( Real.continuous_cosh.continuousOn ) fun x hx => ne_of_gt ( Real.cosh_pos x ) ) ( ContinuousOn.div_const ( continuousOn_id.mul ( show ContinuousOn ( fun x => Real.tanh x ) ( Set.Icc 0 a ) from ContinuousOn.congr ( show ContinuousOn ( fun x => Real.sinh x / Real.cosh x ) ( Set.Icc 0 a ) from ContinuousOn.div ( Real.continuous_sinh.continuousOn ) ( Real.continuous_cosh.continuousOn ) fun x hx => ne_of_gt ( Real.cosh_pos x ) ) fun x hx => Real.tanh_eq_sinh_div_cosh x ) ) _ ) ) ( fun x hx => DifferentiableAt.differentiableWithinAt ( by norm_num [ Real.differentiableAt_sinh, Real.differentiableAt_cosh, ne_of_gt ( Real.cosh_pos _ ), Real.tanh_eq_sinh_div_cosh ] ) );
      have := h_deriv c hc.1.1; rw [ hc.2, ge_iff_le ] at this; rw [ le_div_iff₀ ] at this <;> norm_num at * <;> linarith;
    nlinarith [ h_log_cosh a ha ];
  · obtain ⟨b, hb⟩ : ∃ b > 0, Real.log (Real.cosh x) - Real.log (Real.cosh a) = Real.log (Real.cosh b) - Real.log (Real.cosh a) ∧ b^2 = x^2 := by
      exact ⟨ |x|, abs_pos.mpr hx, by simp +decide [ Real.cosh_abs ], by simp +decide ⟩;
    cases' lt_trichotomy b a with h h <;> simp_all +decide [ Real.log_div, ne_of_gt, Real.cosh_pos ];
    · -- By the mean value theorem, there exists some $c \in (b, a)$ such that $\frac{\log(\cosh a) - \log(\cosh b)}{a^2 - b^2} = \frac{\tanh c}{2c}$.
      obtain ⟨c, hc⟩ : ∃ c ∈ Set.Ioo b a, (Real.log (Real.cosh a) - Real.log (Real.cosh b)) / (a^2 - b^2) = Real.tanh c / (2 * c) := by
        have h_mean_value : ∃ c ∈ Set.Ioo b a, deriv (fun y => Real.log (Real.cosh y)) c / deriv (fun y => y^2) c = (Real.log (Real.cosh a) - Real.log (Real.cosh b)) / (a^2 - b^2) := by
          have h_mean_value : ∃ c ∈ Set.Ioo b a, deriv (fun y => Real.log (Real.cosh y) - (Real.log (Real.cosh b) + (Real.log (Real.cosh a) - Real.log (Real.cosh b)) / (a^2 - b^2) * (y^2 - b^2))) c = 0 := by
            apply_rules [ exists_deriv_eq_zero ];
            · exact ContinuousOn.sub ( ContinuousOn.log ( Real.continuous_cosh.continuousOn ) fun y hy => ne_of_gt ( Real.cosh_pos _ ) ) ( Continuous.continuousOn ( by continuity ) );
            · rw [ div_mul_cancel₀ ] <;> nlinarith;
          norm_num [ Real.differentiableAt_cosh, ne_of_gt ( Real.cosh_pos _ ) ] at *;
          exact h_mean_value.imp fun x hx => ⟨ hx.1, by rw [ div_eq_iff ( by linarith ) ] ; linarith ⟩;
        obtain ⟨ c, hc₁, hc₂ ⟩ := h_mean_value; use c; simp_all +decide [ Real.tanh_eq_sinh_div_cosh, Real.differentiableAt_sinh, Real.differentiableAt_cosh, ne_of_gt ( Real.cosh_pos _ ) ] ;
      -- Since $c \in (b, a)$, we have $\frac{\tanh c}{2c} \geq \frac{\tanh a}{2a}$ by the antitone property of $\frac{\tanh x}{x}$.
      have h_antitone : Real.tanh c / (2 * c) ≥ Real.tanh a / (2 * a) := by
        have h_antitone : AntitoneOn (fun x : ℝ => Real.tanh x / x) (Set.Ioi 0) :=
          antitoneOn_tanh_div
        have := h_antitone ( show 0 < c by linarith [ hc.1.1 ] ) ( show 0 < a by linarith ) ( by linarith [ hc.1.2 ] ) ; ring_nf at *; linarith;
      rw [ ← hb.2.2, ← hc.2, ge_iff_le, le_div_iff₀ ] at * <;> nlinarith;
    · cases' h with h h <;> simp_all +decide [ Real.tanh_eq_sinh_div_cosh ];
      -- By the mean value theorem, there exists some $c \in (a, b)$ such that $\frac{\log(\cosh b) - \log(\cosh a)}{b^2 - a^2} = \frac{\sinh c}{2c \cosh c}$.
      obtain ⟨c, hc⟩ : ∃ c ∈ Set.Ioo a b, (Real.log (Real.cosh b) - Real.log (Real.cosh a)) / (b^2 - a^2) = (Real.sinh c) / (2 * c * Real.cosh c) := by
        have h_mvt : ∃ c ∈ Set.Ioo a b, deriv (fun x => Real.log (Real.cosh x)) c / deriv (fun x => x^2) c = (Real.log (Real.cosh b) - Real.log (Real.cosh a)) / (b^2 - a^2) := by
          have h_mvt : ∃ c ∈ Set.Ioo a b, deriv (fun x => Real.log (Real.cosh x) - (Real.log (Real.cosh a) + (Real.log (Real.cosh b) - Real.log (Real.cosh a)) / (b^2 - a^2) * (x^2 - a^2))) c = 0 := by
            apply_rules [ exists_deriv_eq_zero ];
            · exact ContinuousOn.sub ( ContinuousOn.log ( Real.continuous_cosh.continuousOn ) fun x hx => ne_of_gt ( Real.cosh_pos x ) ) ( Continuous.continuousOn ( by continuity ) );
            · rw [ div_mul_cancel₀ ] <;> nlinarith;
          obtain ⟨ c, hc₁, hc₂ ⟩ := h_mvt; use c; norm_num [ Real.differentiableAt_cosh, ne_of_gt ( Real.cosh_pos _ ) ] at *;
          exact ⟨ hc₁, by rw [ div_eq_iff ( by linarith ) ] ; linarith ⟩;
        norm_num [ Real.differentiableAt_cosh, ne_of_gt ( Real.cosh_pos _ ) ] at *;
        exact h_mvt.imp fun x hx => ⟨ hx.1, by rw [ ← hx.2 ] ; ring ⟩;
      -- Since $\frac{\sinh c}{2c \cosh c} \leq \frac{\sinh a}{2a \cosh a}$ for $c > a$, we have $\frac{\log(\cosh b) - \log(\cosh a)}{b^2 - a^2} \leq \frac{\sinh a}{2a \cosh a}$.
      have h_ineq : (Real.sinh c) / (2 * c * Real.cosh c) ≤ (Real.sinh a) / (2 * a * Real.cosh a) := by
        have h_ineq : ∀ x y : ℝ, 0 < x → x < y → (Real.sinh y) / (y * Real.cosh y) ≤ (Real.sinh x) / (x * Real.cosh x) := by
          intros x y hx hy
          have h_deriv_neg : ∀ x : ℝ, 0 < x → deriv (fun x => Real.sinh x / (x * Real.cosh x)) x ≤ 0 := by
            intro x hx; norm_num [ Real.differentiableAt_sinh, Real.differentiableAt_cosh, ne_of_gt hx, ne_of_gt ( Real.cosh_pos x ) ];
            rw [ div_le_iff₀ ] <;> nlinarith [ Real.sinh_sq x, Real.sinh_pos_iff.mpr hx, Real.cosh_pos x, mul_pos hx ( Real.cosh_pos x ), le_sinh_mul_cosh hx.le ];
          have := exists_deriv_eq_slope ( f := fun x => Real.sinh x / ( x * Real.cosh x ) ) hy;
          contrapose! this;
          exact ⟨ continuousOn_of_forall_continuousAt fun z hz => DifferentiableAt.continuousAt <| by exact DifferentiableAt.div ( Real.differentiableAt_sinh ) ( DifferentiableAt.mul differentiableAt_id <| Real.differentiableAt_cosh ) <| ne_of_gt <| mul_pos ( by linarith [ hz.1 ] ) <| Real.cosh_pos _, fun z hz => DifferentiableAt.differentiableWithinAt <| by exact DifferentiableAt.div ( Real.differentiableAt_sinh ) ( DifferentiableAt.mul differentiableAt_id <| Real.differentiableAt_cosh ) <| ne_of_gt <| mul_pos ( by linarith [ hz.1 ] ) <| Real.cosh_pos _, fun z hz => by rw [ ne_eq, eq_div_iff ] <;> nlinarith [ h_deriv_neg z <| by linarith [ hz.1 ] ] ⟩;
        convert mul_le_mul_of_nonneg_right ( h_ineq a c ha hc.1.1 ) ( show 0 ≤ 1 / 2 by norm_num ) using 1 <;> ring;
      rw [ ← hb.2.2, ← hc.2 ] at *;
      rw [ div_le_iff₀ ] at h_ineq <;> ring_nf at * <;> nlinarith

/-
Kearns--Saul inequality for a random variable in `{-1, 1}` with mean `q`.

The expression on the left is the moment generating function of `X - q`, where
`P(X = 1) = (1 + q) / 2` and `P(X = -1) = (1 - q) / 2`.
-/
lemma kearns_saul_inequality
    {q u : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) :
    ((1 + q) / 2) * Real.exp (u * (1 - q)) +
        ((1 - q) / 2) * Real.exp (-u * (1 + q))
      ≤ Real.exp (ksCoefficient q * u ^ 2 / 2) := by
  by_cases hq : q = 0;
  · unfold ksCoefficient; norm_num [ hq ] ; ring_nf ;
    -- We'll use the exponential property to simplify the expression. Note that $e^{u^2 / 2} \geq \frac{e^u + e^{-u}}{2}$ for all $u$.
    have h_exp : ∀ u : ℝ, Real.exp (u^2 / 2) ≥ (Real.exp u + Real.exp (-u)) / 2 := by
      intro u; rw [ Real.exp_eq_exp_ℝ ] ; norm_num [ NormedSpace.exp_eq_tsum_div ] ; ring_nf; norm_num; (
      rw [ ← tsum_mul_right, ← tsum_mul_right, ← Summable.tsum_add ] ; rw [ ← tsum_even_add_odd ] ; norm_num [ pow_mul', mul_assoc, mul_comm, mul_left_comm, tsum_mul_left ] ; ring_nf ; norm_num;
      · refine' Summable.tsum_le_tsum _ _ _;
        · intro i; rw [ mul_assoc ] ; gcongr ; induction' i with i ih <;> norm_num [ Nat.factorial_succ, pow_succ' ] at * ; ring_nf at * ; nlinarith;
          field_simp;
          induction i <;> simp_all +decide [ Nat.factorial, pow_succ' ];
          norm_num [ Nat.succ_mul, Nat.factorial_succ ] at *;
          norm_num [ Nat.factorial_succ, Nat.mul_two ] at *;
          norm_num [ Nat.factorial_succ, add_assoc ] at *;
          norm_num [ Nat.add_comm, Nat.add_left_comm, Nat.factorial ] at *;
          nlinarith [ sq ( ( ↑‹ℕ› : ℝ ) : ℝ ), show ( 0 : ℝ ) ≤ ↑ ( ‹ℕ› + ‹ℕ› ).factorial * ( 2 ^ ‹ℕ› ) ⁻¹ by positivity ];
        · exact Real.summable_pow_div_factorial _ |> Summable.comp_injective <| by aesop_cat;
        · norm_num [ pow_mul' ];
          exact Summable.of_nonneg_of_le ( fun n => by positivity ) ( fun n => mul_le_of_le_one_right ( by positivity ) ( pow_le_one₀ ( by positivity ) ( by norm_num ) ) ) ( Real.summable_pow_div_factorial _ );
      · exact Summable.add ( Summable.mul_right _ <| Real.summable_pow_div_factorial _ |> Summable.comp_injective <| by intro m n h; simpa using h ) ( Summable.mul_right _ <| Summable.of_norm <| by simpa using Real.summable_pow_div_factorial _ |> Summable.comp_injective <| by intro m n h; simpa using h );
      · norm_num [ pow_add ];
      · exact Summable.mul_right _ <| Real.summable_pow_div_factorial _;
      · exact Summable.mul_right _ <| Summable.of_norm <| by simpa using Real.summable_pow_div_factorial |u|;);
    convert h_exp u |> le_trans <| le_of_eq _ using 1 <;> ring;
  · -- Let $a = \text{artanh}(q)$, so $a > 0$ and $\tanh(a) = q$.
    set a := Real.artanh q with ha
    have ha_pos : 0 < a := by
      simp +zetaDelta at *;
      grind +suggestions
    have h_tanh_a : Real.tanh a = q := by
      rw [ Real.tanh_eq_sinh_div_cosh, Real.sinh_artanh, Real.cosh_artanh ];
      · rw [ div_div, mul_one_div, div_eq_iff ] ; ring ; norm_num [ ne_of_gt ( Real.sqrt_pos.mpr ( show 0 < 1 - q ^ 2 by nlinarith ) ) ];
        exact div_ne_zero ( Real.sqrt_ne_zero'.mpr ( by nlinarith ) ) ( Real.sqrt_ne_zero'.mpr ( by nlinarith ) );
      · constructor <;> linarith;
      · constructor <;> linarith;
    -- Algebraically rewrite LHS as exp(-q*u) * (cosh (u+a) / cosh a).
    have h_lhs : (1 + q) / 2 * Real.exp (u * (1 - q)) + (1 - q) / 2 * Real.exp (-u * (1 + q)) = Real.exp (-q * u) * (Real.cosh (u + a) / Real.cosh a) := by
      rw [ Real.tanh_eq_sinh_div_cosh, div_eq_iff ] at h_tanh_a <;> norm_num [ Real.sinh_add, Real.cosh_add ] at *;
      · rw [ h_tanh_a, Real.cosh_eq, Real.sinh_eq ] ; ring;
        norm_num [ Real.exp_add, Real.exp_sub, ne_of_gt ( Real.cosh_pos _ ) ] ; ring;
        norm_num [ Real.exp_neg ];
      · exact ne_of_gt ( Real.cosh_pos _ );
    -- Apply the helper lemma `log_cosh_le_quadratic_tangent` with `x = u + a`.
    have h_helper : Real.log (Real.cosh (u + a)) - Real.log (Real.cosh a) ≤ (Real.tanh a / (2 * a)) * ((u + a) ^ 2 - a ^ 2) := by
      apply log_cosh_le_quadratic_tangent ha_pos;
    convert Real.exp_le_exp.mpr ( show -q * u + Real.log ( Real.cosh ( u + a ) ) - Real.log ( Real.cosh a ) ≤ ksCoefficient q * u ^ 2 / 2 from ?_ ) using 1;
    · rw [ h_lhs, Real.exp_sub, Real.exp_add, Real.exp_log ( Real.cosh_pos _ ), Real.exp_log ( Real.cosh_pos _ ) ];
      ring;
    · unfold ksCoefficient; ring_nf at *; simp_all +decide [ ne_of_gt ] ;
      convert h_helper using 1 ; ring_nf ; norm_num [ ha_pos.ne' ]

end GeneralizedLatala
end SpinGlass
