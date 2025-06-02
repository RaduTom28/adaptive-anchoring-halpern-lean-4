import AdaptiveAnchoringHalpernLean4.SamVariationIteration

local notation "⟪" x ", " y "⟫" => inner ℝ x y

class SamFramework (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] where
  x_0 : E
  T : E → E
  f : E → E
  a : ℕ → ℝ
  ρ : ℝ
  iter : ℕ → E
  hRhroBounds : ρ ≥ 0 ∧ ρ < 1
  hTNonExpansive : ∀ x y : E, ‖T x - T y‖ ≤ ‖x - y‖
  hTHasFixedPoint : ∃ x_star : E, T x_star = x_star
  hInitialNotFixed : T x_0 ≠ x_0
  hFRhoContraction : ∀ x y : E , ‖f x - f y‖ ≤ ρ * ‖x - y‖
  hSequenceBounds : ∀ n : ℕ , a n ≥ 0 ∧ a n ≤ 1
  hIterDefinition : ∀ n : ℕ , iter (n+1) = (1 - a n) • f (iter n) + a n • T (iter n)

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

theorem sequence_bounds {I : SamIteration H} :
  ∀ (n : ℕ), phi I (n + 1) / (phi I (n + 1) + 1) ≥ 0 ∧ phi I (n + 1) / (phi I (n + 1) + 1) ≤ 1 := by
    intros n
    have h1 := And.left (first_bounds I n)
    have h2 : phi I (n + 1) > 0 := by linarith
    have h3 : phi I (n + 1) + 1 > 0 := by linarith
    constructor
    case left =>
      refine div_nonneg ?_ ?_
      exact le_of_lt h2
      exact le_of_lt h3
    case right =>
      refine (div_le_one₀ h3).mpr ?_
      linarith

theorem iteration_definition {I : SamIteration H} :
  ∀ (n : ℕ),
    x I (n + 1) =
      (1 - phi I (n + 1) / (phi I (n + 1) + 1)) • I.f (x I n) + (phi I (n + 1) / (phi I (n + 1) + 1)) • I.T (x I n) := by
        intros n
        have h := recurrence_subst_phi I n
        have h1 := And.left (first_bounds I n)
        have h2 : phi I (n + 1) > 0 := by linarith
        have h3 : phi I (n + 1) + 1 > 0 := by linarith
        have aux1 : 1 - phi I (n + 1) / (phi I (n + 1) + 1) = 1 / (phi I (n + 1) + 1) := by
          calc
            1 - phi I (n + 1) / (phi I (n + 1) + 1) =  (phi I (n + 1) + 1)/(phi I (n + 1) + 1) - phi I (n + 1) / (phi I (n + 1) + 1) := by
              refine sub_left_inj.mpr ?_
              field_simp
            _ = (phi I (n + 1) + 1 - phi I (n + 1)) / (phi I (n + 1) + 1) := by
              exact div_sub_div_same (phi I (n + 1) + 1) (phi I (n + 1)) (phi I (n + 1) + 1)
            _ = 1 / (phi I (n + 1) + 1) := by
              field_simp
        rw [aux1]
        assumption


noncomputable
instance SamAdaptiveFrameworkFitted {I : SamIteration H} : SamFramework H where
  x_0 := I.x_0
  T := I.T
  f := I.f
  a (n : ℕ) := phi I (n+1)/(phi I (n+1) + 1)
  ρ := I.ρ
  iter (n : ℕ) := x I n
  hRhroBounds := I.hRhroBounds
  hTNonExpansive := I.hTNonExpansive
  hTHasFixedPoint := I.hTHasFixedPoint
  hInitialNotFixed := I.hInitialNotFixed
  hFRhoContraction := I.hFRhoContraction
  hSequenceBounds := sequence_bounds
  hIterDefinition := iteration_definition
