import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Tactic.Linarith

local notation "⟪" x ", " y "⟫" => inner ℝ x y

structure SamIteration (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] where
  x_0 : E
  T : E → E
  f : E → E
  ρ : ℝ
  hRhroBounds : ρ ≥ 0 ∧ ρ < 1
  hTNonExpansive : ∀ x y : E, ‖T x - T y‖ ≤ ‖x - y‖
  hTHasFixedPoint : ∃ x_star : E, T x_star = x_star
  hInitialNotFixed : T x_0 ≠ x_0
  hFRhoContraction : ∀ x y : E , ‖f x - f y‖ ≤ ρ * ‖x - y‖


variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

noncomputable def x (I : SamIteration H) (n : Nat) : H :=
match n with
  | 0     => I.x_0
  | (n+1) =>
      let ϕ := 2 * ⟪x I n - I.T (x I n), I.f (x I n)  - x I n⟫ / (‖x I n - I.T (x I n)‖ ^ 2) + 1
      (1 / (ϕ + 1)) • I.f (x I n) + (ϕ / (ϕ + 1)) • I.T (x I n)

noncomputable def phi (I : SamIteration H)(n : Nat) : ℝ := 2 * ⟪x I (n-1) - I.T (x I (n-1)), I.f (x I (n-1)) - x I (n-1)⟫ / (‖x I (n-1) - I.T (x I (n-1))‖ ^ 2) + 1

axiom fixed_point_not_encountered_in_sequence (I : SamIteration H) (n : ℕ) : x I (n) ≠ I.T (x I (n))

-- additional conditions :
axiom first_term_is_contraction_fixed (I : SamIteration H) : I.f I.x_0 = I.x_0

theorem xn_rewritten_subst_phi (I : SamIteration H) (n : Nat) : x I (n+1) = (1 / (phi I (n+1) + 1)) •  I.f (x I n) + (phi I (n+1)  / (phi I (n+1)  + 1)) •  I.T (x I n) := by
  simp
  unfold phi
  norm_num
  rw [x]
  simp

lemma base_case_recurrence (I : SamIteration H) : x I 0 = I.x_0 := by
  unfold x
  simp

lemma first_phi (I : SamIteration H) : phi I 1 = 1 := by
  unfold phi
  simp
  rw [base_case_recurrence]
  rw [first_term_is_contraction_fixed]
  simp


lemma first_bounds (I : SamIteration H) (n : ℕ) : (phi I (n+1) ≥ n+1) ∧ (‖(x I (n+1)) - I.T (x I (n+1))‖^2 ≤ (2/(phi I (n+1))) • ⟪ (x I (n+1)) - I.T (x I (n+1)) , I.f (x I (n+1)) - x I (n+1)⟫) := by
  induction n
  case zero =>
    constructor
    case left =>
      norm_num
      rw [first_phi]
    case right =>
      norm_num
      -- introduce new constraint - isolate as separate proof to choose what to add
  case succ =>
    sorry
