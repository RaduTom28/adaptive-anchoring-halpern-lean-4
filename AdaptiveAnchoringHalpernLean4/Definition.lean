import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Tactic.Linarith

local notation "⟪" x ", " y "⟫" => inner ℝ x y

structure Iteration (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] where
  x_0 : E
  T : E → E
  hTNonExpansive : ∀ x y : E, ‖T x - T y‖ ≤ ‖x - y‖
  hTHasFixedPoint : ∃ x_star : E, T x_star = x_star
  hInitialNotFixed : T x_0 ≠ x_0


variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

noncomputable def x (I : Iteration H) (n : Nat) : H :=
match n with
  | 0     => I.x_0
  | (n+1) =>
      let ϕ := 2 * ⟪x I n - I.T (x I n), I.x_0 - x I n⟫ / (‖x I n - I.T (x I n)‖ ^ 2) + 1
      (1 / (ϕ + 1)) • I.x_0 + (ϕ / (ϕ + 1)) • I.T (x I n)



noncomputable def phi (I : Iteration H)(n : Nat) : ℝ := 2 * ⟪x I (n-1) - I.T (x I (n-1)), I.x_0 - x I (n-1)⟫ / (‖x I (n-1) - I.T (x I (n-1))‖ ^ 2) + 1



lemma base_case_recurrence (I : Iteration H) : x I 0 = I.x_0 := by
  unfold x
  simp


lemma first_recurrence_term (I : Iteration H) : x I 1 = (2:ℝ)⁻¹ • I.x_0 + (2:ℝ)⁻¹ • I.T I.x_0 := by
  unfold x
  simp
  norm_num
  rw [base_case_recurrence]
  norm_num

lemma first_phi (I : Iteration H) : phi I 1 = 1 := by
  unfold phi
  simp
  rw [base_case_recurrence]
  simp

lemma recurrence_subst_phi (I : Iteration H) (n : Nat) : x I (n+1) = (1 / (phi I (n+1) + 1)) •  I.x_0 + (phi I (n+1)  / (phi I (n+1)  + 1)) •  I.T (x I n) := by
  simp
  unfold phi
  norm_num
  rw [x]
  simp

omit [CompleteSpace H] in
lemma split_prod (x : H) : (2:ℝ) • x = x + x := by
  exact two_smul ℝ x

-- noted
theorem essential_1 (x y : H) : ‖x + y‖^2 = ‖x‖^2 + ‖y‖^2 + 2 * ⟪x,y⟫ := by
  rw [@norm_add_sq_real]
  rw [add_right_comm]

-- @[simp]
-- lemma aux_simp (f : ℝ) : (f + 1) / f = (f + 1) • f⁻¹ := by
--   simp
--   exact rfl

-- @[simp]
-- lemma aux_simp_2 (f : ℝ) : f / (f + 1) = f  • (f+1)⁻¹ := by
--   simp
--   exact rfl

-- @[simp]
-- lemma aux_simp_3 (f : ℝ) (h1 : f+1 ≠ 0) : (f + 1) • (f + 1)⁻¹ = 1 := by
--   field_simp

-- @[simp]
-- lemma aux_simp_4 (f r: ℝ) (h1 : f+1 ≠ 0) : ((f + 1) * r) • (f + 1)⁻¹ = r := by
--   simp
--   field_simp

-- @[simp]
-- lemma aux_simp_5 (f: ℝ) (h1 : f+1 ≠ 0): ((f + 1) * f⁻¹) • (f + 1)⁻¹ =  f⁻¹ := by
--   simp only [smul_eq_mul]
--   rw [propext (mul_inv_eq_iff_eq_mul₀ h1)]
--   ring

-- @[simp]
-- lemma aux_simp_6 (r : H) (f : ℝ) (h1 : f+1 ≠ 0): ((f + 1) * f⁻¹) • (f + 1)⁻¹ • r =  f⁻¹ • r := by




-- @[simp]
-- lemma aux_transformation_first (f : ℝ) (r s t : H) (hFGreaterThanZero: (f > 0)): (1/(f+1)) • r + (f/(f+1)) • s = t  → s = ((f+1)/f) • t - (1/f) • r := by
--   intros h
--   subst t
--   have hFNeqZero : f ≠ 0 := by exact ne_of_gt hFGreaterThanZero
--   have hFPlusOneNeqZero : f+1 ≠ 0 := by
--     apply ne_of_gt
--     linarith
--   simp



-- @[simp]
-- lemma recurrence_rewritten (I : Iteration H) (n : Nat) : I.T (x I n) = x I (n+1) + (1/(phi I (n+1))) • (x I (n+1) - I.x_0) := by
--   have recurrence := recurrence_subst_phi I n
--   refine Eq.symm (add_eq_of_eq_sub ?_)
--   rw [recurrence]
--   refine add_eq_of_eq_sub ?_



-- theorem diff_first_two_terms (I : Iteration H) : ‖ I.T (I.x_0) - I.T (x I 1)‖ ^ 2 = ‖x I 1 - I.T (x I 1)‖^2 + ‖x I 1 - I.x_0‖^2 + 2 * ⟪ x I 1 - I.T (x I 1), x I 1 - I.x_0 ⟫ := by
-- sorry

omit [InnerProductSpace ℝ H] [CompleteSpace H] in
theorem comm_operation (x y z : H) : x + x - y - z = (x - y) + (x - z) := by
  rw [@sub_add_sub_comm]
  rw [@sub_sub]

theorem square_nonexpansive (I : Iteration H) (x y : H) : ‖I.T x - I.T y‖^2 ≤ ‖x - y‖^2 := by
  have h1 := I.hTNonExpansive x y
  mono
  simp

-- add comparison util
-- use theorem for minus change inside inner in new have


omit [CompleteSpace H] in
theorem inner_factor_minus (x y0 y1 : H) : ⟪ x, y0 - y1 ⟫ = - ⟪ x , y1 - y0 ⟫ := by
  rw [inner_sub_right]
  rw [inner_sub_right]
  rw [real_inner_comm]
  simp

lemma first_bounds (I : Iteration H) (n : ℕ) : (phi I (n+1) ≥ n+1) ∧ (‖(x I (n+1)) - I.T (x I (n+1))‖^2 ≤ (2/(phi I (n+1))) • ⟪ (x I (n+1)) - I.T (x I (n+1)) , I.x_0 - x I (n+1)⟫) := by
  induction n
  case zero =>
    constructor
    case left =>
      unfold phi
      simp
      rw [base_case_recurrence]
      simp
    case right =>
      have hRecFirstStep : I.T I.x_0 = (2:ℝ) • x I 1 - I.x_0 := by
        rw [first_recurrence_term]
        simp
      have hNormSqConsecTermDiffExpanded: ‖ I.T (I.x_0) - I.T (x I 1)‖ ^ 2 = ‖x I 1 - I.T (x I 1)‖^2 + ‖x I 1 - I.x_0‖^2 + 2 * ⟪ x I 1 - I.T (x I 1), x I 1 - I.x_0 ⟫ := by
        rw [hRecFirstStep]
        rw [split_prod]
        rw [comm_operation]
        rw [norm_add_sq_real]
        rw [add_right_comm]
        rw [real_inner_comm]
        simp
        rw [add_comm]
      have hConsecSquareNonexpansive := square_nonexpansive I I.x_0 (x I 1)

      simp
      rw [first_phi]
      simp




  case succ n exp =>
    constructor
    case left =>
      sorry
    case right =>
      sorry
