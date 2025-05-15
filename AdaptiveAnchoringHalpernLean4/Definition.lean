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

axiom fixed_point_not_encountered_in_sequence (I : Iteration H) (n : ℕ) : x I (n + 1) ≠ I.T (x I (n + 1))

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


omit [CompleteSpace H] in
theorem essential_1 (x y : H) : ‖x + y‖^2 = ‖x‖^2 + ‖y‖^2 + 2 * ⟪x,y⟫ := by
  rw [@norm_add_sq_real]
  rw [add_right_comm]


omit [InnerProductSpace ℝ H] [CompleteSpace H] in
theorem comm_operation (x y z : H) : x + x - y - z = (x - y) + (x - z) := by
  rw [@sub_add_sub_comm]
  rw [@sub_sub]

theorem square_nonexpansive (I : Iteration H) (x y : H) : ‖I.T x - I.T y‖^2 ≤ ‖x - y‖^2 := by
  have h1 := I.hTNonExpansive x y
  mono
  simp

-- add comparison util

omit [CompleteSpace H] in
theorem inner_factor_minus (x y0 y1 : H) : ⟪ x, y0 - y1 ⟫ = - ⟪ x , y1 - y0 ⟫ := by
  rw [inner_sub_right]
  rw [inner_sub_right]
  rw [real_inner_comm]
  simp


theorem comparison_util {a b c : ℝ} (h : a + b ≤ b + c) : a ≤ c := by
  linarith

omit [InnerProductSpace ℝ H] [CompleteSpace H] in
theorem norm_factor_minus {x y : H} : ‖x-y‖ = ‖y-x‖ := by
  rw [@norm_sub_rev]

theorem applied_norm_factor_minus (I : Iteration H) : ‖x I 1 - I.x_0‖ ^ 2 =  ‖I.x_0 - x I 1‖ ^ 2:= by
  rw [@norm_sub_rev]

theorem aux_simp_1 (a b c: ℝ) (h : a > 0)  : a * (c/a * b) = c * b := by field_simp

theorem aux_simp_2 (a b : ℝ) (h : a ≠ 0): a⁻¹ * (a * b) = b := by field_simp

omit [InnerProductSpace ℝ H] [CompleteSpace H] in
theorem aux_simp_3 {a b : H} (h : a ≠ b) : ‖a - b‖ ^ 2 ≠ 0 := by
  refine pow_ne_zero 2 ?_
  refine norm_ne_zero_iff.mpr ?_
  exact sub_ne_zero_of_ne h

theorem aux_simp_4 (I : Iteration H) (n : ℕ) : phi I (n + 1) ≥ n + 1 → phi I (n + 1) > 0:= by
  intros h
  linarith

omit [InnerProductSpace ℝ H] [CompleteSpace H] in
theorem aux_simp_5 {a b c : H} :  a + b = c → b = c - a := by
  intros h
  exact eq_sub_of_add_eq' h

omit [CompleteSpace H] in
theorem aux_simp_6 {a b : H} {r : ℝ} (h : r ≠ 0) : r • a = b → a = r⁻¹ • b := by
  intros h1
  rw [← h1]
  exact Eq.symm (inv_smul_smul₀ h a)

theorem aux_simp_7 {a : ℝ} : a > 0 → a + 1 > 0 := by
  intros h
  linarith

theorem aux_simp_8 {a b : ℝ} : a > 0 → b > 0 → a/b > 0 := by
  intros h1 h2
  exact div_pos h1 h2

theorem aux_simp_9 {a b : ℝ} (h : b ≠ 0 ∧ a ≠ 0) : a/b ≠ 0 → b/a ≠ 0 := by
  intro h1
  exact div_ne_zero_iff.mpr h

omit [CompleteSpace H] in
theorem aux_simp_10 {b c d : H} {r : ℝ} : d = r • (b - c) → d = (r • b - r • c) := by
  intro h
  rw [h]
  exact smul_sub r b c

omit [CompleteSpace H] in
theorem aux_simp_11 {a b : ℝ} {x : H} (h1 : a ≠ 0): ((a/b) • 1/a) • x  = b⁻¹ • x := by
  field_simp
  rw [div_mul_cancel_right₀ h1 b]
  field_simp

theorem aux_simp_12 {I : Iteration H} {n : Nat} : (phi I (n + 1) + 1) / phi I (n + 1) = (phi I (n+1) + 1) • (phi I (n + 1)) ⁻¹ := by
  exact rfl

theorem aux_simp_13 {I : Iteration H} {n : Nat} : (1 / (phi I (n + 1) + 1)) =  (phi I (n + 1) + 1) ⁻¹ := by
  exact one_div (phi I (n + 1) + 1)


omit [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H] in
theorem trivial1 { a : ℝ } (h1 : a ≠ 0) : a • a⁻¹ = 1 := by
  field_simp

 omit [CompleteSpace H] in
theorem aux_simp_14 { a b : ℝ } {c : H} (h1 : a ≠ 0) : (a • b⁻¹) • a⁻¹ • c = b⁻¹ • c := by
  have aux1 : (a • b⁻¹) • a⁻¹ • c = a • b⁻¹ • a⁻¹ • c := by
    exact IsScalarTower.smul_assoc a b⁻¹ (a⁻¹ • c)
  rw [aux1]
  have aux2 : a • b⁻¹ • a⁻¹ • c = b⁻¹ • a • a⁻¹ • c := by rw [@smul_algebra_smul_comm]
  have aux3 : b⁻¹ • a • a⁻¹ • c =  b⁻¹ • (a • a⁻¹) • c := by rw [@smul_assoc]
  rw [trivial1] at aux3
  have aux4 : b⁻¹ • a • a⁻¹ • c = a • b⁻¹ • a⁻¹ • c := by
    exact id (Eq.symm aux2)
  rw [←aux4]
  have aux5 : b⁻¹ • (1:ℝ) • c = b⁻¹ • c := by rw [one_smul]
  exact Eq.trans aux3 aux5
  assumption


theorem aux_simp_15 {I : Iteration H} {n : Nat} (h : phi I (n + 1) + 1 ≠  0) : ((phi I (n + 1) + 1) • (phi I (n + 1))⁻¹) • (phi I (n + 1) + 1)⁻¹ • I.x_0 = (phi I (n + 1))⁻¹ • I.x_0 := by
  refine aux_simp_14 ?_
  assumption


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
      rw [inner_factor_minus] at hNormSqConsecTermDiffExpanded
      simp at hNormSqConsecTermDiffExpanded
      rw [hNormSqConsecTermDiffExpanded] at hConsecSquareNonexpansive
      norm_num at hConsecSquareNonexpansive
      rw [applied_norm_factor_minus] at hConsecSquareNonexpansive
      exact comparison_util hConsecSquareNonexpansive
  case succ n exp =>
    have hPhiIndStep := And.left exp
    have hBoundIndStep := And.right exp
    constructor
    case left =>
      -- strategy  -> write lemma that has bound induction step as input that proves connection for next phi
      have hPhiIndStepPos : phi I (n+1) ≥ 0 := by linarith
      have hMainTerm := mul_le_mul_of_nonneg_left hBoundIndStep hPhiIndStepPos
      norm_num at hMainTerm
      rw [aux_simp_1] at hMainTerm
      have hAppliedComm : phi I (n + 1) * ‖x I (n + 1) - I.T (x I (n + 1))‖ ^ 2 = ‖x I (n + 1) - I.T (x I (n + 1))‖ ^ 2 * phi I (n + 1):= by
        exact
          Eq.symm
            (Lean.Grind.CommRing.mul_comm (‖x I (n + 1) - I.T (x I (n + 1))‖ ^ 2) (phi I (n + 1)))
      rw [hAppliedComm] at hMainTerm
      have hInvNormDiffPos : 1/(‖x I (n + 1) - I.T (x I (n + 1))‖ ^ 2) > 0 := by
        have hAxiomCondition := fixed_point_not_encountered_in_sequence I n
        field_simp
        apply pow_pos
        rw [norm_pos_iff]
        exact sub_ne_zero_of_ne hAxiomCondition
      have hInvNormDiffPosOrZero : 1/(‖x I (n + 1) - I.T (x I (n + 1))‖ ^ 2) ≥  0 := by linarith
      have hMainTerm := mul_le_mul_of_nonneg_left hMainTerm hInvNormDiffPosOrZero
      norm_num at hMainTerm
      rw [aux_simp_2] at hMainTerm
      have transitionToNextPhi : (‖x I (n + 1) - I.T (x I (n + 1))‖ ^ 2)⁻¹ * (2 * ⟪x I (n + 1) - I.T (x I (n + 1)), I.x_0 - x I (n + 1)⟫) = phi I (n+2) - 1 := by
        unfold phi
        norm_num
        field_simp
      rw [transitionToNextPhi] at hMainTerm
      have hMainTerm := le_trans hPhiIndStep hMainTerm
      simp
      linarith
      have hAxiom := fixed_point_not_encountered_in_sequence I n
      exact aux_simp_3 hAxiom
      case h =>
        exact aux_simp_4 I n hPhiIndStep
    case right =>
      have hPhiIndStepIsPos := aux_simp_4 I n hPhiIndStep
      have hPhiIndStepNeqZero : phi I (n + 1) ≠  0 := by exact Ne.symm (ne_of_lt hPhiIndStepIsPos)
      have hPhiIndStepPlusOneIsPos : phi I (n + 1) + 1 > 0 := by exact aux_simp_7 hPhiIndStepIsPos
      have hPhiIndStepPlusOneIsNeqZero : phi I (n + 1) + 1 ≠  0 := by exact Ne.symm (ne_of_lt hPhiIndStepPlusOneIsPos)
      have hRecurrenceRewritten : I.T (x I n) = x I (n+1) + (phi I (n+1)) ⁻¹ • (x I (n+1) - I.x_0) := by
        have hRegularIterationDefinition := Eq.symm (recurrence_subst_phi I n)
        have hRegularIterationDefinition := aux_simp_5 hRegularIterationDefinition
        have hPhiRapNeqZero : (phi I (n + 1) / (phi I (n + 1) + 1)) ≠ 0 := by
          have aux1 := aux_simp_4 I n hPhiIndStep
          have aux2 := aux_simp_7 aux1
          have aux3 := aux_simp_8 aux1 aux2
          linarith
        have hPhiRapNeqZeroInv : ( (phi I (n + 1) + 1)/phi I (n + 1) ) ≠ 0 := by
          have aux1 := aux_simp_4 I n hPhiIndStep
          have aux2 := aux_simp_7 aux1
          have aux3 := aux_simp_8 aux2 aux1
          linarith
        have hRegularIterationDefinition := aux_simp_6 hPhiRapNeqZero hRegularIterationDefinition
        field_simp at hRegularIterationDefinition
        have hRegularIterationDefinition : I.T (x I n) = (phi I (n+1))⁻¹ • (phi I (n+1) +1) • x I (n + 1) - (phi I (n+1))⁻¹ • I.x_0 := by
          norm_num at hRegularIterationDefinition
          have aux1 := aux_simp_10 hRegularIterationDefinition
          norm_num at aux1
          field_simp at aux1
          rw [aux_simp_12] at aux1
          rw [aux_simp_13] at aux1
          rw [aux_simp_15] at aux1
          have aux1 : I.T (x I n) = (phi I (n + 1) + 1) • (phi I (n + 1))⁻¹ • x I (n + 1) - (phi I (n + 1))⁻¹ • I.x_0 := by
            sorry



          --have aux2 : ((phi I (n + 1) + 1) / phi I (n + 1)) • (phi I (n + 1) + 1)⁻¹ •  x I (n + 1) = (phi I (n+1))⁻¹ •  x I (n + 1) := by








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
