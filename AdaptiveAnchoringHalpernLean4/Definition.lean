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


@[simp]
lemma base_case_recurrence (I : Iteration H) : x I 0 = I.x_0 := by
  unfold x
  simp

@[simp]
lemma first_recurrence_term (I : Iteration H) : x I 1 = (2:ℝ)⁻¹ • I.x_0 + (2:ℝ)⁻¹ • I.T I.x_0 := by
  unfold x
  simp
  norm_num

@[simp]
lemma recurrence_subst_phi (I : Iteration H) (n : Nat) : x I (n+1) = (1 / (phi I (n+1) + 1)) •  I.x_0 + (phi I (n+1)  / (phi I (n+1)  + 1)) •  I.T (x I n) := by
  simp
  unfold phi
  norm_num
  rw [x]
  simp

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


lemma first_bounds (I : Iteration H) (n : ℕ) : (phi I (n+1) ≥ n+1) ∧ (‖(x I (n+1)) - I.T (x I (n+1))‖^2 ≤ 2/(phi I (n+1)) • ⟪ (x I (n+1)) - I.T (x I (n+1)) , I.x_0 - x I (n+1)⟫) := by
  induction n
  case zero =>
    constructor
    case left =>
      simp
      unfold phi
      simp
    case right =>
    have hRecFirstStep : I.T I.x_0 = (2:ℝ) • x I 1 - I.x_0 := by
      rw [first_recurrence_term]
      simp
    have hNormSqConsecTermDiffExpanded : ‖ I.T (x I 1) ‖ ^ 2 = ‖x I 1 - I.T x I 1‖^2 + ‖ x I 1 - I.x_0 ‖^2 := by sorry
  case succ n exp =>
    constructor
    case left =>
      sorry
    case right =>
      sorry
