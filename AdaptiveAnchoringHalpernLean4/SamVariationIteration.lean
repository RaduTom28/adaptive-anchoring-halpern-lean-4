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

axiom inner_contraction_diff_condition (I : SamIteration H) (n : ℕ) : ⟪ x I (n+1) - I.T (x I (n+1)) , I.f (x I (n+1)) - I.f (x I n) ⟫ ≥ 0

theorem recurrence_subst_phi (I : SamIteration H) (n : Nat) : x I (n+1) = (1 / (phi I (n+1) + 1)) •  I.f (x I n) + (phi I (n+1)  / (phi I (n+1)  + 1)) •  I.T (x I n) := by
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

lemma first_term (I :SamIteration H) : x I 1 = (2:ℝ)⁻¹ • I.x_0 + (2:ℝ)⁻¹ • I.T I.x_0 := by
  field_simp
  rw [recurrence_subst_phi]
  norm_num
  rw [first_phi]
  norm_num
  rw [base_case_recurrence]
  rw [first_term_is_contraction_fixed]


omit [CompleteSpace H] in
lemma split_prod (x : H) : (2:ℝ) • x = x + x := by
  exact two_smul ℝ x

omit [CompleteSpace H] in
theorem essential_1 {x y : H} : ‖x + y‖^2 = ‖x‖^2 + ‖y‖^2 + 2 * ⟪x,y⟫ := by
  rw [@norm_add_sq_real]
  rw [add_right_comm]

omit [CompleteSpace H] in
theorem essential_1' {x y : H} : ‖x - y‖^2 = ‖x‖^2 + ‖y‖^2 - 2 * ⟪x,y⟫ := by
  rw [@norm_sub_sq_real]
  rw [@sub_add_eq_add_sub]

omit [InnerProductSpace ℝ H] [CompleteSpace H] in
theorem comm_operation (x y z : H) : x + x - y - z = (x - y) + (x - z) := by
  rw [@sub_add_sub_comm]
  rw [@sub_sub]

theorem square_nonexpansive (I : SamIteration H) (x y : H) : ‖I.T x - I.T y‖^2 ≤ ‖x - y‖^2 := by
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

omit [CompleteSpace H] in
theorem inner_factor {x y : H } {a : ℝ} : ⟪x, a • y⟫ = a • ⟪x , y⟫ :=
  by rw [@inner_smul_right_eq_smul]


theorem comparison_util {a b c : ℝ} (h : a + b ≤ b + c) : a ≤ c := by
  linarith

omit [InnerProductSpace ℝ H] [CompleteSpace H] in
theorem norm_factor_minus {x y : H} : ‖x-y‖ = ‖y-x‖ := by
  rw [@norm_sub_rev]

theorem applied_norm_factor_minus (I : SamIteration H) : ‖x I 1 - I.x_0‖ ^ 2 =  ‖I.x_0 - x I 1‖ ^ 2:= by
  rw [@norm_sub_rev]

theorem aux_simp_1 (a b c: ℝ) (h : a > 0)  : a * (c/a * b) = c * b := by field_simp

theorem aux_simp_2 (a b : ℝ) (h : a ≠ 0): a⁻¹ * (a * b) = b := by field_simp

omit [InnerProductSpace ℝ H] [CompleteSpace H] in
theorem aux_simp_3 {a b : H} (h : a ≠ b) : ‖a - b‖ ^ 2 ≠ 0 := by
  refine pow_ne_zero 2 ?_
  refine norm_ne_zero_iff.mpr ?_
  exact sub_ne_zero_of_ne h

theorem aux_simp_4 (I : SamIteration H) (n : ℕ) : phi I (n + 1) ≥ n + 1 → phi I (n + 1) > 0:= by
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

theorem aux_simp_12 {I : SamIteration H} {n : Nat} : (phi I (n + 1) + 1) / phi I (n + 1) = (phi I (n+1) + 1) • (phi I (n + 1)) ⁻¹ := by
  exact rfl

theorem aux_simp_13 {I : SamIteration H} {n : Nat} : (1 / (phi I (n + 1) + 1)) =  (phi I (n + 1) + 1) ⁻¹ := by
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


theorem aux_simp_15 {I : SamIteration H} {n : Nat} (h : phi I (n + 1) + 1 ≠  0) : ((phi I (n + 1) + 1) • (phi I (n + 1))⁻¹) • (phi I (n + 1) + 1)⁻¹ • I.f (x I n) = (phi I (n + 1))⁻¹ • I.f (x I n) := by
  refine aux_simp_14 ?_
  assumption

omit [CompleteSpace H] in
theorem aux_simp_16 {a b : ℝ} {x : H} : (a • b⁻¹) • x = b⁻¹ • a • x := by
  rw [@smul_assoc]
  rw [@smul_algebra_smul_comm]

omit [CompleteSpace H] in
theorem factor {a b : ℝ} {x : H} : (a + b) • x = a • x + b • x := by
  rw [@add_smul]

omit [CompleteSpace H] in
theorem factor_diff {a b : ℝ} {x : H} : (a - b) • x = a • x - b • x := by
  rw [@sub_smul]

omit [CompleteSpace H] in
theorem factor' {a : ℝ} {x y : H} : a • (x - y) = a • x - a • y := by
  rw [@smul_sub]

omit [CompleteSpace H] in
theorem aux_simp_17 {a : ℝ} {x y z : H} (h1 : a ≠ 0) : z = a⁻¹ • (a + (1:ℝ)) • x - a⁻¹ • y → z =  x + a⁻¹ • (x - y) := by
  intros h3
  have aux1 : a⁻¹ • (a+ 1:ℝ ) • x= ((1:ℝ) + a⁻¹) • x := by
    rw [propext (inv_smul_eq_iff₀ h1)]
    have aux1' : a • (1 + a⁻¹) • x = (a * (1 + a⁻¹)) • x  := by rw [@smul_smul]
    rw [aux1']
    have aux1'' : (a * (1 + a⁻¹)) = (a + 1) := by
      refine CancelDenoms.add_subst ?_ ?_
      rw [propext (mul_eq_left₀ h1)]
      rw [propext (mul_inv_eq_one₀ h1)]
    rw [aux1'']
  rw [aux1] at h3
  have aux2 : (1 + a⁻¹) • x = x + a⁻¹ • x := by
    field_simp
    rw [@add_div]
    have aux2' : a / a = (1:ℝ) := by rw [propext (div_eq_one_iff_eq h1)]
    rw [aux2']
    rw [factor]
    simp
  rw [aux2] at h3
  have aux3 : a⁻¹ • x - a⁻¹ • y  = a⁻¹ • (x - y) := by
    rw [@factor']
  have aux4 : z = x + (a⁻¹ • x - a⁻¹ • y) := by
    rw [h3]
    abel
  rw [← factor'] at aux4
  assumption


theorem aux_simp_18 {a b : ℝ}: a = b → a^2=b^2 := by
  exact fun a_1 ↦ congrFun (congrArg HPow.hPow a_1) 2

omit [CompleteSpace H] in
theorem factor_norm {a : ℝ} {x : H} : (‖a • x‖) = (|a| • ‖x‖) := by
  simp
  rw [norm_smul]
  simp

theorem aux_simp_19 {a b : ℝ} : (a⁻¹ * b)^2 = 1/(a^2) * b^2 := by
  field_simp

omit [CompleteSpace H] in
theorem aux_simp_20 {a : ℝ} {x y : H} : ⟪x , a • y⟫ = a * ⟪x, y⟫ :=
  by exact real_inner_smul_right x y a


theorem aux_simp_21 {a b : ℝ} (h1 : a ≥ 0) (h2 : b ≥ 0): a ≥ b → a^2 ≥ b^2 := by
  intros h
  exact (sq_le_sq₀ h2 h1).mpr h

theorem aux_simp_22 {a : ℝ} (h1 : a+1 ≠ 0) : a/(a+1) = 1 - 1/(a+1) := by
  rw [one_sub_div h1]
  simp

omit [CompleteSpace H] in
theorem aux_simp_24 {x y z : H} {a : ℝ} : x - (a • y + (z - a • z)) = (x - z) - a • (y - z) := by
  have aux0 : x - (a • y + (z - a • z)) =  x - (a • y + z - a • z) :=  by abel
  rw [aux0]
  have aux1 : x - (a • y + z - a • z) = x - a • y - z + a • z := by
    abel
  rw [aux1]
  have aux2 : x - a • y - z + a • z =  x - z + a • z - a • y := by abel
  rw [aux2]
  have aux3 : x - z + a • z - a • y = x - z + a • (z - y) := by
    rw [factor']
    abel
  rw [aux3]
  have aux4 : (a • (z - y)) = - (a • (y - z)) := by
    rw [@factor']
    rw [@factor']
    simp
  rw [aux4]
  abel

omit [InnerProductSpace ℝ H] [CompleteSpace H] in
theorem aux_simp_25 {x : H} {a : ℝ} : (|a| • ‖x‖) ^ 2 = a^2 * ‖x‖^2 := by
  simp
  rw [@sq]
  ring_nf
  simp
  rw [aux_simp_18 rfl]
  ring

theorem aux_simp_26 {a b c: ℝ} : a * (1/b) • c = a/b * c := by
  field_simp

omit [CompleteSpace H] in
theorem aux_simp_27 {x : H} {a : ℝ} : - x - a • x = (-1 - a) • x := by
  rw [@factor_diff]
  field_simp

omit [CompleteSpace H] in
theorem aux_simp_28 {x y : H} {a : ℝ} (h : a ≠ 0): x - (y + a⁻¹ • (y-x)) = - ((a+1)/a) • (y-x) := by
  field_simp
  have auxlocal1 : x - (y + (1 / a) • (y - x)) = x - y - (1/a) • (y-x) := by
    rw [@sub_add_eq_sub_sub]
  rw [auxlocal1]
  have auxlocal2 : x - y = - (y - x) := by
    rw [@neg_sub]
  rw [auxlocal2]
  have auxlocal3 : ((-1 + -a) / a) = - (a + 1)/a := by
    rw [@neg_add_rev]
  rw [auxlocal3]
  have auxlocal4 : -(y - x) - (1 / a) • (y - x) = (-1 - 1/a) • (y-x) := by
    rw[aux_simp_27]
  rw [auxlocal4]
  have auxlocal5 : (-1 - 1 / a) = (-(a + 1) / a) := by
    rw [← auxlocal3]
    refine Eq.symm (aux_simp_5 ?_)
    field_simp
  rw [auxlocal5]

theorem aux_simp_29 {a : ℝ} (h1 : a ≠ 0) (h2 : a+1 ≠ 0): 2 / (a + 1) * -((a + 1) / a) = -2 / a := by
  field_simp
  ring

theorem aux_simp_30 {a b : ℝ} : a = a + b → b = 0 := by
  intros h
  field_simp at h
  assumption

omit [CompleteSpace H] in
theorem aux_simp_31 {x y z : H} {a : ℝ} : a * ⟪x , z⟫ - a * ⟪y , z⟫ = - a * ⟪ y-x , z ⟫ := by
  have auxlocal1 : a * ⟪x, z⟫ - a * ⟪y, z⟫ = -a * (⟪y, z⟫ - ⟪x, z⟫) := by
    ring
  rw [auxlocal1]
  rw [@inner_sub_left]

omit [CompleteSpace H] in
theorem aux_simp_32 {x y : H} {a : ℝ} : -(a * ⟪x , y⟫) = a * ⟪ x, -y⟫ := by
  simp

theorem aux_simp_33 {a b : ℝ} : 2/a * (-1/a * b) = -2/(a^2) * b := by
  ring

theorem aux_simp_34 {a b : ℝ} : -a + b = 0 → b = a := by
  intros h
  rw [neg_add_eq_zero] at h
  exact h.symm

omit [CompleteSpace H] in
theorem aux_simp_35 {x y z : H} {a : ℝ} : a * ⟪x , y⟫ - a * ⟪x , z⟫ = a * ⟪x , y-z⟫ := by
    rw [inner_sub_right]
    rw [@mul_sub]

theorem aux_simp_36 {a b c d : ℝ} : (a + b = c - d) ↔ (a - c = -b -d) := by
  constructor
  case mp =>
    intro h
    calc
      a - c = a + b - c - b := by ring
          _ = c - d - c - b := by rw [h]
          _ = - b - d := by ring
  case mpr =>
    intro h
    calc
      a + b = a - c + b + c := by ring
          _ =  -b - d + b + c := by rw [h]
    ring

theorem aux_simp_37 {a b : ℝ} : a + b ≤ 0 ↔ -b ≥ a := by
  constructor
  case mp =>
    intro h
    exact le_neg_iff_add_nonpos_right.mpr h
  case mpr =>
    intro h
    exact le_neg_iff_add_nonpos_right.mp h


theorem recurrence_rewritten {I : SamIteration H} (n : ℕ) (h : phi I (n + 1) ≥ ↑n + 1) : I.T (x I n) = x I (n+1) + (phi I (n+1)) ⁻¹ • (x I (n+1) - I.f (x I n)) := by

    have hPhiIndStepIsPos := aux_simp_4 I n h
    have hPhiIndStepNeqZero : phi I (n + 1) ≠  0 := by exact Ne.symm (ne_of_lt hPhiIndStepIsPos)
    have hPhiIndStepPlusOneIsPos : phi I (n + 1) + 1 > 0 := by exact aux_simp_7 hPhiIndStepIsPos
    have hPhiIndStepPlusOneIsNeqZero : phi I (n + 1) + 1 ≠  0 := by exact Ne.symm (ne_of_lt hPhiIndStepPlusOneIsPos)

    have hRegularIterationDefinition := Eq.symm (recurrence_subst_phi I n)
    have hRegularIterationDefinition := aux_simp_5 hRegularIterationDefinition
    have hPhiRapNeqZero : (phi I (n + 1) / (phi I (n + 1) + 1)) ≠ 0 := by
      have aux1 := aux_simp_4 I n h
      have aux2 := aux_simp_7 aux1
      have aux3 := aux_simp_8 aux1 aux2
      linarith
    have hPhiRapNeqZeroInv : ( (phi I (n + 1) + 1)/phi I (n + 1) ) ≠ 0 := by
      have aux1 := aux_simp_4 I n h
      have aux2 := aux_simp_7 aux1
      have aux3 := aux_simp_8 aux2 aux1
      linarith
    have hRegularIterationDefinition := aux_simp_6 hPhiRapNeqZero hRegularIterationDefinition
    field_simp at hRegularIterationDefinition
    have hRegularIterationDefinition : I.T (x I n) = (phi I (n+1))⁻¹ • (phi I (n+1) +1) • x I (n + 1) - (phi I (n+1))⁻¹ • I.f (x I n) := by
      norm_num at hRegularIterationDefinition
      have aux1 := aux_simp_10 hRegularIterationDefinition
      norm_num at aux1
      field_simp at aux1
      rw [aux_simp_12] at aux1
      rw [aux_simp_13] at aux1
      rw [aux_simp_15] at aux1
      have aux2 : ((phi I (n + 1) + 1) • (phi I (n + 1))⁻¹) • x I (n + 1) = (phi I (n + 1))⁻¹ • (phi I (n + 1) + 1) • x I (n + 1)  := by
        rw [aux_simp_16]
      rw [← aux2]
      assumption
      assumption
    exact aux_simp_17 hPhiIndStepNeqZero hRegularIterationDefinition

theorem phi_rewritten {I : SamIteration H} (n : ℕ) : phi I (n+1) * ‖x I n - I.T (x I n)‖^2 = 2 * ⟪x I n - I.T (x I n) , I.f (x I n) - I.T (x I n)⟫ - ‖x I n - I.T (x I n)‖^2 := by
  unfold phi
  norm_num
  have aux1 : ‖x I n - I.T (x I n)‖ ^ 2 ≠ 0 := by
    have hFixedNotEncountered := fixed_point_not_encountered_in_sequence I (n)
    exact aux_simp_3 hFixedNotEncountered
  field_simp
  have aux2 :
  2 * ⟪x I n - I.T (x I n), I.f (x I n) - x I n⟫ - 2 * ⟪x I n - I.T (x I n), I.f (x I n) - I.T (x I n)⟫ =
  -2 * ‖x I n - I.T (x I n)‖^2
  := by
    rw[aux_simp_35]
    norm_num
    rw[inner_factor_minus]
    simp
    rw [← @real_inner_self_eq_norm_sq]
  rw [aux_simp_36]
  rw [aux_simp_35]
  calc
    2 * ⟪x I n - I.T (x I n), I.f (x I n)- x I n - (I.f (x I n) - I.T (x I n))⟫ =
    2 * ⟪x I n - I.T (x I n), I.T (x I n) - x I n⟫
    := by rw [@sub_sub_sub_cancel_left]
    _ = 2 * -⟪x I n - I.T (x I n), x I n - I.T (x I n)⟫
    := by rw [inner_factor_minus]
    _ = -2 * ⟪x I n - I.T (x I n), x I n - I.T (x I n)⟫
    := by simp
    _ = -2 * ‖x I n - I.T (x I n)‖^2
    := by rw [← @real_inner_self_eq_norm_sq]
  ring

theorem norm_consec_squared_ineq {I : SamIteration H} (n : ℕ) (h : phi I (n + 1) ≥ ↑n + 1) : ‖x I n - x I (n+1)‖^2 ≥ ‖ x I (n+1) - I.T (x I (n+1))‖^2 + 2 • (phi I (n+1))⁻¹ • ⟪x I (n+1) - I.T (x I (n+1)) , x I (n+1) - I.f (x I n) ⟫ + (1/(phi I (n+1))^2) • ‖ x I (n+1) - I.f (x I n)‖^2 := by

        have hPhiIndStepIsPos := aux_simp_4 I n h
        have hPhiIndStepNeqZero : phi I (n + 1) ≠  0 := by exact Ne.symm (ne_of_lt hPhiIndStepIsPos)
        have hPhiIndStepPlusOneIsPos : phi I (n + 1) + 1 > 0 := by exact aux_simp_7 hPhiIndStepIsPos
        have hPhiIndStepPlusOneIsNeqZero : phi I (n + 1) + 1 ≠  0 := by exact Ne.symm (ne_of_lt hPhiIndStepPlusOneIsPos)
        have hRecurrenceRewritten := recurrence_rewritten n h

        have hNonexpansiveConsec := I.hTNonExpansive (x I n) (x I (n+1))
        have hConsecTDiff : ‖I.T (x I n) - I.T (x I (n + 1))‖ = ‖ x I (n+1) - I.T (x I (n+1)) + (phi I (n+1))⁻¹ • ( x I (n + 1) - I.f (x I n))‖ := by
          rw [hRecurrenceRewritten]
          abel_nf
        have hConsecTDiffSquared := aux_simp_18 hConsecTDiff
        rw [essential_1] at hConsecTDiffSquared
        rw [norm_smul] at hConsecTDiffSquared
        simp at hConsecTDiffSquared
        have hModPhiEqPhi : |phi I (n+1)| = phi I (n+1) := by
          simp
          exact le_of_lt hPhiIndStepIsPos
        rw [hModPhiEqPhi] at hConsecTDiffSquared
        rw [aux_simp_19] at hConsecTDiffSquared
        rw [aux_simp_20] at hConsecTDiffSquared
        have aux1 : 2 * ((phi I (n + 1))⁻¹ * ⟪x I (n + 1) - I.T (x I (n + 1)), x I (n + 1) - I.f (x I n)⟫)  = 2/(phi I (n+1)) * ⟪x I (n + 1) - I.T (x I (n + 1)), x I (n + 1) - I.f (x I n)⟫:= by field_simp
        rw [aux1] at hConsecTDiffSquared
        have hNorm1Pos : ‖I.T (x I n) - I.T (x I (n + 1))‖ ≥ 0 := by simp
        have hNorm2Pos : ‖x I n - x I (n + 1)‖ ≥ 0 := by simp
        have hNonexpansiveConsecSquared := aux_simp_21 hNorm2Pos hNorm1Pos hNonexpansiveConsec
        have hFinalStep :
        ‖x I n - x I (n + 1)‖ ^ 2 ≥ ‖x I (n + 1) - I.T (x I (n + 1))‖ ^ 2
        + 1 / phi I (n + 1) ^ 2 * ‖x I (n + 1) - I.f (x I n)‖ ^ 2
        + 2 / phi I (n + 1) * ⟪x I (n + 1) - I.T (x I (n + 1)), x I (n + 1) - I.f (x I n)⟫ := by
          exact le_of_eq_of_le (id (Eq.symm hConsecTDiffSquared)) hNonexpansiveConsecSquared
        have auxlocal1 :
        2 • (phi I (n + 1))⁻¹ • ⟪x I (n + 1) - I.T (x I (n + 1)), x I (n + 1) - I.f (x I n)⟫  =
        2 /phi I (n + 1) * ⟪x I (n + 1) - I.T (x I (n + 1)), x I (n + 1) - I.f (x I n)⟫  := by field_simp
        rw [auxlocal1]
        have auxlocal2 : (1 / phi I (n + 1) ^ 2) • ‖x I (n + 1) - I.f (x I n)‖ ^ 2 = (1 / phi I (n + 1) ^ 2) * ‖x I (n + 1) - I.f (x I n)‖ ^ 2 := by field_simp
        rw [auxlocal2]
        have auxlocal3 :
        ‖x I (n + 1) - I.T (x I (n + 1))‖ ^ 2 + 1 / phi I (n + 1) ^ 2 * ‖x I (n + 1) - I.f (x I n)‖ ^ 2 +
        2 / phi I (n + 1) * ⟪x I (n + 1) - I.T (x I (n + 1)), x I (n + 1) - I.f (x I n)⟫ =
        ‖x I (n + 1) - I.T (x I (n + 1))‖ ^ 2 + 2 / phi I (n + 1) * ⟪x I (n + 1) - I.T (x I (n + 1)), x I (n + 1) - I.f (x I n)⟫ +
        1 / phi I (n + 1) ^ 2 * ‖x I (n + 1) - I.f (x I n)‖ ^ 2 := by
          exact add_right_comm (‖x I (n + 1) - I.T (x I (n + 1))‖ ^ 2)
            (1 / phi I (n + 1) ^ 2 * ‖x I (n + 1) - I.f (x I n)‖ ^ 2)
            (2 / phi I (n + 1) * ⟪x I (n + 1) - I.T (x I (n + 1)), x I (n + 1) - I.f (x I n)⟫)
        rw [←auxlocal3]
        assumption

theorem norm_consec_terms_squared_eq {I : SamIteration H} (n : ℕ) (h : phi I (n + 1) ≥ ↑n + 1) :
      ‖x I n - x I (n+1)‖^2 =
      ‖x I n - I.T (x I n)‖^2
      - 2/(phi I (n + 1)+1) * ⟪x I n - I.T (x I n) , I.f (x I n) - I.T (x I n)⟫
      + 1/(phi I (n + 1)+1)^2 * ‖I.f (x I n) - I.T (x I n)‖^2 :=
      by

        have hPhiIndStepIsPos := aux_simp_4 I n h
        have hPhiIndStepNeqZero : phi I (n + 1) ≠  0 := by exact Ne.symm (ne_of_lt hPhiIndStepIsPos)
        have hPhiIndStepPlusOneIsPos : phi I (n + 1) + 1 > 0 := by exact aux_simp_7 hPhiIndStepIsPos
        have hPhiIndStepPlusOneIsNeqZero : phi I (n + 1) + 1 ≠  0 := by exact Ne.symm (ne_of_lt hPhiIndStepPlusOneIsPos)
        have hRecurrenceRewritten := recurrence_rewritten n h

        rw [recurrence_subst_phi]
        have auxlocal1 :
        x I n - ((1 / (phi I (n + 1) + 1)) • I.f (x I n) + (phi I (n + 1) / (phi I (n + 1) + 1)) • I.T (x I n))  =
        (x I n - I.T (x I n)) - (1/(phi I (n+1) + 1)) •  (I.f (x I n) - I.T (x I n))
        := by
          have hAuxPhiRapLocal : (phi I (n+1)) / (phi I (n+1) + 1) = 1 - 1/(phi I (n+1) +1) := by
            rw [aux_simp_22]
            assumption
          rw [hAuxPhiRapLocal]
          rw [factor_diff]
          field_simp
          rw [aux_simp_24]

        rw [auxlocal1]
        rw [essential_1']
        rw [inner_factor]
        rw [factor_norm]
        rw [aux_simp_25]
        rw [aux_simp_26]
        simp
        exact
          add_sub_right_comm (‖x I n - I.T (x I n)‖ ^ 2)
            (((phi I (n + 1) + 1) ^ 2)⁻¹ *  ‖I.f (x I n) - I.T (x I n)‖ ^ 2)
            (2 / (phi I (n + 1) + 1) * ⟪x I n - I.T (x I n), I.f (x I n) - I.T (x I n)⟫)

theorem current_start_diff_norm_sq  {I : SamIteration H} (n : ℕ) (h : phi I (n + 1) ≥ ↑n + 1) : (1/(phi I (n+1))^2) * ‖x I (n+1) - I.f (x I n)‖^2 = (1/(phi I (n+1) +1)^2) * ‖I.f (x I n) - I.T (x I n)‖^2 := by

        have hPhiIndStepIsPos := aux_simp_4 I n h
        have hPhiIndStepNeqZero : phi I (n + 1) ≠  0 := by exact Ne.symm (ne_of_lt hPhiIndStepIsPos)
        have hPhiIndStepPlusOneIsPos : phi I (n + 1) + 1 > 0 := by exact aux_simp_7 hPhiIndStepIsPos
        have hPhiIndStepPlusOneIsNeqZero : phi I (n + 1) + 1 ≠  0 := by exact Ne.symm (ne_of_lt hPhiIndStepPlusOneIsPos)

        have hRecurrenceRewritten : I.T (x I n) = x I (n+1) + (phi I (n+1)) ⁻¹ • (x I (n+1) - I.f (x I n)) := recurrence_rewritten n h
        have hNormConsecSquaredIneq := norm_consec_squared_ineq n h
        have hNormConsecTermsSquaredEq := norm_consec_terms_squared_eq n h

        have term1 :
        ‖x I n - I.T (x I n)‖ ^ 2 =
        ‖x I n - x I (n + 1)‖ ^ 2 + 1/(phi I (n+1))^2 * ‖x I (n+1) - I.f (x I n)‖^2 - (2/(phi I (n+1))) * ⟪ x I n - x I (n+1), x I (n+1) - I.f (x I n) ⟫ :=
        by
          rw [hRecurrenceRewritten]
          have auxlocal1 :
          ‖x I n - (x I (n + 1) + (phi I (n + 1))⁻¹ • (x I (n + 1) - I.f (x I n)))‖ ^ 2 =
          ‖ x I n - x I (n+1)‖^2 + (1/(phi I (n+1))^2) * ‖x I (n+1) - I.f (x I n)‖^2
          - 2/(phi I (n+1)) * ⟪x I n - x I (n+1), x I (n+1) - I.f (x I n)⟫ :=
          by
            have auxlocal1 :
            ‖x I n - (x I (n + 1) + (phi I (n + 1))⁻¹ • (x I (n + 1) - I.f (x I n)))‖ =
            ‖(x I n - x I (n+1)) - (1/(phi I (n+1))) • (x I (n+1) - I.f (x I n))‖ :=
            by
              ring_nf
              abel_nf
            rw [auxlocal1]
            rw [essential_1']
            rw [factor_norm]
            rw [aux_simp_25]
            rw [inner_factor]
            field_simp
          rw [auxlocal1]
        have term2 : 2 / (phi I (n + 1) + 1) * ⟪x I n - I.T (x I n), I.f (x I n) - I.T (x I n)⟫ = -2/(phi I (n+1)) * ⟪x I n - I.T (x I n) , x I (n+1) - I.f (x I n)⟫ :=
          by
          nth_rw 2 [hRecurrenceRewritten]
          rw [aux_simp_28 hPhiIndStepNeqZero]
          rw [inner_factor]
          have auxlocal1 :
          2 / (phi I (n + 1) + 1) * -((phi I (n + 1) + 1) / phi I (n + 1)) • ⟪x I n - I.T (x I n), x I (n + 1) - I.f (x I n)⟫ =
          2 / (phi I (n + 1) + 1) * -((phi I (n + 1) + 1) / phi I (n + 1)) * ⟪x I n - I.T (x I n), x I (n + 1) - I.f (x I n)⟫ :=
            by
            field_simp
            ring_nf
          rw [auxlocal1]
          rw [aux_simp_29 hPhiIndStepNeqZero hPhiIndStepPlusOneIsNeqZero]
        rw [inner_factor_minus] at term1
        rw [term1] at hNormConsecTermsSquaredEq
        rw [term2] at hNormConsecTermsSquaredEq
        have auxlocal1 :
        2 / phi I (n + 1) * -⟪x I n - x I (n + 1), I.f (x I n) - x I (n + 1)⟫ =
        - 2 / phi I (n + 1) * ⟪x I n - x I (n + 1), I.f (x I n) - x I (n + 1)⟫
        := by
          ring
        rw [auxlocal1] at hNormConsecTermsSquaredEq
        nth_rw 2 [inner_factor_minus] at hNormConsecTermsSquaredEq
        have auxlocal2 :
        -2 / phi I (n + 1) * -⟪x I n - I.T (x I n), I.f (x I n) - x I (n + 1)⟫ =
        2 / phi I (n + 1) * ⟪x I n - I.T (x I n), I.f (x I n) - x I (n + 1)⟫
        := by
          ring
        rw [auxlocal2] at hNormConsecTermsSquaredEq
        have auxlocal3 :
        ‖x I n - x I (n + 1)‖ ^ 2 + 1 / phi I (n + 1) ^ 2 * ‖x I (n + 1) - I.f (x I n)‖ ^ 2 -
        -2 / phi I (n + 1) * ⟪x I n - x I (n + 1), I.f (x I n) - x I (n + 1)⟫ -
        2 / phi I (n + 1) * ⟪x I n - I.T (x I n), I.f (x I n) - x I (n + 1)⟫ +
        1 / (phi I (n + 1) + 1) ^ 2 *  ‖I.f (x I n) - I.T (x I n)‖ ^ 2 =
         ‖x I n - x I (n + 1)‖ ^ 2 + (1 / phi I (n + 1) ^ 2 * ‖x I (n + 1) - I.f (x I n)‖ ^ 2 -
        -2 / phi I (n + 1) * ⟪x I n - x I (n + 1), I.f (x I n) - x I (n + 1)⟫ -
        2 / phi I (n + 1) * ⟪x I n - I.T (x I n), I.f (x I n) - x I (n + 1)⟫ +
        1 / (phi I (n + 1) + 1) ^ 2 * ‖I.f (x I n) - I.T (x I n)‖ ^ 2)
        := by
          abel
        rw [auxlocal3] at hNormConsecTermsSquaredEq
        have hMainTerm := aux_simp_30 hNormConsecTermsSquaredEq
        have auxlocal4 :
        1 / phi I (n + 1) ^ 2 * ‖x I (n + 1) - I.f (x I n)‖ ^ 2 - -2 / phi I (n + 1) * ⟪x I n - x I (n + 1), I.f (x I n) - x I (n + 1)⟫ -
        2 / phi I (n + 1) * ⟪x I n - I.T (x I n), I.f (x I n) - x I (n + 1)⟫ +
        1 / (phi I (n + 1) + 1) ^ 2 * ‖ I.f (x I n) - I.T (x I n)‖ ^ 2 =
        1 / phi I (n + 1) ^ 2 * ‖x I (n + 1) - I.f (x I n)‖ ^ 2 + 2 / phi I (n + 1) * ⟪x I n - x I (n + 1), I.f (x I n) - x I (n + 1)⟫ -
        2 / phi I (n + 1) * ⟪x I n - I.T (x I n), I.f (x I n) - x I (n + 1)⟫ +
        1 / (phi I (n + 1) + 1) ^ 2 * ‖ I.f (x I n) - I.T (x I n)‖ ^ 2
        := by
          ring
        rw [auxlocal4] at hMainTerm
        have auxlocal5 :
        1 / phi I (n + 1) ^ 2 * ‖x I (n + 1) - I.f (x I n)‖ ^ 2 + 2 / phi I (n + 1) * ⟪x I n - x I (n + 1), I.f (x I n) - x I (n + 1)⟫ -
        2 / phi I (n + 1) * ⟪x I n - I.T (x I n), I.f (x I n) - x I (n + 1)⟫ +
        1 / (phi I (n + 1) + 1) ^ 2 * ‖ I.f (x I n) - I.T (x I n)‖ ^ 2 =
        1 / phi I (n + 1) ^ 2 * ‖x I (n + 1) - I.f (x I n)‖ ^ 2 + (2 / phi I (n + 1) * ⟪x I n - x I (n + 1), I.f (x I n) - x I (n + 1)⟫ -
        2 / phi I (n + 1) * ⟪x I n - I.T (x I n), I.f (x I n) - x I (n + 1)⟫) +
        1 / (phi I (n + 1) + 1) ^ 2 * ‖ I.f (x I n) - I.T (x I n)‖ ^ 2
        := by
          ring
        rw [auxlocal5] at hMainTerm
        rw [aux_simp_31] at hMainTerm
        have auxterm6 :
        -(2 / phi I (n + 1)) * ⟪x I n - I.T (x I n) - (x I n - x I (n + 1)), I.f (x I n) - x I (n + 1)⟫ =
        (2 / phi I (n + 1)) * ⟪ x I (n + 1) - I.T (x I n) , x I (n + 1) - I.f (x I n)⟫
        := by
          abel_nf
          simp
          rw [aux_simp_32]
          have auxlocal1 : -(-x I (n + 1) + I.f (x I n)) =  x I (n + 1) - I.f (x I n) := by
            ring_nf
            simp
            abel_nf
          rw [auxlocal1]
          abel_nf
        rw [auxterm6] at hMainTerm
        nth_rw 1 [hRecurrenceRewritten] at hMainTerm
        have auxterm7 :
        ⟪x I (n + 1) - (x I (n + 1) + (phi I (n + 1))⁻¹ • (x I (n + 1) - I.f (x I n))), x I (n + 1) - I.f (x I n)⟫ =
        -1/(phi I (n + 1)) * ⟪ x I (n + 1) - I.f (x I n) , x I (n + 1) - I.f (x I n) ⟫
        := by
          norm_num
          rw [@real_inner_smul_left]
          field_simp
        rw[auxterm7] at hMainTerm
        have auxterm8 :
        ⟪x I (n + 1) - I.f (x I n), x I (n + 1) - I.f (x I n)⟫ =
        ‖x I (n + 1) - I.f (x I n)‖^2
        := by
          rw [← @real_inner_self_eq_norm_sq]
        rw [auxterm8] at hMainTerm
        rw [aux_simp_33] at hMainTerm
        have auxterm9 :
        1 / phi I (n + 1) ^ 2 * ‖x I (n + 1) - I.f (x I n)‖ ^ 2 + -2 / phi I (n + 1) ^ 2 * ‖x I (n + 1) - I.f (x I n)‖ ^ 2 =
        -1/ phi I (n + 1) ^ 2 * ‖x I (n + 1) - I.f (x I n)‖ ^ 2
        := by
          ring
        rw [auxterm9] at hMainTerm
        have auxterm10 : -1 / phi I (n + 1) ^ 2 * ‖x I (n + 1) - I.f (x I n)‖ ^ 2 =  -(1 / phi I (n + 1) ^ 2 * ‖x I (n + 1) - I.f (x I n)‖ ^ 2) := by
          field_simp
        rw [auxterm10] at hMainTerm
        have hMainTerm2 :
        1 / (phi I (n + 1) + 1) ^ 2 *  ‖I.f (x I n) - I.T (x I n)‖ ^ 2 = 1 / phi I (n + 1) ^ 2 * ‖x I (n + 1) - I.f (x I n)‖ ^ 2 := aux_simp_34 hMainTerm
        rw [hMainTerm2]

theorem norm_sq_diff_phi {I : SamIteration H} (n : ℕ) (h : phi I (n + 1) ≥ ↑n + 1) : ‖x I n - I.T (x I n)‖ ^ 2 = 2/(phi I (n+1) + 1) * ⟪x I n - I.T (x I n), I.f (x I n) - I.T (x I n)⟫ := by
  have hPhiIndStepIsPos := aux_simp_4 I n h
  have hPhiIndStepNeqZero : phi I (n + 1) ≠  0 := by exact Ne.symm (ne_of_lt hPhiIndStepIsPos)
  have hPhiIndStepPlusOneIsPos : phi I (n + 1) + 1 > 0 := by exact aux_simp_7 hPhiIndStepIsPos
  have hPhiIndStepPlusOneIsNeqZero : phi I (n + 1) + 1 ≠  0 := by exact Ne.symm (ne_of_lt hPhiIndStepPlusOneIsPos)
  have hPhiRw : phi I (n+1) * ‖x I n - I.T (x I n)‖^2 + ‖x I n - I.T (x I n)‖^2 = 2 * ⟪x I n - I.T (x I n) , I.f (x I n) - I.T (x I n)⟫ := by
    rw [@phi_rewritten]
    simp
  have aux1 : (phi I (n + 1) + 1)/(phi I (n + 1) + 1) = 1 := by rw [propext
      (div_eq_one_iff_eq hPhiIndStepPlusOneIsNeqZero)]
  have hPhiRw1 : (phi I (n+1) + 1) * ‖x I n - I.T (x I n)‖^2 = 2 * ⟪x I n - I.T (x I n) , I.f (x I n) - I.T (x I n)⟫ := by
      calc
        (phi I (n + 1) + 1) * ‖x I n - I.T (x I n)‖ ^ 2 =
            phi I (n + 1)  * ‖x I n - I.T (x I n)‖ ^ 2 + ‖x I n - I.T (x I n)‖ ^ 2 :=
            by rw [@add_one_mul]
        _ =  2 * ⟪x I n - I.T (x I n), I.f (x I n) - I.T (x I n)⟫ := by rw [hPhiRw]
  calc
    ‖x I n - I.T (x I n)‖ ^ 2 = 1 * ‖x I n - I.T (x I n)‖ ^ 2 := by simp
    _ = (phi I (n + 1) + 1)/(phi I (n + 1) + 1) * ‖x I n - I.T (x I n)‖ ^ 2 := by rw [aux1]
    _ = (phi I (n + 1) + 1)⁻¹ * ((phi I (n + 1) + 1) * ‖x I n - I.T (x I n)‖ ^ 2) := by field_simp
    _ = (phi I (n + 1) + 1)⁻¹ *  2 * ⟪x I n - I.T (x I n), I.f (x I n) - I.T (x I n)⟫ := by
      rw [hPhiRw1]
      field_simp
  field_simp

omit [InnerProductSpace ℝ H] [CompleteSpace H] in
theorem norm_sum_ineq_split ( x y : H ) : ‖x + y‖ ≤ ‖x‖ + ‖y‖ := by
  exact norm_add_le x y

omit [CompleteSpace H] in
theorem norm_sum_ineq_split_factor_scalars  (a b : ℝ ) (x y : H ) (h1 : a ≥ 0) (h2 : b ≥ 0) : ‖a•x + b•y‖ ≤ a*‖x‖ + b*‖y‖ := by
  have aux1 : ‖a•x + b•y‖ ≤ ‖a • x‖ + ‖b •y‖ :=  norm_sum_ineq_split (a • x) (b • y)
  rw [factor_norm , factor_norm] at aux1
  simp at aux1
  have aux2 : |a| = a := by rw [abs_of_nonneg h1]
  have aux3 : |b| = b := by rw [abs_of_nonneg h2]
  rw [aux2, aux3] at aux1
  assumption

lemma first_bounds (I : SamIteration H) (n : ℕ) : (phi I (n+1) ≥ n+1) ∧ (‖(x I (n+1)) - I.T (x I (n+1))‖^2 ≤ (2/(phi I (n+1))) • ⟪ (x I (n+1)) - I.T (x I (n+1)) , I.f (x I n) - x I (n+1)⟫) := by
  induction n
  case zero =>
    constructor
    case left =>
      norm_num
      rw [first_phi]
    case right =>
      have hRecFirstStep : I.T I.x_0 = (2:ℝ) • x I 1 - I.x_0 := by
        rw [first_term]
        simp
      field_simp at hRecFirstStep
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
      have conc := comparison_util hConsecSquareNonexpansive
      rw [base_case_recurrence]
      rw [first_term_is_contraction_fixed]
      assumption

  case succ n exp =>

    -- left
    have hPhiIndStep := And.left exp
    have hBoundIndStep := And.right exp
    have hPhiIndStepPos : phi I (n+1) ≥ 0 := by linarith
    have hCondition2 := inner_contraction_diff_condition I n

    have hIndStepRwIff :
    ‖x I (n + 1) - I.T (x I (n + 1))‖ ^ 2 ≤ 2 * ⟪x I (n + 1) - I.T (x I (n + 1)), I.f (x I n) - x I (n + 1)⟫ / phi I (n + 1) ↔
    phi I (n + 1) ≤ 2 * ⟪x I (n + 1) - I.T (x I (n + 1)), I.f (x I n) - x I (n + 1)⟫ / ‖x I (n + 1) - I.T (x I (n + 1))‖ ^ 2 := by
      refine Iff.symm (le_div_comm₀ ?_ ?_)
      linarith
      have aux1 := fixed_point_not_encountered_in_sequence I (n+1)
      have aux2 : ‖x I (n + 1) - I.T (x I (n + 1))‖ > 0 := by
        exact norm_sub_pos_iff.mpr aux1
      exact sq_pos_of_pos aux2

    field_simp at hBoundIndStep
    rw [hIndStepRwIff] at hBoundIndStep

    have hLeftConclusion : ↑(n + 1) + 1 ≤ phi I (n + 1 + 1) := by
      calc
        ↑(n + 1) + 1 ≤ phi I (n + 1) + 1:= by
          abel_nf
          simp
          linarith
        _ ≤  2 * ⟪x I (n + 1) - I.T (x I (n + 1)), I.f (x I n) - x I (n + 1)⟫ / ‖x I (n + 1) - I.T (x I (n + 1))‖ ^ 2 + 1 := by
          linarith
        _ ≤ phi I (n + 1 + 1) := by
          unfold phi
          norm_num
          have aux1 := fixed_point_not_encountered_in_sequence I (n+1)
          have aux2 : ‖x I (n + 1) - I.T (x I (n + 1))‖ > 0 := by
            exact norm_sub_pos_iff.mpr aux1
          have aux3 : 1/ ‖x I (n + 1) - I.T (x I (n + 1))‖^2 > 0 := by
            refine aux_simp_8 ?_ ?_
            linarith
            exact sq_pos_of_pos aux2
          refine (div_le_div_iff_of_pos_right ?_).mpr ?_
          exact sq_pos_of_pos aux2
          refine (mul_le_mul_iff_of_pos_left ?_).mpr ?_
          simp
          rw [inner_factor_minus]
          refine neg_le_iff_add_nonneg'.mpr ?_
          have aux4 :
          ⟪x I (n + 1) - I.T (x I (n + 1)), x I (n + 1) - I.f (x I n)⟫ +
          ⟪x I (n + 1) - I.T (x I (n + 1)), I.f (x I (n + 1)) - x I (n + 1)⟫ =
          ⟪x I (n + 1) - I.T (x I (n + 1)) , x I (n + 1) - I.f (x I n) + I.f (x I (n + 1)) - x I (n + 1) ⟫ := by
            rw [← inner_add_right]
            field_simp
            have aux5 : x I (n + 1) - I.f (x I n) + I.f (x I (n + 1)) - x I (n + 1) = - I.f (x I n) + I.f (x I (n + 1)) :=
              by abel
            rw [aux5]
            abel_nf
          rw [aux4]
          abel_nf
          field_simp
          have aux6 :
          ⟪x I (n + 1) + -I.T (x I (n + 1)), -I.f (x I n) + I.f (x I (n + 1))⟫ =
          ⟪x I (n + 1) -I.T (x I (n + 1)),  I.f (x I (n + 1)) - I.f (x I n) ⟫ := by
            abel_nf
          rw [aux6]
          assumption

    --right
    have hRecurrenceRewritten : I.T (x I (n+1)) = x I (n+2) + (phi I (n+2)) ⁻¹ • (x I (n+2) - I.f (x I (n+1))) := recurrence_rewritten (n+1) hLeftConclusion
    have hNormConsecSquaredIneq := norm_consec_squared_ineq (n+1) hLeftConclusion
    have hNormConsecTermsSquaredEq := norm_consec_terms_squared_eq (n+1) hLeftConclusion
    have hCurrentStartDiffNormSq := current_start_diff_norm_sq (n+1) hLeftConclusion
    have hPhiDefinitionRewritten : phi I (n+2) * ‖x I (n+1) - I.T (x I (n+1))‖^2 = 2 * ⟪x I (n+1) - I.T (x I (n+1)) , I.f (x I (n+1)) - I.T (x I (n+1))⟫ - ‖x I (n+1) - I.T (x I (n+1))‖^2 := phi_rewritten (n+1)
    have hPhiNormSqPhi :=  norm_sq_diff_phi (n+1) hLeftConclusion

    rw[hNormConsecTermsSquaredEq] at hNormConsecSquaredIneq
    rw[← hCurrentStartDiffNormSq] at hNormConsecSquaredIneq
    simp at hNormConsecSquaredIneq
    rw[hPhiNormSqPhi] at hNormConsecSquaredIneq
    field_simp at hNormConsecSquaredIneq
    abel_nf at hNormConsecSquaredIneq
    simp at hNormConsecSquaredIneq
    rw [←sub_eq_add_neg] at hNormConsecSquaredIneq
    rw [←sub_eq_add_neg] at hNormConsecSquaredIneq


    constructor
    case left =>
      assumption
    case right =>
      simp
      abel_nf
      simp
      rw [←sub_eq_add_neg]
      rw [aux_simp_37] at hNormConsecSquaredIneq
      field_simp at hNormConsecSquaredIneq
      have auxlocal1 :
      -(2 * ⟪x I (n + 2) - I.T (x I (n + 2)), x I (n + 2) - I.f (x I (n+1))⟫) / phi I (n + 2) =
       2 / phi I (n + 2) * ⟪x I (n + 2) - I.T (x I (n + 2)), -x I (n + 2) + I.f (x I (n+1))⟫ := by
        ring_nf
        rw [inner_factor_minus]
        simp
        field_simp
        rw [@neg_add_eq_sub]
      rw [auxlocal1] at hNormConsecSquaredIneq
      assumption
