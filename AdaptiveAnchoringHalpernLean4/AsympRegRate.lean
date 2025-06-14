import AdaptiveAnchoringHalpernLean4.OriginalIteration
import Mathlib.Topology.Sequences
open Filter Topology

class RateOfConvergence (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] where
  b : ℕ → ℝ
  hBNonNeg : ∀ n : ℕ , b n ≥ 0
  φ : ℕ → ℕ
  hPhi : ∀ (k n: ℕ) , (n ≥ φ k) → (b n ≤ 1/(k+1))


variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable (M : ℕ)

axiom M_cond (I : Iteration H) (p : H) (hPFixed : I.T p = p) : M ≥ ‖I.x_0 - p‖

def Phi (M : ℕ) (k : ℕ) : ℕ := 4 * M * (k+1)

noncomputable
def t_asymp_seq (I : Iteration H) (n : ℕ) : ℝ := ‖x I n - I.T (x I n)‖

theorem aux_1 {a b c : ℕ} (h1 : a ≥ b) (h2: b > c) : a > c := by linarith

theorem aux_1' {a b c : ℝ} (h1 : a ≥ b) (h2: b > c) : a > c := by linarith

theorem aux_2' {c a b: ℝ} (h : c > 0) : a ≥ b → c * a ≥ c * b := by
  intros h
  (expose_names; exact (mul_ineq_sides h_1).mp h)

theorem aux_2 (n M k : ℝ) (h : k+1 > 0): n ≥ 4 * M * (k + 1) → M ≤ n/(4*(k+1)) := by
  intros h1
  have aux1 : n / (k+1) ≥ 4 * M := by exact (le_div_iff₀ h).mpr h1
  have aux2 : 1/4 * n / (k+1) ≥ 1/4 * 4 * M := by
    have auxlocal1 : ((1/4):ℝ) > 0 :=  by simp
    have auxlocal2 := aux_2' auxlocal1 aux1
    field_simp
    field_simp at auxlocal2
    assumption
  have aux3 :  1 / 4 * n / (k + 1) =  n / (4 * (k + 1)) := by
    field_simp
  have aux4 :  1 / 4 * 4 * M = M := by simp
  rw [aux4] at aux2
  rw [aux3] at aux2
  assumption


theorem aux_4 (n : ℕ ) (h : n > 0) : n - 1 + 1 = n := by
  exact Nat.sub_add_cancel h


theorem b_non_neg {I : Iteration H} : ∀ (n : ℕ), t_asymp_seq I n ≥ 0:= by
  intros n
  unfold t_asymp_seq
  exact norm_nonneg (x I n - I.T (x I n))


theorem h_phi {I : Iteration H} : ∀ (k n : ℕ), n ≥ Phi M k → t_asymp_seq I n ≤ 1 / (↑k + 1) := by
  intros k n hN
  unfold t_asymp_seq
  unfold Phi at hN
  have hFixedExists := I.hTHasFixedPoint
  have hKPlusOneNeqZero : k + 1 ≠ 0 := by
    induction k
    case zero =>
      simp
    case succ k hInd =>
      simp
  match hFixedExists with
  | ⟨p, hPfixed⟩ =>
    have hMCond := M_cond M I p hPfixed
    have hNormdiffNeqZero : ‖I.x_0 - p‖ > 0 := by
      have hInitialNotFixed := I.hInitialNotFixed
      refine norm_sub_pos_iff.mpr ?_
      by_contra hContra
      rw [← hContra] at hPfixed
      contradiction
    have hMNeqZero : (M:ℝ) ≠ 0 := by
      have auxlocal := aux_1' hMCond hNormdiffNeqZero
      exact Ne.symm (ne_of_lt auxlocal)
    have hMGeZero : M > 0 := by
      refine Nat.zero_lt_of_ne_zero ?_
      norm_cast
      intros hContra
      norm_cast at hMNeqZero
    have hKPlusOneGeZero : k+1 > 0:= by
      induction k
      simp
      simp
    have hKPlusOneGeZeroCast : (k:ℝ)+1 > 0 := by
      norm_cast
    have hNGeZero : n > 0 := by
      have auxlocal :  4 * M * (k + 1) > 0 := by
        refine Nat.mul_pos ?_ hKPlusOneGeZero
        linarith
      exact aux_1 hN auxlocal

    have hNCast : (n:ℝ) ≥ 4 * (M:ℝ) * ((k:ℝ) + 1) := by norm_cast

    have hNRw : M ≤ n/(4*(k+1)) := by
      refine (Nat.le_div_iff_mul_le ?_).mpr ?_
      induction k
      linarith
      linarith
      induction n
      linarith
      linarith
    have hNRwCast : (M:ℝ) ≤ (n:ℝ)/(4*((k:ℝ)+1)) := by
      exact aux_2 (n:ℝ) (M:ℝ) (k:ℝ) hKPlusOneGeZeroCast hNCast
    have hIneqSec : 1/(k+1) ≥ 4/n * ‖I.x_0 - p‖ := by
      have auxlocal1 : ‖I.x_0 - p‖ ≤ ↑n / (4 * (↑k + 1)) := by linarith
      have auxlocal2 : 1/(n:ℝ) * ‖I.x_0 - p‖ ≤ 1 / (4 * (↑k + 1)) := by
        have hNGeZeroCast : (n:ℝ) > 0 := by exact Nat.cast_pos'.mpr hNGeZero
        have hNinvGeZeroCast : 1/(n:ℝ) > 0:= by exact one_div_pos.mpr hNGeZeroCast
        have hConc := aux_2' hNinvGeZeroCast auxlocal1
        have extra : 1 /(n:ℝ) * ((n:ℝ) / (4 * (↑k + 1))) = 1 / (4 * (↑k + 1)) := by
          ring_nf
          have final_simp : (n:ℝ) * (n:ℝ)⁻¹ = 1 := by
            refine mul_inv_cancel₀ ?_
            linarith
          rw [final_simp]
          simp
        rw [extra] at hConc
        assumption
      have auxlocal3 : 4 * 1 / ↑n * ‖I.x_0 - p‖ ≤ 4 * 1 / (4 * (↑k + 1)) := by
        have aux1: (4:ℝ) > 0 := by simp
        have aux2 := aux_2' aux1 auxlocal2
        field_simp at aux2
        field_simp
        assumption
      simp at auxlocal3
      have auxlocal4 : 4 / (4 * ((k:ℝ) + 1)) = 1 / ((k:ℝ) + 1) := by field_simp
      rw [auxlocal4] at auxlocal3
      assumption
    have hTAsympReg := t_asymp_reg I p hPfixed (n-1)
    rw [aux_4] at hTAsympReg
    have auxlocal1 :  4 / (↑(n - 1) + 1) * ‖I.x_0 - p‖ = 4 / ↑n * ‖I.x_0 - p‖ := by field_simp
    rw [auxlocal1] at hTAsympReg
    linarith
    assumption

noncomputable
instance AdaptiveIterationRateOfConvergence {I : Iteration H} : RateOfConvergence H where
  b := t_asymp_seq I
  hBNonNeg := b_non_neg
  φ := Phi M
  hPhi := h_phi M
