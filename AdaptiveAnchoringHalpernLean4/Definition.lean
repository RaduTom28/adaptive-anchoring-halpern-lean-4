import Mathlib.Analysis.InnerProductSpace.Basic


--todo: include x_n


structure Iteration (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] where
  x_0: E
  T : E → E
  hTNonExpansive : ∀ x y : E, ‖T x - T y‖ ≤ ‖x - y‖
  hTHasFixedPoint : ∃ x_star : E, T x_star = x_star




variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]


def phi (I : Iteration H) (n : Nat) := sorry

def x_n (I : Iteration H) (n : Nat) := sorry


lemma phi_n_geq_n (I : Iteration H) (x y : H) (n : Nat): phi I n ≥ n := by
 sorry
