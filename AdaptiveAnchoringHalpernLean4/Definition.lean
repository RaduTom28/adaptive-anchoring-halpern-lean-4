import Mathlib.Analysis.InnerProductSpace.Basic


--todo: include x_n

local notation "⟪" x ", " y "⟫" => inner ℝ x y

structure Iteration (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] where
  x_0: E
  T : E → E
  hTNonExpansive : ∀ x y : E, ‖T x - T y‖ ≤ ‖x - y‖
  hTHasFixedPoint : ∃ x_star : E, T x_star = x_star




variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]


def phi (I : Iteration H) (n : Nat) := 2 * ⟪x n - T (x n), x₀ - x n⟫ / (‖x n - T (x n)‖ ^ 2)

def x_n (I : Iteration H) (n : Nat) : H
| 0     => x₀
| (n+1) =>
    let ϕ := 2 * ⟪x n - T (x n), x₀ - x n⟫ / (‖x n - T (x n)‖ ^ 2)
    (1 / (ϕ + 1)) • x₀ + (ϕ / (ϕ + 1)) • T (x n)

-- lemma phi_n_geq_n (I : Iteration H) (x y : H) (n : Nat): phi I n ≥ n := by
--  sorry
