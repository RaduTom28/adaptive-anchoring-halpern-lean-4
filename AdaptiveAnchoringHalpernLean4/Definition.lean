import Mathlib.Analysis.InnerProductSpace.Basic

local notation "⟪" x ", " y "⟫" => inner ℝ x y

structure Iteration (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] where
  x_0 : E
  T : E → E
  hTNonExpansive : ∀ x y : E, ‖T x - T y‖ ≤ ‖x - y‖
  hTHasFixedPoint : ∃ x_star : E, T x_star = x_star


variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

noncomputable def x (I : Iteration H) (n : Nat) : H :=
match n with
  | 0     => I.x_0
  | (n+1) =>
      let ϕ := 2 * ⟪x I n - I.T (x I n), I.x_0 - x I n⟫ / (‖x I n - I.T (x I n)‖ ^ 2) + 1
      (1 / (ϕ + 1)) •  I.x_0 + (ϕ / (ϕ + 1)) •  I.T (x I n)

noncomputable def phi (I : Iteration H)(n : Nat) : ℝ := 2 * ⟪x I (n-1) - I.T (x I (n-1)), I.x_0 - x I (n-1)⟫ / (‖x I (n-1) - I.T (x I (n-1))‖ ^ 2) + 1


lemma phi_n_geq_n (I : Iteration H) (n : Nat) : phi I (n+1) ≥ n+1:= by
  induction n
  case zero =>
    simp
    unfold phi
    simp
    unfold x
    simp
  case succ => sorry -- needs next


lemma first_approx (I : Iteration H) (n : Nat)
