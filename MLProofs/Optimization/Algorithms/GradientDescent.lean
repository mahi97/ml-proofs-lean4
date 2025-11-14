import MLProofs.Optimization.Core.DescentLemma
import Mathlib

namespace MLProofs
namespace Optimization
namespace Algorithms

open Core
open scoped RealInnerProductSpace

variable {X : Type _} [NormedAddCommGroup X] [InnerProductSpace ℝ X]

/--
One step of gradient descent with step size `η` applied to `x`.
-/
def gdStep (obj : Core.DiffObjective X) (η : ℝ) (x : X) : X :=
  x - η • obj.grad x

/--
Linear convergence of gradient descent under strong convexity and smoothness.
The proof is currently a stub; the goal is to show that iterates contract
geometrically towards the unique minimizer `xstar` provided by the simple
strong convexity assumption.  This version asserts the usual norm bound.
`TODO`: fill in the contraction proof by combining the descent lemma with the
quadratic lower bound from `mu_strong_convex_simple`.
-/
theorem gd_linear_convergence
    [MLParamSpace X]
    (obj : Core.DiffObjective X) {L μ : ℝ} (η : ℝ)
    (hL : Core.L_smooth_grad obj L) (hμ : Core.mu_strong_convex_simple obj.f μ)
    (hη : 0 < η ∧ η < 2 / L)
    (xstar : X) (hmin : ∀ x, obj.f x ≥ obj.f xstar) :
    ∃ ρ : ℝ, 0 < ρ ∧ ρ < 1 ∧
      ∀ k x0,
        ‖(Nat.iterate (gdStep obj η) k x0) - xstar‖ ≤ ρ ^ k * ‖x0 - xstar‖ := by
  -- TODO: build the contraction argument for the GD operator around `xstar`.
  sorry

end Algorithms
end Optimization
end MLProofs
