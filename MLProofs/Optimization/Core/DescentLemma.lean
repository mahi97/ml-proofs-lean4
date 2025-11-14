import MLProofs.Optimization.Core.Assumptions
import Mathlib

namespace MLProofs
namespace Optimization
namespace Core

open scoped RealInnerProductSpace

variable {X : Type _} [NormedAddCommGroup X] [InnerProductSpace ℝ X]

/--
A smooth objective satisfies the standard descent lemma: moving from `x` to `y`
can increase the objective value by at most a linear term controlled by the
current gradient plus a quadratic term scaled by the smoothness constant `L`.
`TODO`: supply the full proof by referencing mathlib's smoothness lemmas.
-/
lemma descent_lemma
    (obj : DiffObjective X) {L : ℝ} (hL : L_smooth_grad obj L) :
    ∀ x y,
      obj.f y ≤
        obj.f x + ‖obj.grad x‖ * ‖y - x‖ + (L / 2) * ‖y - x‖ ^ 2 := by
  -- TODO: reference standard smoothness inequality once available.
  intro x y
  sorry

end Core
end Optimization
end MLProofs
