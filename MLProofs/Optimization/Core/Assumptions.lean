import Mathlib
import MLProofs.Core.ProbSpace

namespace MLProofs
namespace Core

/--
`MLProofs.Core.ParamSpace` abstracts the ambient parameter space for optimization
problems.  It currently records that the space carries the usual normed
structure inherited from mathlib; future iterations can extend it with
finite-dimensionality or smooth manifold hypotheses if needed.
-/
class ParamSpace (X : Type _) [NormedAddCommGroup X] [NormedSpace ℝ X] : Prop where
  /-- Placeholder for future structure assumptions. -/
  triv : True := trivial

end Core

/-- Convenience alias so we can write `[MLParamSpace X]` in theorems. -/
abbrev MLParamSpace (X : Type _) [NormedAddCommGroup X] [InnerProductSpace ℝ X] :=
  Core.ParamSpace X

namespace Optimization
namespace Core

open scoped RealInnerProductSpace

variable {X : Type _} [NormedAddCommGroup X] [InnerProductSpace ℝ X]

open MLProofs.Core
open MeasureTheory

/--
`DiffObjective` bundles an objective function and a candidate gradient field.
The object is intentionally minimal so that specific algorithms can attach
the assumptions they need (smoothness, convexity, etc.).
-/
structure DiffObjective (X : Type _) [NormedAddCommGroup X] [InnerProductSpace ℝ X]
    where
  f : X → ℝ
  grad : X → X
  /-- The gradient agrees with the Fréchet derivative via the Riesz map. -/
  hasGrad : ∀ x, HasFDerivAt f ((innerSL ℝ (grad x))) x

namespace DiffObjective

/-- Standard coercion so we can treat a `DiffObjective` as its underlying map. -/
instance : CoeFun (DiffObjective X) (fun _ => X → ℝ) where
  coe obj := obj.f

end DiffObjective

/--
`L_smooth_grad obj L` records the Lipschitz continuity of the gradient field.
The constant `L` must be nonnegative.  This assumption is the usual starting
point for the descent lemma and smooth convex optimization.
-/
def L_smooth_grad (obj : DiffObjective X) (L : ℝ) : Prop :=
  0 ≤ L ∧ ∀ x y, ‖obj.grad x - obj.grad y‖ ≤ L * ‖x - y‖

/--
`mu_strong_convex_simple f μ` is a simplified strong convexity statement that
only refers to function values.  It is strong enough to imply uniqueness of the
minimizer and provides the quadratic lower bound needed for linear convergence.
`TODO`: upgrade this to the full gradient inequality version when we connect to
mathlib's convex analysis.
-/
def mu_strong_convex_simple (f : X → ℝ) (μ : ℝ) : Prop :=
  0 < μ ∧ ∀ x y, f y ≥ f x + (μ / 2) * ‖y - x‖ ^ 2

section Stochastic

variable [CompleteSpace X]

/--
`UnbiasedSG obj P g` states that the stochastic gradient oracle `g` has finite
expectation matching the analytic gradient of `obj`.
-/
structure UnbiasedSG (obj : DiffObjective X) (P : ProbSpace)
    (g : X → P.Ω → X) : Prop where
  /-- Integrability of the stochastic gradient. -/
  integrable : ∀ x, Integrable (fun ω => g x ω) P.μ
  /-- Unbiasedness: `E[g(x, ω)] = ∇f(x)`. -/
  unbiased :
    ∀ x,
      ProbSpace.expectation P (fun ω => g x ω) = obj.grad x

/--
`BoundedVarSG obj P g σ` requires that the second moment around the analytic
gradient is uniformly bounded by `σ^2`.
-/
structure BoundedVarSG (obj : DiffObjective X) (P : ProbSpace)
    (g : X → P.Ω → X) (σ : ℝ) : Prop where
  /-- Nonnegativity of the variance parameter. -/
  σ_nonneg : 0 ≤ σ
  /-- Second moment bound. -/
  variance_bound :
    ∀ x,
      ∫ ω, ‖g x ω - obj.grad x‖ ^ 2 ∂P.μ ≤ σ ^ 2

end Stochastic

end Core
end Optimization
end MLProofs
