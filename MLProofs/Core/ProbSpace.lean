import Mathlib

noncomputable section

open scoped BigOperators
open MeasureTheory

namespace MLProofs
namespace Core

/--
`ProbSpace` is a lightweight wrapper around a type equipped with a
`MeasureSpace` structure.  Future iterations can pin a probability measure on
`Ω`; for now we only retain the measurable universe and use stubs for
expectation.
-/
structure ProbSpace where
  /-- The sample space. -/
  Ω : Type _
  /-- Measurable structure on the sample space. -/
  measureSpace : MeasureSpace Ω
  /-- Probability measure on the sample space. -/
  μ : Measure Ω
  /-- Certificate that `μ` is a probability measure. -/
  prob : IsProbabilityMeasure μ

attribute [instance] ProbSpace.measureSpace

instance (P : ProbSpace) : IsProbabilityMeasure P.μ := P.prob

/-- Random variables valued in `α` are simply measurable functions on `Ω`. -/
abbrev RandomVar (P : ProbSpace) (α : Type _) := P.Ω → α

namespace ProbSpace

/--
Bochner expectation as an integral with respect to the probability measure.
-/
noncomputable def expectation
    (P : ProbSpace) {E : Type _} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] (X : RandomVar P E) : E :=
  ∫ ω, X ω ∂P.μ

end ProbSpace

end Core
end MLProofs
