import Prim.Elliptical.StochasticRepresentation.Main.Sandwich.CovTarget

namespace Prim.Elliptical

open Prim.LinearAlgebra.DoublyStochasticKernel

noncomputable section

namespace StochasticRotationOptimalitySource

variable {d : Nat}
variable (S : StochasticRotationOptimalitySource d)

/-- Quantile-interval objective sandwich for the moment branch. -/
theorem moment_quantileInterval_objective_sandwich
    (U : OrthogonalMatrixRotation d)
    {I : Finset (Prim.Idx d)} (hI : I.card = S.momentTarget.k) :
    S.momentLeadingQuantileTrace <= S.momentObjective U I /\
      S.momentObjective U I <= S.momentTrailingQuantileTrace := by
  have h := S.moment_quantileInterval_covTarget_trace_sandwich U hI
  have hobj := S.momentTarget.covTarget_trace_eq_objective U I
  exact ⟨by simpa [momentCovTargetTrace, momentObjective, hobj] using h.1,
    by simpa [momentCovTargetTrace, momentObjective, hobj] using h.2⟩

/-- Quantile-interval objective sandwich for the integral branch. -/
theorem integral_quantileInterval_objective_sandwich
    (U : OrthogonalMatrixRotation d)
    {I : Finset (Prim.Idx d)} (hI : I.card = S.integralTarget.k) :
    S.integralLeadingQuantileTrace <= S.integralObjective U I /\
      S.integralObjective U I <= S.integralTrailingQuantileTrace := by
  have h := S.integral_quantileInterval_covTarget_trace_sandwich U hI
  have hobj := S.integralTarget.covTarget_trace_eq_objective U I
  exact ⟨by simpa [integralCovTargetTrace, integralObjective, hobj] using h.1,
    by simpa [integralCovTargetTrace, integralObjective, hobj] using h.2⟩

end StochasticRotationOptimalitySource

end

end Prim.Elliptical
