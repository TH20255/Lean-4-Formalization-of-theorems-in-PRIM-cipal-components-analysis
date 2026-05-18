import Prim.Elliptical.StochasticRepresentation.Main.Sandwich.Objective

namespace Prim.Elliptical

open Prim.LinearAlgebra.DoublyStochasticKernel

noncomputable section

namespace StochasticRotationOptimalitySource

variable {d : Nat}
variable (S : StochasticRotationOptimalitySource d)

/-- Paired covariance-target trace sandwich for the public stochastic source. -/
theorem quantileInterval_covTarget_trace_sandwich_pair
    (Um : OrthogonalMatrixRotation d)
    {Im : Finset (Prim.Idx d)} (hIm : Im.card = S.momentTarget.k)
    (Ui : OrthogonalMatrixRotation d)
    {Ii : Finset (Prim.Idx d)} (hIi : Ii.card = S.integralTarget.k) :
    (S.momentLeadingQuantileTrace <= S.momentCovTargetTrace Um Im /\
        S.momentCovTargetTrace Um Im <= S.momentTrailingQuantileTrace) /\
      S.integralLeadingQuantileTrace <= S.integralCovTargetTrace Ui Ii /\
        S.integralCovTargetTrace Ui Ii <= S.integralTrailingQuantileTrace := by
  exact ⟨S.moment_quantileInterval_covTarget_trace_sandwich Um hIm,
    S.integral_quantileInterval_covTarget_trace_sandwich Ui hIi⟩

/-- Paired objective sandwich for the public stochastic source. -/
theorem quantileInterval_objective_sandwich_pair
    (Um : OrthogonalMatrixRotation d)
    {Im : Finset (Prim.Idx d)} (hIm : Im.card = S.momentTarget.k)
    (Ui : OrthogonalMatrixRotation d)
    {Ii : Finset (Prim.Idx d)} (hIi : Ii.card = S.integralTarget.k) :
    (S.momentLeadingQuantileTrace <= S.momentObjective Um Im /\
        S.momentObjective Um Im <= S.momentTrailingQuantileTrace) /\
      S.integralLeadingQuantileTrace <= S.integralObjective Ui Ii /\
        S.integralObjective Ui Ii <= S.integralTrailingQuantileTrace := by
  exact ⟨S.moment_quantileInterval_objective_sandwich Um hIm,
    S.integral_quantileInterval_objective_sandwich Ui hIi⟩

/-- Same-set covariance-target trace sandwich for the public stochastic source. -/
theorem quantileInterval_covTarget_trace_sandwich_pair_sameSet
    (hk : S.momentTarget.k = S.integralTarget.k)
    (U : OrthogonalMatrixRotation d)
    {I : Finset (Prim.Idx d)} (hI : I.card = S.momentTarget.k) :
    (S.momentLeadingQuantileTrace <= S.momentCovTargetTrace U I /\
        S.momentCovTargetTrace U I <= S.momentTrailingQuantileTrace) /\
      S.integralLeadingQuantileTrace <= S.integralCovTargetTrace U I /\
        S.integralCovTargetTrace U I <= S.integralTrailingQuantileTrace := by
  exact S.quantileInterval_covTarget_trace_sandwich_pair U hI U (by simpa [hk] using hI)

/-- Same-set objective sandwich for the public stochastic source. -/
theorem quantileInterval_objective_sandwich_pair_sameSet
    (hk : S.momentTarget.k = S.integralTarget.k)
    (U : OrthogonalMatrixRotation d)
    {I : Finset (Prim.Idx d)} (hI : I.card = S.momentTarget.k) :
    (S.momentLeadingQuantileTrace <= S.momentObjective U I /\
        S.momentObjective U I <= S.momentTrailingQuantileTrace) /\
      S.integralLeadingQuantileTrace <= S.integralObjective U I /\
        S.integralObjective U I <= S.integralTrailingQuantileTrace := by
  exact S.quantileInterval_objective_sandwich_pair U hI U (by simpa [hk] using hI)

end StochasticRotationOptimalitySource

end

end Prim.Elliptical
