import Prim.Elliptical.StochasticRepresentation.Main.Endpoints
import Prim.Proofs.RotationOptimality.MomentFormulaTarget.Targets.Core.Integral.Trace.CovTarget

namespace Prim.Elliptical

open Prim.LinearAlgebra
open Prim.LinearAlgebra.DoublyStochasticKernel
open Prim.Proofs.CardinalOrderedValueKDimensionalRotationConExpProfile

noncomputable section

namespace StochasticRotationOptimalitySource

variable {d : Nat}
variable (S : StochasticRotationOptimalitySource d)

/-- Principal-box covariance-target trace sandwich for the moment branch. -/
theorem moment_principalBox_covTarget_trace_sandwich
    (U : OrthogonalMatrixRotation d)
    {I : Finset (Prim.Idx d)} (hI : I.card = S.momentTarget.k) :
    S.momentLeadingPrincipalTrace <= S.momentCovTargetTrace U I /\
      S.momentCovTargetTrace U I <= S.momentTrailingPrincipalTrace := by
  have h := S.momentTarget.covTarget_trace_sandwich U hI
  have hlead :
      S.momentTarget.diagonal.core.preservedTraceOn S.momentTarget.diagonal.q
          (leadingIndexSet d S.momentTarget.k) =
        S.momentLeadingPrincipalTrace := by
    calc
      S.momentTarget.diagonal.core.preservedTraceOn S.momentTarget.diagonal.q
          (leadingIndexSet d S.momentTarget.k)
          = S.core.preservedTraceOn S.quantile.radius
              (leadingIndexSet d S.momentTarget.k) := by
              rw [S.moment_same_core, S.moment_same_radius, S.quantile_radius]
      _ = S.momentLeadingPrincipalTrace := by
              simpa [momentLeadingPrincipalTrace] using
                S.core.preservedTraceOn_eq S.quantile.radius S.quantile.hradius
                  (leadingIndexSet d S.momentTarget.k)
  have htrail :
      S.momentTarget.diagonal.core.preservedTraceOn S.momentTarget.diagonal.q
          (trailingIndexSet d S.momentTarget.k) =
        S.momentTrailingPrincipalTrace := by
    calc
      S.momentTarget.diagonal.core.preservedTraceOn S.momentTarget.diagonal.q
          (trailingIndexSet d S.momentTarget.k)
          = S.core.preservedTraceOn S.quantile.radius
              (trailingIndexSet d S.momentTarget.k) := by
              rw [S.moment_same_core, S.moment_same_radius, S.quantile_radius]
      _ = S.momentTrailingPrincipalTrace := by
              simpa [momentTrailingPrincipalTrace] using
                S.core.preservedTraceOn_eq S.quantile.radius S.quantile.hradius
                  (trailingIndexSet d S.momentTarget.k)
  exact ⟨by simpa [momentCovTargetTrace, hlead] using h.1,
    by simpa [momentCovTargetTrace, htrail] using h.2⟩

/-- Principal-box covariance-target trace sandwich for the integral branch. -/
theorem integral_principalBox_covTarget_trace_sandwich
    (U : OrthogonalMatrixRotation d)
    {I : Finset (Prim.Idx d)} (hI : I.card = S.integralTarget.k) :
    S.integralLeadingPrincipalTrace <= S.integralCovTargetTrace U I /\
      S.integralCovTargetTrace U I <= S.integralTrailingPrincipalTrace := by
  have h := S.integralTarget.covTarget_trace_sandwich U hI
  have hlead :
      S.integralTarget.diagonal.core.preservedTraceOn S.integralTarget.diagonal.q
          (leadingIndexSet d S.integralTarget.k) =
        S.integralLeadingPrincipalTrace := by
    calc
      S.integralTarget.diagonal.core.preservedTraceOn S.integralTarget.diagonal.q
          (leadingIndexSet d S.integralTarget.k)
          = S.core.preservedTraceOn S.quantile.radius
              (leadingIndexSet d S.integralTarget.k) := by
              rw [S.integral_same_core, S.integral_same_radius, S.quantile_radius]
      _ = S.integralLeadingPrincipalTrace := by
              simpa [integralLeadingPrincipalTrace] using
                S.core.preservedTraceOn_eq S.quantile.radius S.quantile.hradius
                  (leadingIndexSet d S.integralTarget.k)
  have htrail :
      S.integralTarget.diagonal.core.preservedTraceOn S.integralTarget.diagonal.q
          (trailingIndexSet d S.integralTarget.k) =
        S.integralTrailingPrincipalTrace := by
    calc
      S.integralTarget.diagonal.core.preservedTraceOn S.integralTarget.diagonal.q
          (trailingIndexSet d S.integralTarget.k)
          = S.core.preservedTraceOn S.quantile.radius
              (trailingIndexSet d S.integralTarget.k) := by
              rw [S.integral_same_core, S.integral_same_radius, S.quantile_radius]
      _ = S.integralTrailingPrincipalTrace := by
              simpa [integralTrailingPrincipalTrace] using
                S.core.preservedTraceOn_eq S.quantile.radius S.quantile.hradius
                  (trailingIndexSet d S.integralTarget.k)
  exact ⟨by simpa [integralCovTargetTrace, hlead] using h.1,
    by simpa [integralCovTargetTrace, htrail] using h.2⟩

/-- Quantile-interval covariance-target trace sandwich for the moment branch. -/
theorem moment_quantileInterval_covTarget_trace_sandwich
    (U : OrthogonalMatrixRotation d)
    {I : Finset (Prim.Idx d)} (hI : I.card = S.momentTarget.k) :
    S.momentLeadingQuantileTrace <= S.momentCovTargetTrace U I /\
      S.momentCovTargetTrace U I <= S.momentTrailingQuantileTrace := by
  have h := S.moment_principalBox_covTarget_trace_sandwich U hI
  have hlead :=
    S.quantile.intervalPreservedTrace_eq_principalBoxData_preservedTrace
      (leadingIndexSet d S.momentTarget.k)
  have htrail :=
    S.quantile.intervalPreservedTrace_eq_principalBoxData_preservedTrace
      (trailingIndexSet d S.momentTarget.k)
  constructor
  · rw [momentLeadingQuantileTrace, hlead]
    exact h.1
  · rw [momentTrailingQuantileTrace, htrail]
    exact h.2

/-- Quantile-interval covariance-target trace sandwich for the integral branch. -/
theorem integral_quantileInterval_covTarget_trace_sandwich
    (U : OrthogonalMatrixRotation d)
    {I : Finset (Prim.Idx d)} (hI : I.card = S.integralTarget.k) :
    S.integralLeadingQuantileTrace <= S.integralCovTargetTrace U I /\
      S.integralCovTargetTrace U I <= S.integralTrailingQuantileTrace := by
  have h := S.integral_principalBox_covTarget_trace_sandwich U hI
  have hlead :=
    S.quantile.intervalPreservedTrace_eq_principalBoxData_preservedTrace
      (leadingIndexSet d S.integralTarget.k)
  have htrail :=
    S.quantile.intervalPreservedTrace_eq_principalBoxData_preservedTrace
      (trailingIndexSet d S.integralTarget.k)
  constructor
  · rw [integralLeadingQuantileTrace, hlead]
    exact h.1
  · rw [integralTrailingQuantileTrace, htrail]
    exact h.2

end StochasticRotationOptimalitySource

end

end Prim.Elliptical
