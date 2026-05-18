import Prim.Elliptical.StochasticRepresentation.Main.Source

namespace Prim.Elliptical

open Prim.LinearAlgebra
open Prim.LinearAlgebra.DoublyStochasticKernel
open Prim.Proofs.CardinalOrderedValueKDimensionalRotationConExpProfile

noncomputable section

namespace StochasticRotationOptimalitySource

variable {d : Nat}
variable (S : StochasticRotationOptimalitySource d)

/-- Principal-box leading endpoint for the moment branch. -/
def momentLeadingPrincipalTrace : Real :=
  (S.core.principalBoxData S.quantile.radius S.quantile.hradius).preservedTrace
    S.core.μ S.core.Y (leadingIndexSet d S.momentTarget.k)

/-- Principal-box trailing endpoint for the moment branch. -/
def momentTrailingPrincipalTrace : Real :=
  (S.core.principalBoxData S.quantile.radius S.quantile.hradius).preservedTrace
    S.core.μ S.core.Y (trailingIndexSet d S.momentTarget.k)

/-- Principal-box leading endpoint for the integral branch. -/
def integralLeadingPrincipalTrace : Real :=
  (S.core.principalBoxData S.quantile.radius S.quantile.hradius).preservedTrace
    S.core.μ S.core.Y (leadingIndexSet d S.integralTarget.k)

/-- Principal-box trailing endpoint for the integral branch. -/
def integralTrailingPrincipalTrace : Real :=
  (S.core.principalBoxData S.quantile.radius S.quantile.hradius).preservedTrace
    S.core.μ S.core.Y (trailingIndexSet d S.integralTarget.k)

/-- Quantile-interval leading endpoint for the moment branch. -/
def momentLeadingQuantileTrace : Real :=
  Prim.Probability.preservedTrace d S.core.μ
    (S.quantile.Q.intervalEvent (leadingIndexSet d S.momentTarget.k)) S.core.Y

/-- Quantile-interval trailing endpoint for the moment branch. -/
def momentTrailingQuantileTrace : Real :=
  Prim.Probability.preservedTrace d S.core.μ
    (S.quantile.Q.intervalEvent (trailingIndexSet d S.momentTarget.k)) S.core.Y

/-- Quantile-interval leading endpoint for the integral branch. -/
def integralLeadingQuantileTrace : Real :=
  Prim.Probability.preservedTrace d S.core.μ
    (S.quantile.Q.intervalEvent (leadingIndexSet d S.integralTarget.k)) S.core.Y

/-- Quantile-interval trailing endpoint for the integral branch. -/
def integralTrailingQuantileTrace : Real :=
  Prim.Probability.preservedTrace d S.core.μ
    (S.quantile.Q.intervalEvent (trailingIndexSet d S.integralTarget.k)) S.core.Y

/-- Covariance-target trace for the moment branch. -/
def momentCovTargetTrace
    (U : OrthogonalMatrixRotation d) (I : Finset (Prim.Idx d)) : Real :=
  Matrix.trace (orthogonalMatrixDiagonalTraceCovTarget S.momentTarget.diagonal U I)

/-- Covariance-target trace for the integral branch. -/
def integralCovTargetTrace
    (U : OrthogonalMatrixRotation d) (I : Finset (Prim.Idx d)) : Real :=
  Matrix.trace (orthogonalMatrixDiagonalTraceCovTarget S.integralTarget.diagonal U I)

/-- Diagonal trace objective for the moment branch. -/
def momentObjective
    (U : OrthogonalMatrixRotation d) (I : Finset (Prim.Idx d)) : Real :=
  orthogonalMatrixDiagonalTraceObjective S.momentTarget.diagonal U I

/-- Diagonal trace objective for the integral branch. -/
def integralObjective
    (U : OrthogonalMatrixRotation d) (I : Finset (Prim.Idx d)) : Real :=
  orthogonalMatrixDiagonalTraceObjective S.integralTarget.diagonal U I


end StochasticRotationOptimalitySource

end

end Prim.Elliptical
