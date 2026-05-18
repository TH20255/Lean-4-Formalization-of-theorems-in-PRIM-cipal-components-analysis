import Prim.Elliptical.StochasticRepresentation.Main.Sandwich.Pair

namespace Prim.Elliptical

open Prim.LinearAlgebra
open Prim.LinearAlgebra.DoublyStochasticKernel
open Prim.Proofs.CardinalOrderedValueKDimensionalRotationConExpProfile

noncomputable section

variable {d : Nat}

/-- Public stochastic-representation covariance-target trace theorem. -/
theorem stochasticRepresentation_rotationOptimality_covTarget_trace_sandwich_pair
    (S : StochasticRotationOptimalitySource d)
    (Um : OrthogonalMatrixRotation d)
    {Im : Finset (Prim.Idx d)} (hIm : Im.card = S.momentTarget.k)
    (Ui : OrthogonalMatrixRotation d)
    {Ii : Finset (Prim.Idx d)} (hIi : Ii.card = S.integralTarget.k) :
    (S.momentLeadingQuantileTrace <= S.momentCovTargetTrace Um Im /\
        S.momentCovTargetTrace Um Im <= S.momentTrailingQuantileTrace) /\
      S.integralLeadingQuantileTrace <= S.integralCovTargetTrace Ui Ii /\
        S.integralCovTargetTrace Ui Ii <= S.integralTrailingQuantileTrace :=
  S.quantileInterval_covTarget_trace_sandwich_pair Um hIm Ui hIi

/-- Public stochastic-representation objective theorem. -/
theorem stochasticRepresentation_rotationOptimality_objective_sandwich_pair
    (S : StochasticRotationOptimalitySource d)
    (Um : OrthogonalMatrixRotation d)
    {Im : Finset (Prim.Idx d)} (hIm : Im.card = S.momentTarget.k)
    (Ui : OrthogonalMatrixRotation d)
    {Ii : Finset (Prim.Idx d)} (hIi : Ii.card = S.integralTarget.k) :
    (S.momentLeadingQuantileTrace <= S.momentObjective Um Im /\
        S.momentObjective Um Im <= S.momentTrailingQuantileTrace) /\
      S.integralLeadingQuantileTrace <= S.integralObjective Ui Ii /\
        S.integralObjective Ui Ii <= S.integralTrailingQuantileTrace :=
  S.quantileInterval_objective_sandwich_pair Um hIm Ui hIi

/-- Same-set public stochastic-representation covariance-target trace theorem. -/
theorem stochasticRepresentation_rotationOptimality_covTarget_trace_sandwich_pair_sameSet
    (S : StochasticRotationOptimalitySource d)
    (hk : S.momentTarget.k = S.integralTarget.k)
    (U : OrthogonalMatrixRotation d)
    {I : Finset (Prim.Idx d)} (hI : I.card = S.momentTarget.k) :
    (S.momentLeadingQuantileTrace <= S.momentCovTargetTrace U I /\
        S.momentCovTargetTrace U I <= S.momentTrailingQuantileTrace) /\
      S.integralLeadingQuantileTrace <= S.integralCovTargetTrace U I /\
        S.integralCovTargetTrace U I <= S.integralTrailingQuantileTrace :=
  S.quantileInterval_covTarget_trace_sandwich_pair_sameSet hk U hI

/--
Main public stochastic-representation theorem.

This is the publication-facing entry point: under the stochastic source package
and equal moment/integral target cardinalities, both checked routes satisfy the
same quantile-interval objective sandwich for the same rotation and index set.
-/
theorem stochasticRepresentation_rotationOptimality
    (S : StochasticRotationOptimalitySource d)
    (hk : S.momentTarget.k = S.integralTarget.k)
    (U : OrthogonalMatrixRotation d)
    {I : Finset (Prim.Idx d)} (hI : I.card = S.momentTarget.k) :
    (S.momentLeadingQuantileTrace <= S.momentObjective U I /\
        S.momentObjective U I <= S.momentTrailingQuantileTrace) /\
      S.integralLeadingQuantileTrace <= S.integralObjective U I /\
        S.integralObjective U I <= S.integralTrailingQuantileTrace :=
  S.quantileInterval_objective_sandwich_pair_sameSet hk U hI

/-- Backward-descriptive alias for the same-set public objective theorem. -/
theorem stochasticRepresentation_rotationOptimality_objective_sandwich_pair_sameSet
    (S : StochasticRotationOptimalitySource d)
    (hk : S.momentTarget.k = S.integralTarget.k)
    (U : OrthogonalMatrixRotation d)
    {I : Finset (Prim.Idx d)} (hI : I.card = S.momentTarget.k) :
    (S.momentLeadingQuantileTrace <= S.momentObjective U I /\
        S.momentObjective U I <= S.momentTrailingQuantileTrace) /\
      S.integralLeadingQuantileTrace <= S.integralObjective U I /\
        S.integralObjective U I <= S.integralTrailingQuantileTrace :=
  stochasticRepresentation_rotationOptimality S hk U hI


end

end Prim.Elliptical
