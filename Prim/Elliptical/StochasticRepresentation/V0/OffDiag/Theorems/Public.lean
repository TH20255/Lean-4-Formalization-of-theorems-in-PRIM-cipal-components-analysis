import Prim.Elliptical.StochasticRepresentation.V0.OffDiag.Source.Conversions
import Prim.Elliptical.StochasticRepresentation.Main.Theorems

/-!
Public theorem wrappers for the full off-diagonal accepted-assumptions v0 source.
-/

namespace Prim.Elliptical

open Prim.LinearAlgebra
open Prim.LinearAlgebra.DoublyStochasticKernel
open Prim.Proofs.CardinalOrderedValueKDimensionalRotationConExpProfile
open MeasureTheory

noncomputable section

variable {d : Nat}

/--
Same-set theorem from the full off-diagonal v0 source package, stated directly
on the final public stochastic source object.
-/
theorem stochasticPrincipalBoxAmbientOffDiagFormulaSource_publicRotationOptimality
    (S : StochasticPrincipalBoxAmbientOffDiagFormulaSource d)
    (U : OrthogonalMatrixRotation d)
    {I : Finset (Prim.Idx d)} (hI : I.card = S.k) :
    (S.toRotationOptimalitySource.momentLeadingQuantileTrace <=
        S.toRotationOptimalitySource.momentObjective U I /\
      S.toRotationOptimalitySource.momentObjective U I <=
        S.toRotationOptimalitySource.momentTrailingQuantileTrace) /\
      S.toRotationOptimalitySource.integralLeadingQuantileTrace <=
        S.toRotationOptimalitySource.integralObjective U I /\
      S.toRotationOptimalitySource.integralObjective U I <=
        S.toRotationOptimalitySource.integralTrailingQuantileTrace := by
  simpa [StochasticPrincipalBoxAmbientOffDiagFormulaSource.toRotationOptimalitySource,
    StochasticPrincipalBoxAmbientOffDiagFormulaSource.toAmbientAngularMomentOffDiagSource] using
    stochasticRepresentation_rotationOptimality
      S.toRotationOptimalitySource rfl U hI

/--
Same-set covariance-target theorem from the full off-diagonal v0 source
package, stated directly on the final public stochastic source object.
-/
theorem stochasticPrincipalBoxAmbientOffDiagFormulaSource_publicCovTargetTraceSandwichPairSameSet
    (S : StochasticPrincipalBoxAmbientOffDiagFormulaSource d)
    (U : OrthogonalMatrixRotation d)
    {I : Finset (Prim.Idx d)} (hI : I.card = S.k) :
    (S.toRotationOptimalitySource.momentLeadingQuantileTrace <=
        S.toRotationOptimalitySource.momentCovTargetTrace U I /\
      S.toRotationOptimalitySource.momentCovTargetTrace U I <=
        S.toRotationOptimalitySource.momentTrailingQuantileTrace) /\
      S.toRotationOptimalitySource.integralLeadingQuantileTrace <=
        S.toRotationOptimalitySource.integralCovTargetTrace U I /\
      S.toRotationOptimalitySource.integralCovTargetTrace U I <=
        S.toRotationOptimalitySource.integralTrailingQuantileTrace := by
  simpa [StochasticPrincipalBoxAmbientOffDiagFormulaSource.toRotationOptimalitySource,
    StochasticPrincipalBoxAmbientOffDiagFormulaSource.toAmbientAngularMomentOffDiagSource] using
    stochasticRepresentation_rotationOptimality_covTarget_trace_sandwich_pair_sameSet
      S.toRotationOptimalitySource rfl U hI

/--
Two-rotation covariance-target theorem from the full off-diagonal v0 source
package.
-/
theorem stochasticPrincipalBoxAmbientOffDiagFormulaSource_covTargetTraceSandwichPair
    (S : StochasticPrincipalBoxAmbientOffDiagFormulaSource d)
    (Um : OrthogonalMatrixRotation d)
    {Im : Finset (Prim.Idx d)} (hIm : Im.card = S.k)
    (Ui : OrthogonalMatrixRotation d)
    {Ii : Finset (Prim.Idx d)} (hIi : Ii.card = S.k) :
    (S.toRotationOptimalitySource.momentLeadingQuantileTrace <=
        S.toRotationOptimalitySource.momentCovTargetTrace Um Im /\
      S.toRotationOptimalitySource.momentCovTargetTrace Um Im <=
        S.toRotationOptimalitySource.momentTrailingQuantileTrace) /\
      S.toRotationOptimalitySource.integralLeadingQuantileTrace <=
        S.toRotationOptimalitySource.integralCovTargetTrace Ui Ii /\
      S.toRotationOptimalitySource.integralCovTargetTrace Ui Ii <=
        S.toRotationOptimalitySource.integralTrailingQuantileTrace := by
  simpa [StochasticPrincipalBoxAmbientOffDiagFormulaSource.toRotationOptimalitySource,
    StochasticPrincipalBoxAmbientOffDiagFormulaSource.toAmbientAngularMomentOffDiagSource] using
    stochasticRepresentation_rotationOptimality_covTarget_trace_sandwich_pair
      S.toRotationOptimalitySource Um hIm Ui hIi

/-- Two-rotation objective theorem from the full off-diagonal v0 source package. -/
theorem stochasticPrincipalBoxAmbientOffDiagFormulaSource_objectiveSandwichPair
    (S : StochasticPrincipalBoxAmbientOffDiagFormulaSource d)
    (Um : OrthogonalMatrixRotation d)
    {Im : Finset (Prim.Idx d)} (hIm : Im.card = S.k)
    (Ui : OrthogonalMatrixRotation d)
    {Ii : Finset (Prim.Idx d)} (hIi : Ii.card = S.k) :
    (S.toRotationOptimalitySource.momentLeadingQuantileTrace <=
        S.toRotationOptimalitySource.momentObjective Um Im /\
      S.toRotationOptimalitySource.momentObjective Um Im <=
        S.toRotationOptimalitySource.momentTrailingQuantileTrace) /\
      S.toRotationOptimalitySource.integralLeadingQuantileTrace <=
        S.toRotationOptimalitySource.integralObjective Ui Ii /\
      S.toRotationOptimalitySource.integralObjective Ui Ii <=
        S.toRotationOptimalitySource.integralTrailingQuantileTrace := by
  simpa [StochasticPrincipalBoxAmbientOffDiagFormulaSource.toRotationOptimalitySource,
    StochasticPrincipalBoxAmbientOffDiagFormulaSource.toAmbientAngularMomentOffDiagSource] using
    stochasticRepresentation_rotationOptimality_objective_sandwich_pair
      S.toRotationOptimalitySource Um hIm Ui hIi

end

end Prim.Elliptical
