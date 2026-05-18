import Prim.Elliptical.StochasticRepresentation.Main.Theorems
import Prim.Release.AcceptedAssumptionsV0.Upper
import Prim.Release.AcceptedAssumptionsV0.OffDiag

/-!
Public/core release aliases for the stochastic-representation route.

This leaf contains the publication-facing theorem constants without raw,
sign-symmetry, family, or lower-constructor convenience aliases.
-/

namespace Prim.Release.StochasticRepresentation

noncomputable section

/-- Public stochastic-representation source package. -/
abbrev Source := Prim.Elliptical.StochasticRotationOptimalitySource

/-- Main same-set public theorem. -/
abbrev rotationOptimalityConst :=
  @Prim.Elliptical.stochasticRepresentation_rotationOptimality

/-- Two-rotation covariance-target trace theorem. -/
abbrev covTargetTraceSandwichPairConst :=
  @Prim.Elliptical.stochasticRepresentation_rotationOptimality_covTarget_trace_sandwich_pair

/-- Two-rotation objective theorem. -/
abbrev objectiveSandwichPairConst :=
  @Prim.Elliptical.stochasticRepresentation_rotationOptimality_objective_sandwich_pair

/-- Same-set covariance-target trace theorem. -/
abbrev covTargetTraceSandwichPairSameSetConst :=
  @Prim.Elliptical.stochasticRepresentation_rotationOptimality_covTarget_trace_sandwich_pair_sameSet

/-- Same-set objective theorem. -/
abbrev objectiveSandwichPairSameSetConst :=
  @Prim.Elliptical.stochasticRepresentation_rotationOptimality_objective_sandwich_pair_sameSet

/-! Accepted-assumptions v0 citation points. -/

/--
Accepted-assumptions v0 source package: stochastic representation, a clean
principal quantile source, and principal-box moment/formula sources are taken
as the theorem inputs.
-/
abbrev AcceptedAssumptionSource :=
  Prim.Release.AcceptedAssumptionsV0.Source

abbrev acceptedAssumptionRotationOptimalityConst :=
  @Prim.Elliptical.stochasticPrincipalBoxAmbientFormulaSource_publicRotationOptimality
abbrev acceptedAssumptionCovTargetTraceSandwichPairSameSetConst :=
  @Prim.Elliptical.stochasticPrincipalBoxAmbientFormulaSource_publicCovTargetTraceSandwichPairSameSet
abbrev acceptedAssumptionCovTargetTraceSandwichPairConst :=
  @Prim.Elliptical.stochasticPrincipalBoxAmbientFormulaSource_covTargetTraceSandwichPair
abbrev acceptedAssumptionObjectiveSandwichPairConst :=
  @Prim.Elliptical.stochasticPrincipalBoxAmbientFormulaSource_objectiveSandwichPair

/-- Full off-diagonal accepted-assumptions v0 source package. -/
abbrev AcceptedAssumptionOffDiagSource :=
  Prim.Release.AcceptedAssumptionsV0.OffDiagSource

abbrev acceptedAssumptionOffDiagRotationOptimalityConst :=
  @Prim.Elliptical.stochasticPrincipalBoxAmbientOffDiagFormulaSource_publicRotationOptimality
abbrev acceptedAssumptionOffDiagCovTargetTraceSandwichPairSameSetConst :=
  @Prim.Elliptical.stochasticPrincipalBoxAmbientOffDiagFormulaSource_publicCovTargetTraceSandwichPairSameSet
abbrev acceptedAssumptionOffDiagCovTargetTraceSandwichPairConst :=
  @Prim.Elliptical.stochasticPrincipalBoxAmbientOffDiagFormulaSource_covTargetTraceSandwichPair
abbrev acceptedAssumptionOffDiagObjectiveSandwichPairConst :=
  @Prim.Elliptical.stochasticPrincipalBoxAmbientOffDiagFormulaSource_objectiveSandwichPair

end

end Prim.Release.StochasticRepresentation
