import Prim.Release.AcceptedAssumptionsV0.Upper
import Prim.Release.AcceptedAssumptionsV0.OffDiag

/-!
Publication-facing theorem map for the accepted-assumptions stochastic v0
boundary.

The broader compatibility map also exports explicit constructor aliases.
-/

namespace Prim.Release.TheoremMap

noncomputable section

/-! Public stochastic source boundary. -/

/-- Stochastic-representation source package used by the compact theorem. -/
abbrev StochasticRotationOptimalitySource :=
  Prim.Elliptical.StochasticRotationOptimalitySource

/-- Main same-set stochastic-representation theorem. -/
abbrev stochasticRepresentationRotationOptimalityConst :=
  @Prim.Elliptical.stochasticRepresentation_rotationOptimality

abbrev stochasticRepresentationRotationOptimalityCovTargetPairConst :=
  @Prim.Elliptical.stochasticRepresentation_rotationOptimality_covTarget_trace_sandwich_pair

abbrev stochasticRepresentationRotationOptimalityObjectivePairConst :=
  @Prim.Elliptical.stochasticRepresentation_rotationOptimality_objective_sandwich_pair

abbrev stochasticRepresentationRotationOptimalityCovTargetPairSameSetConst :=
  @Prim.Elliptical.stochasticRepresentation_rotationOptimality_covTarget_trace_sandwich_pair_sameSet

abbrev stochasticRepresentationRotationOptimalityObjectiveSameSetConst :=
  @Prim.Elliptical.stochasticRepresentation_rotationOptimality

abbrev stochasticRepresentationRotationOptimalityObjectivePairSameSetConst :=
  @Prim.Elliptical.stochasticRepresentation_rotationOptimality_objective_sandwich_pair_sameSet

/-! Accepted-assumptions stochastic v0 citation points. -/

/-- Upper-triangular accepted-assumptions v0 source package. -/
abbrev stochasticAcceptedAssumptionSource :=
  Prim.Release.AcceptedAssumptionsV0.Source

abbrev stochasticAcceptedAssumptionRotationOptimalityConst :=
  @Prim.Elliptical.stochasticPrincipalBoxAmbientFormulaSource_publicRotationOptimality

abbrev stochasticAcceptedAssumptionCovTargetTraceSandwichPairSameSetConst :=
  @Prim.Elliptical.stochasticPrincipalBoxAmbientFormulaSource_publicCovTargetTraceSandwichPairSameSet

abbrev stochasticAcceptedAssumptionCovTargetTraceSandwichPairConst :=
  @Prim.Elliptical.stochasticPrincipalBoxAmbientFormulaSource_covTargetTraceSandwichPair

abbrev stochasticAcceptedAssumptionObjectiveSandwichPairConst :=
  @Prim.Elliptical.stochasticPrincipalBoxAmbientFormulaSource_objectiveSandwichPair

/-- Full off-diagonal accepted-assumptions v0 source package. -/
abbrev stochasticAcceptedAssumptionOffDiagSource :=
  Prim.Release.AcceptedAssumptionsV0.OffDiagSource

abbrev stochasticAcceptedAssumptionOffDiagRotationOptimalityConst :=
  @Prim.Elliptical.stochasticPrincipalBoxAmbientOffDiagFormulaSource_publicRotationOptimality

abbrev stochasticAcceptedAssumptionOffDiagCovTargetTraceSandwichPairSameSetConst :=
  @Prim.Elliptical.stochasticPrincipalBoxAmbientOffDiagFormulaSource_publicCovTargetTraceSandwichPairSameSet

abbrev stochasticAcceptedAssumptionOffDiagCovTargetTraceSandwichPairConst :=
  @Prim.Elliptical.stochasticPrincipalBoxAmbientOffDiagFormulaSource_covTargetTraceSandwichPair

abbrev stochasticAcceptedAssumptionOffDiagObjectiveSandwichPairConst :=
  @Prim.Elliptical.stochasticPrincipalBoxAmbientOffDiagFormulaSource_objectiveSandwichPair

end

end Prim.Release.TheoremMap
