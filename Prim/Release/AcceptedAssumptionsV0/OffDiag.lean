import Prim.Elliptical.StochasticRepresentation.V0.OffDiag.Theorems.Public

/-!
Full off-diagonal accepted-assumptions v0 release sibling.

This module extends the upper-triangular v0 release spine with the stronger
full off-diagonal source package and theorem aliases.
-/

namespace Prim.Release.AcceptedAssumptionsV0

noncomputable section

/--
Full off-diagonal accepted-assumptions v0 source package.
-/
abbrev OffDiagSource :=
  Prim.Elliptical.StochasticPrincipalBoxAmbientOffDiagFormulaSource

/-- Same-set rotation-optimality theorem for the full off-diagonal v0 source. -/
abbrev offDiagRotationOptimalityConst :=
  @Prim.Elliptical.stochasticPrincipalBoxAmbientOffDiagFormulaSource_publicRotationOptimality

/-- Same-set covariance-target trace theorem for the full off-diagonal v0 source. -/
abbrev offDiagCovTargetTraceSandwichPairSameSetConst :=
  @Prim.Elliptical.stochasticPrincipalBoxAmbientOffDiagFormulaSource_publicCovTargetTraceSandwichPairSameSet

/-- Two-rotation covariance-target trace theorem for the full off-diagonal v0 source. -/
abbrev offDiagCovTargetTraceSandwichPairConst :=
  @Prim.Elliptical.stochasticPrincipalBoxAmbientOffDiagFormulaSource_covTargetTraceSandwichPair

/-- Two-rotation objective theorem for the full off-diagonal v0 source. -/
abbrev offDiagObjectiveSandwichPairConst :=
  @Prim.Elliptical.stochasticPrincipalBoxAmbientOffDiagFormulaSource_objectiveSandwichPair

end

end Prim.Release.AcceptedAssumptionsV0
