import Prim.Elliptical.StochasticRepresentation.V0.Upper.Theorems.Public

/-!
Upper-triangular accepted-assumptions v0 release spine.

This is the lightest publication-facing v0 entrance.  It exposes the
accepted-assumptions stochastic theorem boundary with upper-triangular
cancellation, while the stronger full off-diagonal sibling lives in
`Prim.Release.AcceptedAssumptionsV0.OffDiag`.
-/

namespace Prim.Release.AcceptedAssumptionsV0

noncomputable section

/--
Upper-triangular accepted-assumptions v0 source package: stochastic
representation, clean principal quantile source, principal-box moment/formula
sources, and upper-triangular cancellation are theorem inputs.
-/
abbrev Source := Prim.Elliptical.StochasticPrincipalBoxAmbientFormulaSource

/-- Same-set rotation-optimality theorem for the upper-triangular v0 source. -/
abbrev rotationOptimalityConst :=
  @Prim.Elliptical.stochasticPrincipalBoxAmbientFormulaSource_publicRotationOptimality

/-- Same-set covariance-target trace theorem for the upper-triangular v0 source. -/
abbrev covTargetTraceSandwichPairSameSetConst :=
  @Prim.Elliptical.stochasticPrincipalBoxAmbientFormulaSource_publicCovTargetTraceSandwichPairSameSet

/-- Two-rotation covariance-target trace theorem for the upper-triangular v0 source. -/
abbrev covTargetTraceSandwichPairConst :=
  @Prim.Elliptical.stochasticPrincipalBoxAmbientFormulaSource_covTargetTraceSandwichPair

/-- Two-rotation objective theorem for the upper-triangular v0 source. -/
abbrev objectiveSandwichPairConst :=
  @Prim.Elliptical.stochasticPrincipalBoxAmbientFormulaSource_objectiveSandwichPair

end

end Prim.Release.AcceptedAssumptionsV0
