import Prim.Proofs.BoxVolume.QuantileRadiusSource
import Prim.Proofs.RotationOptimality.MomentFormulaTarget.Targets.Core.Moment.Data
import Prim.Proofs.RotationOptimality.MomentFormulaTarget.Targets.Core.Integral.Data

/-!
Public stochastic-representation entrance for rotation optimality.

This module is the non-historical public boundary for the main theorem chain.
It starts from an `EllipticalCore`, a clean principal central-quantile source,
and the two compact rotated-peeling formula targets. Characteristic
function constructors may still build these objects elsewhere, but the theorem
below does not expose characteristic-function assumptions.
-/

namespace Prim.Elliptical

open Prim.LinearAlgebra
open Prim.LinearAlgebra.DoublyStochasticKernel
open Prim.Proofs.CardinalOrderedValueKDimensionalRotationConExpProfile

noncomputable section
/-- Compact centered-moment target used by the stochastic public boundary. -/
abbrev StochasticCenteredMomentRotationTarget (d : Nat) :=
  CardinalRotatedPeelCenteredMomentTarget d

/-- Compact centered-integral target used by the stochastic public boundary. -/
abbrev StochasticCenteredIntegralRotationTarget (d : Nat) :=
  CardinalRotatedPeelCenteredIntegralTarget d

/--
Public source package for the stochastic-representation version of the final
rotation-optimality theorem.

The package deliberately keeps the distributional source as `EllipticalCore`.
The quantile-source field is the paper-facing probabilistic input, and the two
formula targets are the checked moment and integral routes to the same
objective sandwich.
-/
structure StochasticRotationOptimalitySource (d : Nat) where
  core : EllipticalCore d
  quantileSource : EllipticalCore.PrincipalCentralQuantileSource core
  momentTarget : StochasticCenteredMomentRotationTarget d
  integralTarget : StochasticCenteredIntegralRotationTarget d
  moment_same_core : momentTarget.diagonal.core = core
  integral_same_core : integralTarget.diagonal.core = core
  moment_same_radius : momentTarget.diagonal.q = quantileSource.radius
  integral_same_radius : integralTarget.diagonal.q = quantileSource.radius

namespace StochasticRotationOptimalitySource

variable {d : Nat}
variable (S : StochasticRotationOptimalitySource d)

/-- Internal checked quantile/radius handoff derived from the public quantile source. -/
def quantile : Prim.Proofs.PrincipalQuantileRadiusAssumption S.core :=
  Prim.Proofs.PrincipalQuantileRadiusAssumption.ofPrincipalCentralQuantileSource
    S.quantileSource

@[simp] theorem quantile_Q :
    S.quantile.Q = S.quantileSource.toCentralQuantileBoxData := rfl

@[simp] theorem quantile_radius : S.quantile.radius = S.quantileSource.radius := rfl

@[simp] theorem quantile_hradius : S.quantile.hradius = S.quantileSource.hradius := rfl

/-- Constructor from a named principal central-quantile source. -/
def ofPrincipalCentralQuantileSource
    (core : EllipticalCore d)
    (quantile : EllipticalCore.PrincipalCentralQuantileSource core)
    (momentTarget : StochasticCenteredMomentRotationTarget d)
    (integralTarget : StochasticCenteredIntegralRotationTarget d)
    (moment_same_core : momentTarget.diagonal.core = core)
    (integral_same_core : integralTarget.diagonal.core = core)
    (moment_same_radius : momentTarget.diagonal.q = quantile.radius)
    (integral_same_radius : integralTarget.diagonal.q = quantile.radius) :
    StochasticRotationOptimalitySource d where
  core := core
  quantileSource := quantile
  momentTarget := momentTarget
  integralTarget := integralTarget
  moment_same_core := moment_same_core
  integral_same_core := integral_same_core
  moment_same_radius := by
    simpa using moment_same_radius
  integral_same_radius := by
    simpa using integral_same_radius


end StochasticRotationOptimalitySource

end

end Prim.Elliptical
