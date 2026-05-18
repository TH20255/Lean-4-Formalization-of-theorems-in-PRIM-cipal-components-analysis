import Prim.Elliptical.Core.DiagonalCovariance.Basic
import Prim.Proofs.KDimensional.Core.Constructors.TraceFormula
import Prim.Proofs.KDimensional.Diagonal.Base

/-!
Shared stochastic diagonal profile and constructors from principal-box
formula packages.
-/

namespace Prim.Elliptical

open Prim.Proofs

noncomputable section

/-- Shared diagonal profile for stochastic-representation rotation targets. -/
structure StochasticDiagonalProfile (d : Nat) where
  core : EllipticalCore d
  radius : Real
  radius_nonneg : 0 <= radius
  diagonal : KDimensionalDiagonalProfile d
  same_core : diagonal.core = core
  same_radius : diagonal.q = radius

namespace StochasticDiagonalProfile

variable {d : Nat}

/-- Build the shared stochastic diagonal profile from a centered-product package. -/
def ofPrincipalBoxCenteredProductMomentDiagUpperFormula
    (core : EllipticalCore d) (q : Real) (hq : 0 <= q)
    (F : EllipticalCore.PrincipalBoxCenteredProductMomentDiagUpperFormula core q hq) :
    StochasticDiagonalProfile d :=
  let base := KDimensionalProfile.ofPrincipalBoxCenteredProductMomentDiagFormula F.diag
  { core := core
    radius := q
    radius_nonneg := hq
    diagonal :=
      KDimensionalDiagonalProfile.ofBoxCenteredProductMomentAndUpperCenteredProductMoment
        base F.diag.a F.diag.b hq F.diag.formula F.upper.formula
    same_core := by
      rfl
    same_radius := by
      rfl }

/-- Build the shared stochastic diagonal profile from a centered-integral package. -/
def ofPrincipalBoxCenteredIntegralDiagUpperFormula
    (core : EllipticalCore d) (q : Real) (hq : 0 <= q)
    (F : EllipticalCore.PrincipalBoxCenteredIntegralDiagUpperFormula core q hq) :
    StochasticDiagonalProfile d :=
  let base := KDimensionalProfile.ofPrincipalBoxCenteredIntegralDiagFormula F.diag
  { core := core
    radius := q
    radius_nonneg := hq
    diagonal :=
      KDimensionalDiagonalProfile.ofBoxCenteredIntegralAndUpperCenteredIntegral
        base F.diag.a F.diag.b hq F.diag.formula F.upper.formula
    same_core := by
      rfl
    same_radius := by
      rfl }

/-- Build the shared stochastic diagonal profile from one diagonal covariance family. -/
def ofPrincipalBoxDiagonalCovarianceFamily
    (core : EllipticalCore d) (q : Real) (hq : 0 <= q)
    (F : EllipticalCore.PrincipalBoxDiagonalCovarianceFamily core q hq) :
    StochasticDiagonalProfile d :=
  ofPrincipalBoxCenteredProductMomentDiagUpperFormula
    core q hq F.toProductMomentDiagUpperFormula

/-- Inherit the coefficient sign needed by rotated formula blocks. -/
theorem ofPrincipalBoxDiagonalCovarianceFamily_coeff_nonpos
    {core : EllipticalCore d} {q : Real} {hq : 0 <= q}
    (F : EllipticalCore.PrincipalBoxDiagonalCovarianceFamily core q hq) :
    (ofPrincipalBoxDiagonalCovarianceFamily core q hq F).diagonal.b -
        (ofPrincipalBoxDiagonalCovarianceFamily core q hq F).diagonal.a <= 0 := by
  simpa [ofPrincipalBoxDiagonalCovarianceFamily,
    ofPrincipalBoxCenteredProductMomentDiagUpperFormula] using F.coeff_nonpos

end StochasticDiagonalProfile

end

end Prim.Elliptical
