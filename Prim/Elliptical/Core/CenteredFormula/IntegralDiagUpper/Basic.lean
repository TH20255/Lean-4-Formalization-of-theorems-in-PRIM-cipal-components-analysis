import Prim.Elliptical.Core.CenteredFormula.Diag.Integral
import Prim.Elliptical.Core.CenteredFormula.Upper
import Prim.Probability.ConditionalCovariance.CentralBox.Core.Diagonal

open scoped BigOperators
open MeasureTheory

namespace Prim.Elliptical

namespace EllipticalCore

variable {d : Nat} (E : EllipticalCore d)

/--
Combined principal-box centered-integral diagonal and upper-triangular formulas.

This is the compact analytic target for producing a diagonal covariance profile
from centered-integral covariance identities.
-/
structure PrincipalBoxCenteredIntegralDiagUpperFormula
    (E : EllipticalCore d) (q : ℝ) (hq : 0 ≤ q) where
  diag : PrincipalBoxCenteredIntegralDiagFormula E q hq
  upper : PrincipalBoxCenteredIntegralUpperFormula E q hq

namespace PrincipalBoxCenteredIntegralDiagUpperFormula

variable {d : Nat} {E : EllipticalCore d} {q : ℝ} {hq : 0 ≤ q}

/-- Build the combined centered-integral formula object from raw formulas. -/
noncomputable def ofFormula
    (a b : ℝ) (hcoeff : b - a ≤ 0)
    (hdiag :
      ∀ I j,
        (∫ ω, (E.Y ω j -
              Prim.Probability.meanVec d
                (Prim.Probability.condOn E.μ ((E.principalBoxData q hq).event E.Y I)) E.Y j) *
            (E.Y ω j -
              Prim.Probability.meanVec d
                (Prim.Probability.condOn E.μ ((E.principalBoxData q hq).event E.Y I)) E.Y j) ∂
            Prim.Probability.condOn E.μ ((E.principalBoxData q hq).event E.Y I)) =
          (if j ∈ I then b else a) * E.profile.eigenvalue j)
    (hupper :
      ∀ I {j l : Prim.Idx d}, j < l →
        (∫ ω, (E.Y ω j -
              Prim.Probability.meanVec d
                (Prim.Probability.condOn E.μ ((E.principalBoxData q hq).event E.Y I)) E.Y j) *
            (E.Y ω l -
              Prim.Probability.meanVec d
                (Prim.Probability.condOn E.μ ((E.principalBoxData q hq).event E.Y I)) E.Y l) ∂
            Prim.Probability.condOn E.μ ((E.principalBoxData q hq).event E.Y I)) = 0) :
    PrincipalBoxCenteredIntegralDiagUpperFormula E q hq where
  diag :=
    PrincipalBoxCenteredIntegralDiagFormula.ofFormula
      a b hcoeff hdiag
  upper :=
    PrincipalBoxCenteredIntegralUpperFormula.ofFormula hupper

/-- Forget the upper formula and keep the trace-facing diagonal package. -/
noncomputable def toTraceFormulaData
    (D : PrincipalBoxCenteredIntegralDiagUpperFormula E q hq) :
    PrincipalBoxTraceFormulaData E q hq :=
  D.diag.toTraceFormulaData

/--
Build the centered-integral diagonal+upper formula package from a family of
diagonal preserved-covariance witnesses.

The integral formula object is definitionally the same covariance calculation
written without the named centered-product accessor, so the same diagonal
covariance source supplies both final analytic package shapes.
-/
noncomputable def ofDiagonalPreservedCovarianceFamily
    (a b : ℝ) (hcoeff : b - a ≤ 0)
    (D :
      ∀ I,
        (E.principalBoxData q hq).DiagonalPreservedCovariance E.μ E.Y I)
    (hdiagVal :
      ∀ I j, (D I).diagVal j =
        (if j ∈ I then b else a) * E.profile.eigenvalue j) :
    PrincipalBoxCenteredIntegralDiagUpperFormula E q hq :=
  ofFormula a b hcoeff
    (fun I j => by
      change
        (E.principalBoxData q hq).preservedCenteredProductMoment E.μ E.Y I j j =
          (if j ∈ I then b else a) * E.profile.eigenvalue j
      rw [← (E.principalBoxData q hq).preservedCov_eq_centeredProductMoment
        E.μ E.Y I j j]
      rw [(D I).diag_eq j, hdiagVal I j])
    (fun I {j l} hjl => by
      change
        (E.principalBoxData q hq).preservedCenteredProductMoment E.μ E.Y I j l = 0
      rw [← (E.principalBoxData q hq).preservedCov_eq_centeredProductMoment
        E.μ E.Y I j l]
      exact (D I).offDiag_eq_zero (ne_of_lt hjl))


end PrincipalBoxCenteredIntegralDiagUpperFormula

end EllipticalCore

end Prim.Elliptical
