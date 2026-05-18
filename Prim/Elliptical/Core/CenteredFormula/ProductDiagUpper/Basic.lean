import Prim.Elliptical.Core.CenteredFormula.Diag.Product
import Prim.Elliptical.Core.CenteredFormula.Upper
import Prim.Probability.ConditionalCovariance.CentralBox.Core.Diagonal

open scoped BigOperators
open MeasureTheory

namespace Prim.Elliptical

namespace EllipticalCore

variable {d : Nat} (E : EllipticalCore d)

/--
Combined principal-box centered-product diagonal and upper-triangular formulas.

This is the compact analytic target for producing a diagonal covariance profile
from named centered-product moments.
-/
structure PrincipalBoxCenteredProductMomentDiagUpperFormula
    (E : EllipticalCore d) (q : ℝ) (hq : 0 ≤ q) where
  diag : PrincipalBoxCenteredProductMomentDiagFormula E q hq
  upper : PrincipalBoxCenteredProductMomentUpperFormula E q hq

namespace PrincipalBoxCenteredProductMomentDiagUpperFormula

variable {d : Nat} {E : EllipticalCore d} {q : ℝ} {hq : 0 ≤ q}

/-- Build the combined centered-product formula object from raw formulas. -/
noncomputable def ofFormula
    (a b : ℝ) (hcoeff : b - a ≤ 0)
    (hdiag :
      ∀ I j,
        (E.principalBoxData q hq).preservedCenteredProductMoment E.μ E.Y I j j =
          (if j ∈ I then b else a) * E.profile.eigenvalue j)
    (hupper :
      ∀ I {j l : Prim.Idx d}, j < l →
        (E.principalBoxData q hq).preservedCenteredProductMoment E.μ E.Y I j l = 0) :
    PrincipalBoxCenteredProductMomentDiagUpperFormula E q hq where
  diag :=
    PrincipalBoxCenteredProductMomentDiagFormula.ofFormula
      a b hcoeff hdiag
  upper :=
    PrincipalBoxCenteredProductMomentUpperFormula.ofFormula hupper

/-- Forget the upper formula and keep the trace-facing diagonal package. -/
noncomputable def toTraceFormulaData
    (D : PrincipalBoxCenteredProductMomentDiagUpperFormula E q hq) :
    PrincipalBoxTraceFormulaData E q hq :=
  D.diag.toTraceFormulaData

/--
Build the centered-product diagonal+upper formula package from a family of
diagonal preserved-covariance witnesses.

This is a shorter analytic landing point: a source proof may establish that
each principal-box conditional covariance matrix is diagonal with prescribed
entries, and this constructor turns that into the formula package consumed by
the rotation-optimality chain.
-/
noncomputable def ofDiagonalPreservedCovarianceFamily
    (a b : ℝ) (hcoeff : b - a ≤ 0)
    (D :
      ∀ I,
        (E.principalBoxData q hq).DiagonalPreservedCovariance E.μ E.Y I)
    (hdiagVal :
      ∀ I j, (D I).diagVal j =
        (if j ∈ I then b else a) * E.profile.eigenvalue j) :
    PrincipalBoxCenteredProductMomentDiagUpperFormula E q hq :=
  ofFormula a b hcoeff
    (fun I j => by
      rw [← (E.principalBoxData q hq).preservedCov_eq_centeredProductMoment
        E.μ E.Y I j j]
      rw [(D I).diag_eq j, hdiagVal I j])
    (fun I {j l} hjl => by
      rw [← (E.principalBoxData q hq).preservedCov_eq_centeredProductMoment
        E.μ E.Y I j l]
      exact (D I).offDiag_eq_zero (ne_of_lt hjl))


end PrincipalBoxCenteredProductMomentDiagUpperFormula

end EllipticalCore

end Prim.Elliptical
