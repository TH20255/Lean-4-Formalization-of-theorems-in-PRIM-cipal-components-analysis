import Prim.Elliptical.Core.Base
import Prim.Probability.ConditionalCovariance.CentralBox.Core.Basic

open scoped BigOperators
open MeasureTheory

namespace Prim.Elliptical

namespace EllipticalCore

variable {d : Nat} (E : EllipticalCore d)

/--
Source-facing package for principal-box upper-triangular centered-product
vanishing.

The diagonal formula objects above control traces; this object records the
off-diagonal condition needed to build an actual diagonal covariance witness.
-/
structure PrincipalBoxCenteredProductMomentUpperFormula
    (E : EllipticalCore d) (q : ℝ) (hq : 0 ≤ q) where
  formula :
    ∀ I {j l : Prim.Idx d}, j < l →
      (E.principalBoxData q hq).preservedCenteredProductMoment E.μ E.Y I j l = 0

namespace PrincipalBoxCenteredProductMomentUpperFormula

variable {d : Nat} {E : EllipticalCore d} {q : ℝ} {hq : 0 ≤ q}

/-- Build the centered-product upper formula object from its raw formula. -/
noncomputable def ofFormula
    (hupper :
      ∀ I {j l : Prim.Idx d}, j < l →
        (E.principalBoxData q hq).preservedCenteredProductMoment E.μ E.Y I j l = 0) :
    PrincipalBoxCenteredProductMomentUpperFormula E q hq where
  formula := hupper

end PrincipalBoxCenteredProductMomentUpperFormula

/--
Source-facing package for principal-box upper-triangular centered-integral
vanishing.
-/
structure PrincipalBoxCenteredIntegralUpperFormula
    (E : EllipticalCore d) (q : ℝ) (hq : 0 ≤ q) where
  formula :
    ∀ I {j l : Prim.Idx d}, j < l →
      (∫ ω, (E.Y ω j -
            Prim.Probability.meanVec d
              (Prim.Probability.condOn E.μ ((E.principalBoxData q hq).event E.Y I)) E.Y j) *
          (E.Y ω l -
            Prim.Probability.meanVec d
              (Prim.Probability.condOn E.μ ((E.principalBoxData q hq).event E.Y I)) E.Y l) ∂
          Prim.Probability.condOn E.μ ((E.principalBoxData q hq).event E.Y I)) = 0

namespace PrincipalBoxCenteredIntegralUpperFormula

variable {d : Nat} {E : EllipticalCore d} {q : ℝ} {hq : 0 ≤ q}

/-- Build the centered-integral upper formula object from its raw formula. -/
noncomputable def ofFormula
    (hupper :
      ∀ I {j l : Prim.Idx d}, j < l →
        (∫ ω, (E.Y ω j -
              Prim.Probability.meanVec d
                (Prim.Probability.condOn E.μ ((E.principalBoxData q hq).event E.Y I)) E.Y j) *
            (E.Y ω l -
              Prim.Probability.meanVec d
                (Prim.Probability.condOn E.μ ((E.principalBoxData q hq).event E.Y I)) E.Y l) ∂
            Prim.Probability.condOn E.μ ((E.principalBoxData q hq).event E.Y I)) = 0) :
    PrincipalBoxCenteredIntegralUpperFormula E q hq where
  formula := hupper

end PrincipalBoxCenteredIntegralUpperFormula

end EllipticalCore

end Prim.Elliptical
