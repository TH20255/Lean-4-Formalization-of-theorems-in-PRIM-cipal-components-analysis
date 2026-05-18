import Prim.Proofs.RotationOptimality.MomentFormulaTarget.Targets.Core.Integral.Data
import Prim.Proofs.RotationOptimality.MomentFormulaTarget.Targets.Core.Moment.Data

/-!
Conversions between raw centered-integral and named centered-moment targets.
-/

open scoped BigOperators
open MeasureTheory

namespace Prim.Proofs
namespace CardinalOrderedValueKDimensionalRotationConExpProfile

open Prim.LinearAlgebra
open Prim.LinearAlgebra.DoublyStochasticKernel

variable {d : Nat}

namespace CardinalRotatedPeelCenteredIntegralTarget

variable (T : CardinalRotatedPeelCenteredIntegralTarget d)

/-- Integral formulas give the compact named centered-product-moment target. -/
noncomputable def toCenteredMomentTarget :
    CardinalRotatedPeelCenteredMomentTarget d where
  diagonal := T.diagonal
  k := T.k
  coeff_nonpos := T.coeff_nonpos
  diag_formula := by
    intro U I hI j
    rw [← rotatedPeelCenteredIntegral_eq_centeredProductMoment]
    exact T.diag_formula U I hI j
  upper_formula := by
    intro U I hI j l hjl
    rw [← rotatedPeelCenteredIntegral_eq_centeredProductMoment]
    exact T.upper_formula U I hI hjl

end CardinalRotatedPeelCenteredIntegralTarget

namespace CardinalRotatedPeelCenteredMomentTarget

variable (T : CardinalRotatedPeelCenteredMomentTarget d)

/-- The named centered-moment target can also be viewed as a raw integral target. -/
noncomputable def toCenteredIntegralTarget :
    CardinalRotatedPeelCenteredIntegralTarget d where
  diagonal := T.diagonal
  k := T.k
  coeff_nonpos := T.coeff_nonpos
  diag_formula := by
    intro U I hI j
    rw [rotatedPeelCenteredIntegral_eq_centeredProductMoment]
    exact T.diag_formula U I hI j
  upper_formula := by
    intro U I hI j l hjl
    rw [rotatedPeelCenteredIntegral_eq_centeredProductMoment]
    exact T.upper_formula U I hI hjl

/-- Converting to raw integrals and back is extensionally the same target data. -/
theorem toCenteredIntegralTarget_toCenteredMomentTarget :
    T.toCenteredIntegralTarget.toCenteredMomentTarget = T := by
  cases T
  rfl

end CardinalRotatedPeelCenteredMomentTarget

end CardinalOrderedValueKDimensionalRotationConExpProfile
end Prim.Proofs
