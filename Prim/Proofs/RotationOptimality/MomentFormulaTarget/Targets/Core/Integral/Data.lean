import Prim.Proofs.RotationOptimality.MomentFormulaTarget.Targets.Core.Moment.Integral

/-!
Data object for compact centered-integral targets.
-/

open scoped BigOperators
open MeasureTheory

namespace Prim.Proofs
namespace CardinalOrderedValueKDimensionalRotationConExpProfile

open Prim.LinearAlgebra
open Prim.LinearAlgebra.DoublyStochasticKernel

variable {d : Nat}

/--
Integral-level version of `CardinalRotatedPeelCenteredMomentTarget`.

This is often the shape produced by probability calculations before replacing
the integral by the named centered product moment.
-/
structure CardinalRotatedPeelCenteredIntegralTarget (d : Nat) where
  diagonal : KDimensionalDiagonalProfile d
  k : Nat
  coeff_nonpos : diagonal.b - diagonal.a ≤ 0
  diag_formula :
    ∀ U I, I.card = k →
      ∀ j,
        rotatedPeelCenteredIntegral diagonal U I j j =
          orthogonalMatrixDiagonalTraceDiagVal diagonal U I j
  upper_formula :
    ∀ U I, I.card = k →
      ∀ {j l : Prim.Idx d}, j < l →
        rotatedPeelCenteredIntegral diagonal U I j l = 0

end CardinalOrderedValueKDimensionalRotationConExpProfile
end Prim.Proofs
