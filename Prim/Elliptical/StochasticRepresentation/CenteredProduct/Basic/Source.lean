import Prim.Elliptical.StochasticRepresentation.FormulaSource.Source.Basic

/-!
Centered-product source package for the public stochastic-representation theorem.
-/

namespace Prim.Elliptical

open Prim.LinearAlgebra
open Prim.LinearAlgebra.DoublyStochasticKernel
open Prim.Proofs
open Prim.Proofs.CardinalOrderedValueKDimensionalRotationConExpProfile
open MeasureTheory
open scoped BigOperators

noncomputable section

/--
Centered-product moment source package for the public stochastic theorem.

This is the intended next source boundary for representation-side work: prove
the centered-product diagonal formula, the upper off-diagonal vanishing, and
the coefficient sign once; the stochastic constructor layer recovers the
integral branch internally.
-/
structure StochasticCenteredProductMomentSource (d : Nat) where
  diagonal : StochasticDiagonalProfile d
  k : Nat
  coeff_nonpos : diagonal.diagonal.b - diagonal.diagonal.a <= 0
  diag : CardinalRotatedPeelCenteredMomentDiagFormula diagonal.diagonal k
  upper : CardinalRotatedPeelCenteredMomentUpperFormula diagonal.diagonal k
  quantileSource : EllipticalCore.PrincipalCentralQuantileSource diagonal.core
  quantile_same_radius : diagonal.radius = quantileSource.radius

namespace StochasticCenteredProductMomentSource

variable {d : Nat}
variable (M : StochasticCenteredProductMomentSource d)

/-- Build the centered-product source directly from raw rotated-peeling formulas. -/
noncomputable def ofCenteredProductMoment
    (D : StochasticDiagonalProfile d) (k : Nat)
    (hcoeff : D.diagonal.b - D.diagonal.a <= 0)
    (hdiag :
      forall U I, I.card = k ->
        forall j,
          rotatedPeelCenteredProductMoment D.diagonal U I j j =
            orthogonalMatrixDiagonalTraceDiagVal D.diagonal U I j)
    (hupper :
      forall U I, I.card = k ->
        forall {j l : Prim.Idx d}, j < l ->
          rotatedPeelCenteredProductMoment D.diagonal U I j l = 0)
    (quantileSource : EllipticalCore.PrincipalCentralQuantileSource D.core)
    (same_radius : D.radius = quantileSource.radius) :
    StochasticCenteredProductMomentSource d where
  diagonal := D
  k := k
  coeff_nonpos := hcoeff
  diag := { formula := hdiag }
  upper := { formula := hupper }
  quantileSource := quantileSource
  quantile_same_radius := same_radius

/--
Build the centered-product source from formulas stated on the
stochastic-representation-coordinate rotated-peeling event.
-/
noncomputable def ofRepCenteredProductMoment
    (D : StochasticDiagonalProfile d) (k : Nat)
    (hcoeff : D.diagonal.b - D.diagonal.a <= 0)
    (hdiag :
      forall U I, I.card = k ->
        forall j,
          rotatedRepPeelCenteredProductMoment D.diagonal U I j j =
            orthogonalMatrixDiagonalTraceDiagVal D.diagonal U I j)
    (hupper :
      forall U I, I.card = k ->
        forall {j l : Prim.Idx d}, j < l ->
          rotatedRepPeelCenteredProductMoment D.diagonal U I j l = 0)
    (quantileSource : EllipticalCore.PrincipalCentralQuantileSource D.core)
    (same_radius : D.radius = quantileSource.radius) :
    StochasticCenteredProductMomentSource d :=
  ofCenteredProductMoment D k hcoeff
    (fun U I hI j => by
      rw [rotatedPeelCenteredProductMoment_eq_rep]
      exact hdiag U I hI j)
    (fun U I hI {j l} hjl => by
      rw [rotatedPeelCenteredProductMoment_eq_rep]
      exact hupper U I hI (j := j) (l := l) hjl)
    quantileSource same_radius

/--
Build the centered-product source from a principal-box diagonal covariance
family plus representation-event rotated moment formulas.

This constructor removes the duplicated coefficient-sign hypothesis: it is
inherited from the principal-box family used to build the shared stochastic
diagonal profile.
-/
noncomputable def ofPrincipalBoxDiagonalCovarianceFamilyRepCenteredProductMoment
    (core : EllipticalCore d) (q : Real) (hq : 0 <= q)
    (F : EllipticalCore.PrincipalBoxDiagonalCovarianceFamily core q hq)
    (k : Nat)
    (hdiag :
      let D := StochasticDiagonalProfile.ofPrincipalBoxDiagonalCovarianceFamily core q hq F
      forall U I, I.card = k ->
        forall j,
          rotatedRepPeelCenteredProductMoment D.diagonal U I j j =
            orthogonalMatrixDiagonalTraceDiagVal D.diagonal U I j)
    (hupper :
      let D := StochasticDiagonalProfile.ofPrincipalBoxDiagonalCovarianceFamily core q hq F
      forall U I, I.card = k ->
        forall {j l : Prim.Idx d}, j < l ->
          rotatedRepPeelCenteredProductMoment D.diagonal U I j l = 0)
    (quantileSource : EllipticalCore.PrincipalCentralQuantileSource core)
    (same_radius : q = quantileSource.radius) :
    StochasticCenteredProductMomentSource d := by
  let D := StochasticDiagonalProfile.ofPrincipalBoxDiagonalCovarianceFamily core q hq F
  exact
    ofRepCenteredProductMoment D k
      (by
        simpa [D] using
          StochasticDiagonalProfile.ofPrincipalBoxDiagonalCovarianceFamily_coeff_nonpos F)
      hdiag hupper quantileSource (by simpa [D] using same_radius)

/-- Convert the centered-product source package to the formula-block source. -/
noncomputable def toFormulaSource : StochasticFormulaSource d :=
  StochasticFormulaSource.ofCenteredProductMomentBlocks
    M.diagonal M.k M.coeff_nonpos M.diag M.upper
    M.quantileSource M.quantile_same_radius

/-- Convert the centered-product source to the final public stochastic source. -/
noncomputable def toRotationOptimalitySource :
    StochasticRotationOptimalitySource d :=
  M.toFormulaSource.toRotationOptimalitySource

end StochasticCenteredProductMomentSource

end

end Prim.Elliptical
