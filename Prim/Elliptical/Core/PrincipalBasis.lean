import Prim.Elliptical.Core.Base
import Prim.LinearAlgebra.PrincipalBasis.Core

open scoped BigOperators
open MeasureTheory

namespace Prim.Elliptical

namespace EllipticalCore

variable {d : Nat} (E : EllipticalCore d)

/-- The principal-coordinate profile packaged as `PrincipalBasisData`. -/
noncomputable def toPrincipalBasisData : Prim.LinearAlgebra.PrincipalBasisData d where
  eigenvalue := E.profile.eigenvalue
  lambda_nonneg := E.profile.lambda_nonneg
  lambda_antitone := E.profile.lambda_antitone
  basisMatrix := 1
  orthogonalBasis := True
  diagonalizesCovariance := True

@[simp] theorem toPrincipalBasisData_eigenvalue (i : Prim.Idx d) :
    E.toPrincipalBasisData.eigenvalue i = E.profile.eigenvalue i := by
  rfl

/-- Sum of the ordered principal eigenvalues selected by a finite index set. -/
def selectedEigenSum (I : Finset (Prim.Idx d)) : ℝ :=
  Finset.sum I (fun i => E.profile.eigenvalue i)

/-- Sum of the squared ordered principal eigenvalues selected by a finite index set. -/
def selectedEigenSqSum (I : Finset (Prim.Idx d)) : ℝ :=
  Finset.sum I (fun i => (E.profile.eigenvalue i) ^ (2 : Nat))

@[simp] theorem selectedEigenSum_eq_toPrincipalBasisData (I : Finset (Prim.Idx d)) :
    E.selectedEigenSum I = E.toPrincipalBasisData.selectedEigenSum I := by
  rfl

@[simp] theorem selectedEigenSqSum_eq_toPrincipalBasisData (I : Finset (Prim.Idx d)) :
    E.selectedEigenSqSum I = E.toPrincipalBasisData.selectedEigenSqSum I := by
  rfl

end EllipticalCore

end Prim.Elliptical
