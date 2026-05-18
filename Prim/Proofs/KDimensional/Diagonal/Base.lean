import Prim.Proofs.KDimensional.Core.Base.Basic
import Prim.Probability.ConditionalCovariance.CentralBox.UpperConstructors

namespace Prim.Proofs

open scoped BigOperators
open Prim.Elliptical

structure KDimensionalDiagonalProfile (d : Nat) extends KDimensionalProfile d where
  a : ℝ
  b : ℝ
  diagonal_witness :
    ∀ I, Prim.Probability.DiagonalPreservedCovariance d core.μ (core.peelSetEvent q I) core.Y
  diagonal_formula :
    ∀ I j, (diagonal_witness I).diagVal j =
      (if j ∈ I then b else a) * core.profile.eigenvalue j

namespace KDimensionalDiagonalProfile

variable {d : Nat} (P : KDimensionalDiagonalProfile d)

/--
Construct a diagonal `k`-dimensional profile directly from box-event diagonal
covariance witnesses on the principal box data.

This is the natural packaging step once future analytic work has identified the
conditioned covariance matrix on each peeled coordinate set inside the
principal-box interface.
-/
noncomputable def ofBoxDiagonalWitness
    (base : KDimensionalProfile d) (a b : ℝ) (hq : 0 ≤ base.q)
    (hdiag :
      ∀ I,
        (base.core.principalBoxData base.q hq).DiagonalPreservedCovariance
          base.core.μ base.core.Y I)
    (hformula :
      ∀ I j, (hdiag I).diagVal j =
        (if j ∈ I then b else a) * base.core.profile.eigenvalue j) :
    KDimensionalDiagonalProfile d where
  core := base.core
  q := base.q
  offset := base.offset
  coeff := base.coeff
  coeff_nonpos := base.coeff_nonpos
  trace_formula := base.trace_formula
  a := a
  b := b
  diagonal_witness := fun I =>
    Prim.Probability.CentralBoxData.DiagonalPreservedCovariance.toGeneric
      (B := base.core.principalBoxData base.q hq) (hdiag I)
  diagonal_formula := by
    intro I j
    exact hformula I j

/--
Construct a diagonal `k`-dimensional profile directly from box-conditioned
named centered product moments and upper-triangular vanishing.

This is a closer landing point for future analytic proofs than
`ofBoxDiagonalWitness`, because it avoids a manual witness-packaging step.
-/
noncomputable def ofBoxCenteredProductMomentAndUpperCenteredProductMoment
    (base : KDimensionalProfile d) (a b : ℝ) (hq : 0 ≤ base.q)
    (hdiag :
      ∀ I j,
        (base.core.principalBoxData base.q hq).preservedCenteredProductMoment
          base.core.μ base.core.Y I j j =
            (if j ∈ I then b else a) * base.core.profile.eigenvalue j)
    (hupper :
      ∀ I {j l : Prim.Idx d}, j < l →
        (base.core.principalBoxData base.q hq).preservedCenteredProductMoment
          base.core.μ base.core.Y I j l = 0) :
    KDimensionalDiagonalProfile d :=
  let B := base.core.principalBoxData base.q hq
  ofBoxDiagonalWitness base a b hq
    (fun I =>
      B.diagonalPreservedCovarianceOfCenteredProductMomentAndUpperCenteredProductMoment
        base.core.μ base.core.Y I
        (fun j => (if j ∈ I then b else a) * base.core.profile.eigenvalue j)
        (hdiag I) (hupper I))
    (by
      intro I j
      rfl)

/--
Construct a diagonal `k`-dimensional profile directly from raw box-conditioned
centered integral formulas and upper-triangular vanishing.
-/
noncomputable def ofBoxCenteredIntegralAndUpperCenteredIntegral
    (base : KDimensionalProfile d) (a b : ℝ) (hq : 0 ≤ base.q)
    (hdiag :
      ∀ I j,
        (∫ ω,
            (base.core.Y ω j -
                Prim.Probability.meanVec d
                  (Prim.Probability.condOn base.core.μ
                    ((base.core.principalBoxData base.q hq).event base.core.Y I))
                  base.core.Y j) *
              (base.core.Y ω j -
                Prim.Probability.meanVec d
                  (Prim.Probability.condOn base.core.μ
                    ((base.core.principalBoxData base.q hq).event base.core.Y I))
                  base.core.Y j)
          ∂ Prim.Probability.condOn base.core.μ
              ((base.core.principalBoxData base.q hq).event base.core.Y I)) =
          (if j ∈ I then b else a) * base.core.profile.eigenvalue j)
    (hupper :
      ∀ I {j l : Prim.Idx d}, j < l →
        (∫ ω,
            (base.core.Y ω j -
                Prim.Probability.meanVec d
                  (Prim.Probability.condOn base.core.μ
                    ((base.core.principalBoxData base.q hq).event base.core.Y I))
                  base.core.Y j) *
              (base.core.Y ω l -
                Prim.Probability.meanVec d
                  (Prim.Probability.condOn base.core.μ
                    ((base.core.principalBoxData base.q hq).event base.core.Y I))
                  base.core.Y l)
          ∂ Prim.Probability.condOn base.core.μ
              ((base.core.principalBoxData base.q hq).event base.core.Y I)) = 0) :
    KDimensionalDiagonalProfile d :=
  let B := base.core.principalBoxData base.q hq
  ofBoxDiagonalWitness base a b hq
    (fun I =>
      B.diagonalPreservedCovarianceOfCenteredIntegralAndUpperCenteredIntegral
        base.core.μ base.core.Y I
        (fun j => (if j ∈ I then b else a) * base.core.profile.eigenvalue j)
        (hdiag I) (hupper I))
    (by
      intro I j
      rfl)

end KDimensionalDiagonalProfile
end Prim.Proofs
