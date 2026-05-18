import Prim.Proofs.KDimensional.Diagonal.Base

namespace Prim.Proofs

open scoped BigOperators
open Prim.Elliptical

namespace KDimensionalDiagonalProfile

variable {d : Nat} (P : KDimensionalDiagonalProfile d)

/--
Box-event diagonal witness obtained from the generic `k`-dimensional diagonal
profile once the scalar half-width parameter is known to be nonnegative.
-/
def diagonal_witness_on (hq : 0 ≤ P.q) (I : Finset (Prim.Idx d)) :
    (P.core.principalBoxData P.q hq).DiagonalPreservedCovariance
      P.core.μ P.core.Y I where
  diagVal := (P.diagonal_witness I).diagVal
  diag_eq := by
    intro j
    change P.core.preservedCovOn P.q hq I j j = (P.diagonal_witness I).diagVal j
    rw [EllipticalCore.preservedCovOn_eq (E := P.core) P.q hq I]
    exact (P.diagonal_witness I).diag_eq j
  offDiag_eq_zero := by
    intro j k hjk
    change P.core.preservedCovOn P.q hq I j k = 0
    rw [EllipticalCore.preservedCovOn_eq (E := P.core) P.q hq I]
    exact (P.diagonal_witness I).offDiag_eq_zero hjk

/-- Explicit trace formula induced by the diagonal `k`-dimensional profile. -/
theorem preservedTraceOn_eq_sum_coeffs (I : Finset (Prim.Idx d)) :
    P.core.preservedTraceOn P.q I =
      Finset.sum Finset.univ (fun j => ((if j ∈ I then P.b else P.a) * P.core.profile.eigenvalue j)) := by
  calc
    P.core.preservedTraceOn P.q I
        = Prim.Probability.preservedTrace d P.core.μ (P.core.peelSetEvent P.q I) P.core.Y := by
            rfl
    _ = Finset.sum Finset.univ (fun j => (P.diagonal_witness I).diagVal j) := by
          exact (P.diagonal_witness I).preservedTrace_eq_sum_diagVal
    _ = Finset.sum Finset.univ (fun j => ((if j ∈ I then P.b else P.a) * P.core.profile.eigenvalue j)) := by
          refine Finset.sum_congr rfl ?_
          intro j hj
          exact P.diagonal_formula I j

/-- Box-event trace formula induced by the diagonal `k`-dimensional profile. -/
theorem preservedTraceOn_eq_sum_coeffs_on (hq : 0 ≤ P.q) (I : Finset (Prim.Idx d)) :
    P.core.preservedTraceOn P.q I =
      Finset.sum Finset.univ (fun j => ((if j ∈ I then P.b else P.a) * P.core.profile.eigenvalue j)) := by
  calc
    P.core.preservedTraceOn P.q I
        = (P.core.principalBoxData P.q hq).preservedTrace P.core.μ P.core.Y I := by
            rw [EllipticalCore.preservedTraceOn_eq (E := P.core) P.q hq I]
    _ = Finset.sum Finset.univ (fun j => (P.diagonal_witness_on hq I).diagVal j) := by
          exact (P.diagonal_witness_on hq I).preservedTrace_eq_sum_diagVal
    _ = Finset.sum Finset.univ (fun j => ((if j ∈ I then P.b else P.a) * P.core.profile.eigenvalue j)) := by
          refine Finset.sum_congr rfl ?_
          intro j hj
          exact P.diagonal_formula I j

end KDimensionalDiagonalProfile
end Prim.Proofs
