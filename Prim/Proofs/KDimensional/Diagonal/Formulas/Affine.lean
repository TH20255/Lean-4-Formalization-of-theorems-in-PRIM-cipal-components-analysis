import Prim.Proofs.KDimensional.Diagonal.Formulas.Witness

namespace Prim.Proofs

open scoped BigOperators
open Prim.Elliptical

namespace KDimensionalDiagonalProfile

variable {d : Nat} (P : KDimensionalDiagonalProfile d)

/--
The diagonal trace formula simplifies to an explicit affine function of the selected
eigenvalue sum:

  `preservedTraceOn q I = a * (∑ j, λ_j) + (b - a) * eigenSum I`

This makes the connection between the diagonal parameters `a`, `b` and the inherited
affine parameters `offset`, `coeff` from `KDimensionalProfile` explicit.
-/
theorem preservedTraceOn_eq_affine_eigenSum (I : Finset (Prim.Idx d)) :
    P.core.preservedTraceOn P.q I =
      P.a * ∑ j, P.core.profile.eigenvalue j + (P.b - P.a) * eigenSum P.core I := by
  rw [P.preservedTraceOn_eq_sum_coeffs I]
  simp_rw [show ∀ j : Prim.Idx d,
      (if j ∈ I then P.b else P.a) * P.core.profile.eigenvalue j =
        P.a * P.core.profile.eigenvalue j +
          (P.b - P.a) * if j ∈ I then P.core.profile.eigenvalue j else 0
      from fun j => by split_ifs <;> ring,
    Finset.sum_add_distrib, ← Finset.mul_sum]
  have hsum :
      (∑ j, if j ∈ I then P.core.profile.eigenvalue j else 0) =
        eigenSum P.core I := by
    rw [eigenSum]
    exact Finset.sum_ite_mem_eq I (fun j => P.core.profile.eigenvalue j)
  simp [hsum]

/--
The affine offset in a `KDimensionalDiagonalProfile` is determined by its diagonal
parameters: `offset = a * (∑ j, λ_j)`.
-/
theorem offset_eq_a_mul_totalTrace :
    P.offset = P.a * ∑ j, P.core.profile.eigenvalue j := by
  have h1 := P.trace_formula (∅ : Finset (Prim.Idx d))
  have h2 := P.preservedTraceOn_eq_affine_eigenSum (∅ : Finset (Prim.Idx d))
  simp only [eigenSum, Finset.sum_empty, mul_zero, add_zero] at h1 h2
  linarith

/--
The trace affine coefficient agrees with the diagonal parameter difference when
scaled by any eigenvalue sum:
`coeff * eigenSum I = (b - a) * eigenSum I`.

This is the coefficient companion to `offset_eq_a_mul_totalTrace`.
-/
theorem coeff_mul_eigenSum_eq (I : Finset (Prim.Idx d)) :
    P.coeff * eigenSum P.core I = (P.b - P.a) * eigenSum P.core I := by
  have h1 := P.trace_formula I
  have h2 := P.preservedTraceOn_eq_affine_eigenSum I
  have h3 := P.offset_eq_a_mul_totalTrace
  linarith

end KDimensionalDiagonalProfile
end Prim.Proofs
