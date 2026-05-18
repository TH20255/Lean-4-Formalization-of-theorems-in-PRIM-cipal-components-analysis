import Prim.Elliptical.Core.BoxOps.Basic
import Prim.Proofs.KDimensional.Basic

namespace Prim.Proofs

open scoped BigOperators
open Prim.Elliptical

/--
Abstract `k`-dimensional peeling profile in the principal basis.

This packages the point in the proof where the preserved trace has been reduced
to an affine function of the sum of the eigenvalues over the peeled index set.
-/
structure KDimensionalProfile (d : Nat) where
  core : EllipticalCore d
  q : ℝ
  offset : ℝ
  coeff : ℝ
  coeff_nonpos : coeff ≤ 0
  trace_formula :
    ∀ I, core.preservedTraceOn q I = offset + coeff * eigenSum core I

namespace KDimensionalProfile

variable {d : Nat} (P : KDimensionalProfile d)

/--
If one peeled coordinate set has larger selected eigenvalue sum, then it
preserves no more trace than a set with smaller selected eigenvalue sum.
-/
theorem preservedTraceOn_le_of_eigenSum_le {I J : Finset (Prim.Idx d)}
    (hIJ : eigenSum P.core J ≤ eigenSum P.core I) :
    P.core.preservedTraceOn P.q I ≤ P.core.preservedTraceOn P.q J := by
  rw [P.trace_formula I, P.trace_formula J]
  have hMul : P.coeff * eigenSum P.core I ≤ P.coeff * eigenSum P.core J :=
    mul_le_mul_of_nonpos_left hIJ P.coeff_nonpos
  simpa [add_comm, add_left_comm, add_assoc] using add_le_add_left hMul P.offset

/--
Equivalent monotonicity statement with the hypotheses written in the more direct
order for optimization arguments.
-/
theorem preservedTraceOn_ge_of_eigenSum_ge {I J : Finset (Prim.Idx d)}
    (hIJ : eigenSum P.core I ≤ eigenSum P.core J) :
    P.core.preservedTraceOn P.q J ≤ P.core.preservedTraceOn P.q I := by
  exact P.preservedTraceOn_le_of_eigenSum_le hIJ

/-- Larger canonical leading sets preserve no more trace. -/
theorem preservedTraceOn_leadingIndexSet_anti_mono {k l : Nat} (hkl : k ≤ l) :
    P.core.preservedTraceOn P.q (Prim.LinearAlgebra.leadingIndexSet d l) ≤
      P.core.preservedTraceOn P.q (Prim.LinearAlgebra.leadingIndexSet d k) := by
  exact P.preservedTraceOn_ge_of_eigenSum_ge
    (eigenSum_le_of_subset P.core
      (Prim.LinearAlgebra.leadingIndexSet_subset_leadingIndexSet hkl))

/-- Larger canonical trailing sets preserve no more trace. -/
theorem preservedTraceOn_trailingIndexSet_anti_mono {k l : Nat} (hkl : k ≤ l) :
    P.core.preservedTraceOn P.q (Prim.LinearAlgebra.trailingIndexSet d l) ≤
      P.core.preservedTraceOn P.q (Prim.LinearAlgebra.trailingIndexSet d k) := by
  exact P.preservedTraceOn_ge_of_eigenSum_ge
    (eigenSum_le_of_subset P.core
      (Prim.LinearAlgebra.trailingIndexSet_subset_trailingIndexSet hkl))

end KDimensionalProfile

end Prim.Proofs
