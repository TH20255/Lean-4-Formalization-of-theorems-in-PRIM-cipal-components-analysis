import Prim.LinearAlgebra.MatrixMajorization.Fractional.KyFan.Upper
import Prim.LinearAlgebra.MatrixMajorization.Fractional.KyFan.Lower

namespace Prim.LinearAlgebra

namespace FractionalSelection

variable {d : Nat} (F : FractionalSelection d)

/-- Fractional Ky Fan sandwich for antitone ordered values. -/
theorem weightedSum_sandwich
    (w : Prim.Idx d → ℝ) (hanti : Antitone w) :
    trailingPartialSum d w F.k ≤ F.weightedSum w ∧
      F.weightedSum w ≤ leadingPartialSum d w F.k := by
  exact ⟨F.trailingPartialSum_le_weightedSum w hanti,
    F.weightedSum_le_leadingPartialSum w hanti⟩

end FractionalSelection

end Prim.LinearAlgebra
