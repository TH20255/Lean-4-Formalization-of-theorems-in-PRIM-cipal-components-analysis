import Prim.Basic

namespace Prim.Probability

open scoped BigOperators

/--
Data for the central inter-quantile box used by the peeling event.

The map `q` stores the nonnegative half-width in each coordinate.
-/
structure CentralBoxData (d : Nat) where
  alpha : Real
  q : Fin d → Real
  q_nonneg : ∀ i, 0 ≤ q i

namespace CentralBoxData

variable {d : Nat} (B : CentralBoxData d)

/-- Product of the coordinate half-widths over a selected index set. -/
def halfWidthProduct (I : Finset (Fin d)) : Real :=
  Finset.prod I (fun i => B.q i)

/-- Volume of the selected symmetric box in the chosen coordinate subspace. -/
def boxVolume (I : Finset (Fin d)) : Real :=
  (2 : Real) ^ I.card * B.halfWidthProduct I

theorem halfWidthProduct_empty :
    B.halfWidthProduct ∅ = 1 := by
  simp [CentralBoxData.halfWidthProduct]

theorem boxVolume_empty :
    B.boxVolume ∅ = 1 := by
  simp [CentralBoxData.boxVolume, CentralBoxData.halfWidthProduct]

theorem halfWidthProduct_singleton (i : Fin d) :
    B.halfWidthProduct ({i} : Finset (Fin d)) = B.q i := by
  simp [CentralBoxData.halfWidthProduct]

theorem boxVolume_singleton (i : Fin d) :
    B.boxVolume ({i} : Finset (Fin d)) = 2 * B.q i := by
  simp [CentralBoxData.boxVolume, CentralBoxData.halfWidthProduct]

/-- Explicit product formula for the selected box volume. -/
theorem boxVolume_eq_pow_mul_prod (I : Finset (Fin d)) :
    B.boxVolume I = (2 : Real) ^ I.card * Finset.prod I (fun i => B.q i) := by
  rfl

/-- Fixed-cardinality specialization of the selected box-volume formula. -/
theorem boxVolume_eq_fixedCard_pow_mul_prod {k : Nat} {I : Finset (Fin d)}
    (hI : I.card = k) :
    B.boxVolume I = (2 : Real) ^ k * Finset.prod I (fun i => B.q i) := by
  simp [CentralBoxData.boxVolume, CentralBoxData.halfWidthProduct, hI]

/-- Half-width products agree when the selected coordinate half-widths agree. -/
theorem halfWidthProduct_congr (C : CentralBoxData d) {I : Finset (Fin d)}
    (h : ∀ i ∈ I, B.q i = C.q i) :
    B.halfWidthProduct I = C.halfWidthProduct I := by
  unfold CentralBoxData.halfWidthProduct
  exact Finset.prod_congr rfl h

/-- Box volumes agree when the selected coordinate half-widths agree. -/
theorem boxVolume_congr (C : CentralBoxData d) {I : Finset (Fin d)}
    (h : ∀ i ∈ I, B.q i = C.q i) :
    B.boxVolume I = C.boxVolume I := by
  unfold CentralBoxData.boxVolume
  rw [B.halfWidthProduct_congr C h]

/-- Box volumes agree when all coordinate half-widths agree. -/
theorem boxVolume_congr_all (C : CentralBoxData d) (h : ∀ i, B.q i = C.q i)
    (I : Finset (Fin d)) :
    B.boxVolume I = C.boxVolume I :=
  B.boxVolume_congr C (I := I) (fun i _hi => h i)

end CentralBoxData

end Prim.Probability
