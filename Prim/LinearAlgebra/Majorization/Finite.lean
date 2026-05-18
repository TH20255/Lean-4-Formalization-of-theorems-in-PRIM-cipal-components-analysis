import Prim.LinearAlgebra.Majorization.Canonical.FinEmbedding
import Prim.LinearAlgebra.Majorization.Canonical.PartialSums.Totals
import Mathlib.Tactic.Linarith

namespace Prim.LinearAlgebra

open scoped BigOperators

/--
Finite majorization upper bound for an antitone profile: among all `k`-element
subsets of `Fin d`, the first `k` indices maximize the selected sum.
-/
theorem sum_le_leadingPartialSum_of_card_eq {d k : Nat}
    (w : Prim.Idx d → ℝ) (hanti : Antitone w)
    {I : Finset (Prim.Idx d)} (hI : I.card = k) :
    Finset.sum I w ≤ leadingPartialSum d w k := by
  have hk : k ≤ d := by
    rw [← hI]
    simpa using Finset.card_le_card (Finset.subset_univ I)
  rw [sum_eq_sum_orderEmbOfFin w I hI, leadingPartialSum_eq_sum_fin w hk]
  exact Finset.sum_le_sum (fun i _hi =>
    hanti (castLE_le_orderEmbOfFin hk I hI i))

/--
Finite majorization lower bound for an antitone profile: among all `k`-element
subsets of `Fin d`, the last `k` indices minimize the selected sum.
-/
theorem trailingPartialSum_le_sum_of_card_eq {d k : Nat}
    (w : Prim.Idx d → ℝ) (hanti : Antitone w)
    {I : Finset (Prim.Idx d)} (hI : I.card = k) :
    trailingPartialSum d w k ≤ Finset.sum I w := by
  have hk : k ≤ d := by
    rw [← hI]
    simpa using Finset.card_le_card (Finset.subset_univ I)
  have hIc : (Iᶜ).card = d - k := by
    simp [Finset.card_compl, hI]
  have hcomp :
      Finset.sum Iᶜ w ≤ leadingPartialSum d w (d - k) :=
    sum_le_leadingPartialSum_of_card_eq w hanti hIc
  have hsplit :
      Finset.sum I w + Finset.sum Iᶜ w = Finset.sum (Finset.univ : Finset (Prim.Idx d)) w := by
    rw [← Finset.sum_union (f := w) (s₁ := I) (s₂ := Iᶜ) disjoint_compl_right,
      Finset.union_compl]
  have htotal :
      trailingPartialSum d w k + leadingPartialSum d w (d - k) =
        Finset.sum (Finset.univ : Finset (Prim.Idx d)) w :=
    trailingPartialSum_add_leadingPartialSum_sub_eq_total d w hk
  linarith

/--
Finite majorization sandwich theorem for antitone profiles: every `k`-element
selected sum lies between the trailing and leading canonical partial sums.
-/
theorem trailingPartialSum_le_sum_and_sum_le_leadingPartialSum_of_card_eq {d k : Nat}
    (w : Prim.Idx d → ℝ) (hanti : Antitone w)
    {I : Finset (Prim.Idx d)} (hI : I.card = k) :
    trailingPartialSum d w k ≤ Finset.sum I w ∧
      Finset.sum I w ≤ leadingPartialSum d w k := by
  exact ⟨trailingPartialSum_le_sum_of_card_eq w hanti hI,
    sum_le_leadingPartialSum_of_card_eq w hanti hI⟩

end Prim.LinearAlgebra
