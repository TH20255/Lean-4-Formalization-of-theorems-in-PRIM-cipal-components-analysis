import Prim.Probability.ConditionalCovariance.Preserved.Core.Trace
import Prim.Probability.QuantileBox.Event
open scoped BigOperators Matrix
open MeasureTheory

/-!
Central-box preserved covariance, centered-product moment, and trace API.
-/

namespace Prim.Probability

namespace CentralBoxData

variable {Ω : Type*} [MeasurableSpace Ω] {d : Nat} (B : CentralBoxData d)
/-- Covariance after conditioning on a central-box peeling event. -/
noncomputable def preservedCov (μ : Measure Ω) (X : Ω → Prim.Vec d)
    (I : Finset (Fin d)) : Prim.Mat d :=
  Prim.Probability.preservedCov d μ (B.event X I) X

/-- Trace after conditioning on a central-box peeling event. -/
noncomputable def preservedTrace (μ : Measure Ω) (X : Ω → Prim.Vec d)
    (I : Finset (Fin d)) : ℝ :=
  Prim.Probability.preservedTrace d μ (B.event X I) X

@[simp] theorem preservedCov_eq (μ : Measure Ω) (X : Ω → Prim.Vec d)
    (I : Finset (Fin d)) :
    B.preservedCov μ X I = Prim.Probability.preservedCov d μ (B.event X I) X := by
  rfl

/-- Preserved covariances agree when the selected coordinate half-widths agree. -/
theorem preservedCov_congr (C : CentralBoxData d) (μ : Measure Ω)
    (X : Ω → Prim.Vec d) {I : Finset (Fin d)}
    (h : ∀ i ∈ I, B.q i = C.q i) :
    B.preservedCov μ X I = C.preservedCov μ X I := by
  unfold CentralBoxData.preservedCov
  rw [B.event_congr C X h]

/-- Preserved covariances agree when all coordinate half-widths agree. -/
theorem preservedCov_congr_all (C : CentralBoxData d) (μ : Measure Ω)
    (X : Ω → Prim.Vec d) (h : ∀ i, B.q i = C.q i) (I : Finset (Fin d)) :
    B.preservedCov μ X I = C.preservedCov μ X I :=
  B.preservedCov_congr C μ X (I := I) (fun i _hi => h i)

/-- Preserved covariance on a central-box event is symmetric. -/
theorem preservedCov_comm (μ : Measure Ω) (X : Ω → Prim.Vec d)
    (I : Finset (Fin d)) (i j : Prim.Idx d) :
    B.preservedCov μ X I i j = B.preservedCov μ X I j i :=
  Prim.Probability.preservedCov_comm d μ (B.event X I) X i j

/-- Centered product moment under a central-box conditioned measure. -/
noncomputable def preservedCenteredProductMoment
    (μ : Measure Ω) (X : Ω → Prim.Vec d) (I : Finset (Fin d))
    (i j : Prim.Idx d) : ℝ :=
  Prim.Probability.preservedCenteredProductMoment d μ (B.event X I) X i j

/-- Centered product moments agree when the selected coordinate half-widths agree. -/
theorem preservedCenteredProductMoment_congr
    (C : CentralBoxData d) (μ : Measure Ω) (X : Ω → Prim.Vec d)
    {I : Finset (Fin d)} (i j : Prim.Idx d)
    (h : ∀ k ∈ I, B.q k = C.q k) :
    B.preservedCenteredProductMoment μ X I i j =
      C.preservedCenteredProductMoment μ X I i j := by
  unfold CentralBoxData.preservedCenteredProductMoment
  rw [B.event_congr C X h]

/-- Centered product moments agree when all coordinate half-widths agree. -/
theorem preservedCenteredProductMoment_congr_all
    (C : CentralBoxData d) (μ : Measure Ω) (X : Ω → Prim.Vec d)
    (h : ∀ k, B.q k = C.q k) (I : Finset (Fin d)) (i j : Prim.Idx d) :
    B.preservedCenteredProductMoment μ X I i j =
      C.preservedCenteredProductMoment μ X I i j :=
  B.preservedCenteredProductMoment_congr C μ X (I := I) i j (fun k _hk => h k)

/-- A central-box preserved covariance entry is a centered product moment. -/
theorem preservedCov_eq_centeredProductMoment
    (μ : Measure Ω) (X : Ω → Prim.Vec d) (I : Finset (Fin d))
    (i j : Prim.Idx d) :
    B.preservedCov μ X I i j =
      B.preservedCenteredProductMoment μ X I i j := by
  rfl

@[simp] theorem preservedTrace_eq (μ : Measure Ω) (X : Ω → Prim.Vec d)
    (I : Finset (Fin d)) :
    B.preservedTrace μ X I = Prim.Probability.preservedTrace d μ (B.event X I) X := by
  rfl

/-- Preserved traces agree when the selected coordinate half-widths agree. -/
theorem preservedTrace_congr (C : CentralBoxData d) (μ : Measure Ω)
    (X : Ω → Prim.Vec d) {I : Finset (Fin d)}
    (h : ∀ i ∈ I, B.q i = C.q i) :
    B.preservedTrace μ X I = C.preservedTrace μ X I := by
  unfold CentralBoxData.preservedTrace
  rw [B.event_congr C X h]

/-- Preserved traces agree when all coordinate half-widths agree. -/
theorem preservedTrace_congr_all (C : CentralBoxData d) (μ : Measure Ω)
    (X : Ω → Prim.Vec d) (h : ∀ i, B.q i = C.q i) (I : Finset (Fin d)) :
    B.preservedTrace μ X I = C.preservedTrace μ X I :=
  B.preservedTrace_congr C μ X (I := I) (fun i _hi => h i)

@[simp] theorem preservedTrace_eq_sum_diag (μ : Measure Ω) (X : Ω → Prim.Vec d)
    (I : Finset (Fin d)) :
    B.preservedTrace μ X I = ∑ i, B.preservedCov μ X I i i := by
  simpa [CentralBoxData.preservedTrace, CentralBoxData.preservedCov] using
    (Prim.Probability.preservedTrace_eq_sum_diag d μ (B.event X I) X)


end CentralBoxData

end Prim.Probability
