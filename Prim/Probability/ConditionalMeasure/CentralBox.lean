import Prim.Probability.ConditionalMeasure.Basic
import Prim.Probability.QuantileBox.Event

open scoped BigOperators
open MeasureTheory

namespace Prim.Probability

namespace CentralBoxData

variable {Ω : Type*} [MeasurableSpace Ω] {d : Nat} (B : CentralBoxData d)

/-- The event-conditioned measure attached to a central box peeling event. -/
noncomputable def condMeasure (μ : Measure Ω) (X : Ω → Prim.Vec d)
    (I : Finset (Fin d)) : Measure Ω :=
  condOn μ (B.event X I)

/-- Expectation under the box-event conditioned measure. -/
noncomputable def condIntegral
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (μ : Measure Ω) (X : Ω → Prim.Vec d) (I : Finset (Fin d)) (f : Ω → E) : E :=
  condOnIntegral μ (B.event X I) f

@[simp] theorem condMeasure_eq (μ : Measure Ω) (X : Ω → Prim.Vec d)
    (I : Finset (Fin d)) :
    B.condMeasure μ X I = condOn μ (B.event X I) := by
  rfl

@[simp] theorem condIntegral_eq
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (μ : Measure Ω) (X : Ω → Prim.Vec d) (I : Finset (Fin d)) (f : Ω → E) :
    B.condIntegral μ X I f = condOnIntegral μ (B.event X I) f := by
  rfl

/-- Conditioned measures agree when the selected coordinate half-widths agree. -/
theorem condMeasure_congr (C : CentralBoxData d) (μ : Measure Ω)
    (X : Ω → Prim.Vec d) {I : Finset (Fin d)}
    (h : ∀ i ∈ I, B.q i = C.q i) :
    B.condMeasure μ X I = C.condMeasure μ X I := by
  unfold CentralBoxData.condMeasure
  rw [B.event_congr C X h]

/-- Conditioned measures agree when all coordinate half-widths agree. -/
theorem condMeasure_congr_all (C : CentralBoxData d) (μ : Measure Ω)
    (X : Ω → Prim.Vec d) (h : ∀ i, B.q i = C.q i) (I : Finset (Fin d)) :
    B.condMeasure μ X I = C.condMeasure μ X I :=
  B.condMeasure_congr C μ X (I := I) (fun i _hi => h i)

/-- Conditional integrals agree when the selected coordinate half-widths agree. -/
theorem condIntegral_congr
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (C : CentralBoxData d) (μ : Measure Ω) (X : Ω → Prim.Vec d)
    {I : Finset (Fin d)} (f : Ω → E)
    (h : ∀ i ∈ I, B.q i = C.q i) :
    B.condIntegral μ X I f = C.condIntegral μ X I f := by
  unfold CentralBoxData.condIntegral
  rw [B.event_congr C X h]

/-- Conditional integrals agree when all coordinate half-widths agree. -/
theorem condIntegral_congr_all
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (C : CentralBoxData d) (μ : Measure Ω) (X : Ω → Prim.Vec d)
    (h : ∀ i, B.q i = C.q i) (I : Finset (Fin d)) (f : Ω → E) :
    B.condIntegral μ X I f = C.condIntegral μ X I f :=
  B.condIntegral_congr C μ X (I := I) f (fun i _hi => h i)

@[simp] theorem condMeasure_apply (μ : Measure Ω) (X : Ω → Prim.Vec d)
    (I : Finset (Fin d)) (t : Set Ω) (ht : MeasurableSet t) :
    B.condMeasure μ X I t = (μ (t ∩ B.event X I)) / (μ (B.event X I)) := by
  simp [CentralBoxData.condMeasure, ht]

theorem condMeasure_inter_eq_self (μ : Measure Ω) (X : Ω → Prim.Vec d)
    (I : Finset (Fin d)) (hEvent : MeasurableSet (B.event X I)) :
    B.condMeasure μ X I = (B.condMeasure μ X I).restrict (B.event X I) := by
  simpa [CentralBoxData.condMeasure] using
    condOn_inter_eq_self (μ := μ) (s := B.event X I) hEvent

end CentralBoxData

end Prim.Probability
