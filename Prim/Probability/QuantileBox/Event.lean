import Prim.Probability.QuantileBox.Basic
import Mathlib.MeasureTheory.Measure.MeasureSpace

namespace Prim.Probability

open MeasureTheory

/--
Coordinate peeling event for the selected index set `I`.

This is the formal event corresponding to keeping only the points whose chosen
coordinates remain inside the symmetric box of half-widths `q`.
-/
def peelEvent {Ω : Type*} [MeasurableSpace Ω] (d : Nat) (X : Ω → Prim.Vec d)
    (q : Fin d → Real) (I : Finset (Fin d)) : Set Ω :=
  {ω | ∀ i ∈ I, |X ω i| ≤ q i}

@[simp] theorem mem_peelEvent {Ω : Type*} [MeasurableSpace Ω] (d : Nat)
    (X : Ω → Prim.Vec d) (q : Fin d → Real) (I : Finset (Fin d)) (ω : Ω) :
    ω ∈ peelEvent d X q I ↔ ∀ i ∈ I, |X ω i| ≤ q i := Iff.rfl

/-- Peeling events agree when the selected coordinate half-widths agree. -/
theorem peelEvent_congr {Ω : Type*} [MeasurableSpace Ω] (d : Nat)
    (X : Ω → Prim.Vec d) {q r : Fin d → Real} {I : Finset (Fin d)}
    (h : ∀ i ∈ I, q i = r i) :
    peelEvent d X q I = peelEvent d X r I := by
  ext ω
  constructor
  · intro hω i hi
    simpa [h i hi] using hω i hi
  · intro hω i hi
    simpa [h i hi] using hω i hi

/--
A map preserving the selected coordinate absolute values preserves the peeling
event.
-/
theorem peelEvent_preimage_eq_of_abs_apply_eq {Ω : Type*} [MeasurableSpace Ω]
    (d : Nat) (X : Ω → Prim.Vec d) (q : Fin d → Real)
    (I : Finset (Fin d)) (τ : Ω → Ω)
    (habs : ∀ ω i, i ∈ I → |X (τ ω) i| = |X ω i|) :
    Set.preimage τ (peelEvent d X q I) = peelEvent d X q I := by
  ext ω
  constructor
  · intro hω i hi
    simpa [habs ω i hi] using hω i hi
  · intro hω i hi
    simpa [habs ω i hi] using hω i hi

/--
Ambient a.e. selected-coordinate absolute-value preservation gives a.e.
preservation of the peeling event.
-/
theorem peelEvent_preimage_ae_eq_of_abs_ae {Ω : Type*} [MeasurableSpace Ω]
    (d : Nat) (μ : Measure Ω) (X : Ω → Prim.Vec d) (q : Fin d → Real)
    (I : Finset (Fin d)) (τ : Ω → Ω)
    (habs :
      ∀ᵐ ω ∂ μ, ∀ i, i ∈ I → |X (τ ω) i| = |X ω i|) :
    Filter.EventuallyEq (ae μ)
      (Set.preimage τ (peelEvent d X q I)) (peelEvent d X q I) := by
  filter_upwards [habs] with ω hω
  apply propext
  constructor
  · intro hmem i hi
    simpa [hω i hi] using hmem i hi
  · intro hmem i hi
    simpa [hω i hi] using hmem i hi

/--
Peeling event written using explicit lower and upper coordinate cutoffs.

This is the interval form produced by distributional quantile calculations
before one proves that the interval is symmetric around zero.
-/
def intervalPeelEvent {Ω : Type*} [MeasurableSpace Ω] (d : Nat)
    (X : Ω → Prim.Vec d) (lower upper : Fin d → Real)
    (I : Finset (Fin d)) : Set Ω :=
  {ω | ∀ i ∈ I, lower i ≤ X ω i ∧ X ω i ≤ upper i}

@[simp] theorem mem_intervalPeelEvent {Ω : Type*} [MeasurableSpace Ω] (d : Nat)
    (X : Ω → Prim.Vec d) (lower upper : Fin d → Real)
    (I : Finset (Fin d)) (ω : Ω) :
    ω ∈ intervalPeelEvent d X lower upper I ↔
      ∀ i ∈ I, lower i ≤ X ω i ∧ X ω i ≤ upper i := Iff.rfl

/-- A symmetric interval peeling event is the existing absolute-value peeling event. -/
theorem intervalPeelEvent_eq_peelEvent_of_symmetric {Ω : Type*} [MeasurableSpace Ω]
    (d : Nat) (X : Ω → Prim.Vec d)
    (lower upper q : Fin d → Real)
    (hlower : ∀ i, lower i = -q i) (hupper : ∀ i, upper i = q i)
    (I : Finset (Fin d)) :
    intervalPeelEvent d X lower upper I = peelEvent d X q I := by
  ext ω
  constructor
  · intro hω i hi
    have hbounds : -q i ≤ X ω i ∧ X ω i ≤ q i := by
      simpa [hlower i, hupper i] using hω i hi
    exact abs_le.mpr hbounds
  · intro hω i hi
    have hbounds : -q i ≤ X ω i ∧ X ω i ≤ q i := abs_le.mp (hω i hi)
    simpa [hlower i, hupper i] using hbounds

namespace CentralBoxData

variable {Ω : Type*} [MeasurableSpace Ω] {d : Nat} (B : CentralBoxData d)

/-- Peeling event attached to a central box. -/
def event (X : Ω → Prim.Vec d) (I : Finset (Fin d)) : Set Ω :=
  peelEvent d X B.q I

@[simp] theorem mem_event (X : Ω → Prim.Vec d) (I : Finset (Fin d)) (ω : Ω) :
    ω ∈ B.event X I ↔ ∀ i ∈ I, |X ω i| ≤ B.q i := by
  rfl

@[simp] theorem event_eq_peelEvent (X : Ω → Prim.Vec d) (I : Finset (Fin d)) :
    B.event X I = peelEvent d X B.q I := by
  rfl

/-- Central-box events agree when the selected coordinate half-widths agree. -/
theorem event_congr (C : CentralBoxData d) (X : Ω → Prim.Vec d) {I : Finset (Fin d)}
    (h : ∀ i ∈ I, B.q i = C.q i) :
    B.event X I = C.event X I := by
  exact peelEvent_congr d X h

/-- Central-box events agree when all coordinate half-widths agree. -/
theorem event_congr_all (C : CentralBoxData d) (X : Ω → Prim.Vec d)
    (h : ∀ i, B.q i = C.q i) (I : Finset (Fin d)) :
    B.event X I = C.event X I :=
  B.event_congr C X (I := I) (fun i _hi => h i)

/-- A map preserving selected coordinate absolute values preserves a central-box event. -/
theorem event_preimage_eq_of_abs_apply_eq
    (X : Ω → Prim.Vec d) (I : Finset (Fin d)) (τ : Ω → Ω)
    (habs : ∀ ω i, i ∈ I → |X (τ ω) i| = |X ω i|) :
    Set.preimage τ (B.event X I) = B.event X I := by
  exact peelEvent_preimage_eq_of_abs_apply_eq d X B.q I τ habs

/--
Ambient a.e. selected-coordinate absolute-value preservation gives a.e.
preservation of the central-box event.
-/
theorem event_preimage_ae_eq_of_abs_ae
    (μ : Measure Ω) (X : Ω → Prim.Vec d) (I : Finset (Fin d)) (τ : Ω → Ω)
    (habs :
      ∀ᵐ ω ∂ μ, ∀ i, i ∈ I → |X (τ ω) i| = |X ω i|) :
    Filter.EventuallyEq (ae μ)
      (Set.preimage τ (B.event X I)) (B.event X I) := by
  exact peelEvent_preimage_ae_eq_of_abs_ae d μ X B.q I τ habs

end CentralBoxData

end Prim.Probability
