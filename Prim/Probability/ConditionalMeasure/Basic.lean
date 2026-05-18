import Prim.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Restrict
import Mathlib.Tactic.Linarith

open scoped BigOperators
open MeasureTheory

namespace Prim.Probability

/--
Conditioning a measure on an event by normalized restriction.

When `μ s = 0`, this returns the zero measure because `μ s` is inverted in
`ℝ≥0∞`.
-/
noncomputable def condOn {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (s : Set Ω) : Measure Ω :=
  (μ s)⁻¹ • μ.restrict s

@[simp] theorem condOn_empty {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) :
    condOn μ (∅ : Set Ω) = 0 := by
  simp [condOn]

@[simp] theorem condOn_apply {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (s t : Set Ω) (ht : MeasurableSet t) :
    condOn μ s t = (μ (t ∩ s)) / (μ s) := by
  simp [condOn, Measure.restrict_apply, ht, ENNReal.div_eq_inv_mul, mul_comm]

/-- Conditioning is unchanged by replacing the event with an a.e.-equal event. -/
theorem condOn_congr_set {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    {s t : Set Ω} (h : s =ᵐ[μ] t) :
    condOn μ s = condOn μ t := by
  unfold condOn
  rw [Measure.restrict_congr_set h, h.measure_eq]

/--
An ambient a.e. fact remains true after conditioning on any event.

This is the key bridge for using representation identities, which are usually
available `μ`-a.e., inside conditioned covariance and centered-moment
calculations.
-/
theorem ae_condOn_of_ae {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (s : Set Ω) {p : Ω → Prop} (h : ∀ᵐ ω ∂ μ, p ω) :
    ∀ᵐ ω ∂ condOn μ s, p ω := by
  unfold condOn
  exact Measure.ae_smul_measure (ae_restrict_of_ae h) ((μ s)⁻¹)

/-- A.e.-equal functions remain a.e.-equal after conditioning on any event. -/
theorem ae_eq_condOn_of_ae_eq {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (s : Set Ω) {E : Type*} {f g : Ω → E} (h : f =ᵐ[μ] g) :
    f =ᵐ[condOn μ s] g :=
  ae_condOn_of_ae μ s h

/-- A measure-preserving equivalence that preserves the conditioning event
also preserves the conditioned measure.

The event preservation is only required up to ambient a.e. equality.  This is
the standard way to move symmetries of the original distribution into
conditioned event calculations.
-/
theorem measurePreserving_condOn_of_measurePreserving_of_preimage_ae_eq
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (s : Set Ω)
    (τ : MeasurableEquiv Ω Ω) (hτ : MeasurePreserving τ μ μ)
    (hs : Filter.EventuallyEq (ae μ) (Set.preimage τ s) s) :
    MeasurePreserving τ (condOn μ s) (condOn μ s) where
  measurable := τ.measurable
  map_eq := by
    unfold condOn
    rw [Measure.map_smul]
    congr 1
    calc
      (μ.restrict s).map τ =
          (μ.restrict (Set.preimage τ s)).map τ := by
            rw [Measure.restrict_congr_set hs]
      _ = (μ.map τ).restrict s := by
            exact (τ.restrict_map μ s).symm
      _ = μ.restrict s := by
            rw [hτ.map_eq]

/-- A measure-preserving sign symmetry forces the integral of an odd real
function to vanish.

This is the reusable zero-mean bridge for later spherical symmetry arguments:
once a sign-flip measurable equivalence preserves the conditioned measure and
turns a coordinate integrand into its negative, no coordinate-specific integral
algebra remains.
-/
theorem integral_eq_zero_of_measurePreserving_comp_eq_neg
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (τ : MeasurableEquiv Ω Ω) (hτ : MeasurePreserving τ μ μ)
    (f : Ω → ℝ)
    (hodd :
      Filter.EventuallyEq (ae μ)
        (fun ω => f (τ ω)) (fun ω => - f ω)) :
    (∫ ω, f ω ∂ μ) = 0 := by
  have hcomp :
      (∫ ω, f (τ ω) ∂ μ) = ∫ ω, f ω ∂ μ :=
    hτ.integral_comp' f
  have hneg :
      (∫ ω, f (τ ω) ∂ μ) = ∫ ω, - f ω ∂ μ :=
    integral_congr_ae hodd
  rw [integral_neg] at hneg
  linarith

/-- Expectation under the event-conditioned measure. -/
noncomputable def condOnIntegral {Ω : Type*} [MeasurableSpace Ω]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (μ : Measure Ω) (s : Set Ω) (f : Ω → E) : E :=
  ∫ x, f x ∂ condOn μ s

/-- Conditional integrals are unchanged by replacing the event with an a.e.-equal event. -/
theorem condOnIntegral_congr_set {Ω : Type*} [MeasurableSpace Ω]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (μ : Measure Ω) {s t : Set Ω} (h : s =ᵐ[μ] t) (f : Ω → E) :
    condOnIntegral μ s f = condOnIntegral μ t f := by
  simp [condOnIntegral, condOn_congr_set μ h]

/-- The conditioned measure is supported inside the event. -/
theorem condOn_inter_eq_self {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (s : Set Ω) (hs : MeasurableSet s) :
    condOn μ s = (condOn μ s).restrict s := by
  ext t ht
  rw [Measure.restrict_apply ht]
  rw [condOn_apply (μ := μ) (s := s) (t := t) ht]
  rw [condOn_apply (μ := μ) (s := s) (t := t ∩ s) (ht.inter hs)]
  have hss : t ∩ s ∩ s = t ∩ s := by
    ext x
    simp
  rw [hss]

end Prim.Probability
