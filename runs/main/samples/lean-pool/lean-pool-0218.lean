@[expose] public noncomputable section

open MeasureTheory

open scoped MeasureTheory

namespace AleksandrovDifferentiability

theorem prod_measure_diff_eq_zero_of_forall_ae_restrict_section₀
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ : Measure α} {ν : Measure β} [SFinite ν] {s G : Set (α × β)}
    (hs : MeasurableSet s) (hbad : NullMeasurableSet (s \ G) (μ.prod ν))
    (hsection : ∀ x : α, ∀ᵐ y ∂ν.restrict {y : β | (x, y) ∈ s}, (x, y) ∈ G) :
    μ.prod ν (s \ G) = 0 :=
  prod_measure_diff_eq_zero_of_ae_ae_restrict_section₀ hs hbad
    (Filter.Eventually.of_forall hsection)

end AleksandrovDifferentiability
end
