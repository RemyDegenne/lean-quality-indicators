@[expose] public section

noncomputable section

namespace EulerLpBochnerRealization

open MeasureTheory Filter

open scoped ENNReal

variable {α β E : Type*} [MeasurableSpace α] [MeasurableSpace β]
  [NormedAddCommGroup E] {μ : Measure α} {ν : Measure β}

variable [SFinite ν]

theorem realization_ae (w : Lp (Lp E 2 ν) 2 μ) (f : α × β → E)
    (hf : AEStronglyMeasurable f (μ.prod ν))
    (hrep : ∀ᵐ x ∂μ, (w x : β → E) =ᵐ[ν] fun y => f (x, y)) :
    (realization w f hf hrep : α × β → E) =ᵐ[μ.prod ν] f :=
  (field_memLp w f hf hrep).coeFn_toLp

end EulerLpBochnerRealization
end
end
