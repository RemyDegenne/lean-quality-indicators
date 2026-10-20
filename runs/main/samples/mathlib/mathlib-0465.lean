public section

namespace MeasureTheory

open Set Measure Filter Function ENNReal

variable {α β : Type*} {m0 : MeasurableSpace α} [MeasurableSpace β] {μ : Measure α} {s : Set α}

section IsProbabilityMeasure

export MeasureTheory.IsProbabilityMeasure (measure_univ)

theorem IsProbabilityMeasure.ae_neBot [IsProbabilityMeasure μ] : NeBot (ae μ) := inferInstance

end IsProbabilityMeasure
end MeasureTheory
end
