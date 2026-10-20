public section

namespace MeasureTheory

open Set Measure Filter TopologicalSpace

variable {α : Type*} {m0 : MeasurableSpace α} {μ : Measure α} {s : Set α}

export MeasureTheory.NullSingletonClass (measure_singleton)

variable [NullSingletonClass μ]

theorem _root_.Set.Subsingleton.measure_zero (hs : s.Subsingleton) (μ : Measure α)
    [NullSingletonClass μ] :
    μ s = 0 :=
  hs.induction_on (p := fun s => μ s = 0) measure_empty measure_singleton

end MeasureTheory
end
