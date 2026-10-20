public section

open Finset Set

open scoped ENNReal NNReal

namespace MeasureTheory.VectorMeasure

variable {X V : Type*} {mX : MeasurableSpace X}

section Basic

variable [TopologicalSpace V] [ENormedAddCommMonoid V] [T2Space V]
  {μ ν : VectorMeasure X V} {s : Set X}

@[simp]
lemma ennrealVariation_apply (μ : VectorMeasure X V) {s : Set X} (hs : MeasurableSet s) :
    μ.ennrealVariation s = μ.variation s := Measure.toENNRealVectorMeasure_apply_measurable hs

end Basic
end MeasureTheory.VectorMeasure
end
