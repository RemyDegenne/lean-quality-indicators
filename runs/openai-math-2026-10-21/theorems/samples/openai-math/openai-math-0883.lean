namespace OAI

noncomputable section

open MeasureTheory Filter Set

open scoped BigOperators Classical

namespace InvariantIsing

variable {Ω : Type*} [MeasurableSpace Ω]

lemma measurable_simpleFieldPositiveIndex (P : Measure Ω) [IsProbabilityMeasure P] (s : SimpleFunc Ω ℝ) :
    Measurable (simpleFieldPositiveIndex P s) :=
  (measurable_of_finite _).comp (measurable_simpleFieldIndex s)

end InvariantIsing
end
end OAI
