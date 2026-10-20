@[expose] public section

open MeasureTheory MeasurableSpace

open scoped MeasureTheory ENNReal

namespace ProbabilityTheory

variable {Ω ι : Type*}

@[inherit_doc ProbabilityTheory.CondIndepFun]
scoped[ProbabilityTheory] notation3 X:50 " ⟂ᵢ[" Z ", " hZ "; " μ "] " Y:50 =>
  ProbabilityTheory.CondIndepFun (MeasurableSpace.comap Z inferInstance) (Measurable.comap_le hZ)
  X Y μ

@[inherit_doc ProbabilityTheory.CondIndepFun]
scoped[ProbabilityTheory] notation3 X:50 " ⟂ᵢ[" Z ", " hZ "] " Y:50 =>
  ProbabilityTheory.CondIndepFun (MeasurableSpace.comap Z inferInstance) (Measurable.comap_le hZ)
  X Y volume

section FromMeasurableSpacesToSetsOfSets

variable {m' : MeasurableSpace Ω}
  {mΩ : MeasurableSpace Ω} [StandardBorelSpace Ω]
  {hm' : m' ≤ mΩ} {μ : Measure Ω} [IsFiniteMeasure μ]

theorem CondIndep.condIndepSets {s1 s2 : Set (Set Ω)}
    (h_indep : CondIndep m' (generateFrom s1) (generateFrom s2) hm' μ) :
    CondIndepSets m' hm' s1 s2 μ :=
  Kernel.Indep.indepSets h_indep

end FromMeasurableSpacesToSetsOfSets
end ProbabilityTheory
end
