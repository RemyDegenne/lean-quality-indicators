@[expose] public section

open Filter MeasureTheory ProbabilityTheory Set

open scoped ENNReal Topology

noncomputable section

namespace Grunbaum

section UniformCentroid

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasureSpace E] [BorelSpace E]
  [Measure.IsAddHaarMeasure (volume : Measure E)]

/-- Lebesgue volume restricted to `K` and normalized to total mass one. -/
def uniformVolume (K : Set E) : Measure E :=
  (volume K)⁻¹ • volume.restrict K

end UniformCentroid
end Grunbaum
end
end
