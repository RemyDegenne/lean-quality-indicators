@[expose] public section

open MeasureTheory ProbabilityTheory Finset Hypergraph

attribute [local instance] Classical.propDecidable

namespace LeanPool.AsymptoticTrianglePacking.Internal

variable {V : Type*} [DecidableEq V] [Fintype V] {Ω : Type*} [MeasureSpace Ω]
  [IsProbabilityMeasure (ℙ : Measure Ω)]

omit [Fintype V] [IsProbabilityMeasure (ℙ : Measure Ω)] in
theorem measurable_coverInd {H : Finset (Finset V)} {p : ℝ}
    (ρ : BernoulliRetention (Ω := Ω) H p) (u : V) : Measurable (coverInd ρ u) :=
  Measurable.ite (measurableSet_vertex_covered ρ u) measurable_const measurable_const

end LeanPool.AsymptoticTrianglePacking.Internal
end
