@[expose] public section

open MeasureTheory ProbabilityTheory Finset Hypergraph

attribute [local instance] Classical.propDecidable

namespace LeanPool.AsymptoticTrianglePacking.Internal

variable {V : Type*} [DecidableEq V] {Ω : Type*} [MeasureSpace Ω]
  [IsProbabilityMeasure (ℙ : Measure Ω)]

/-- The indicator that all vertices of `e` other than `v` survive the round. -/
noncomputable def safeIndicator {H : Finset (Finset V)} {p : ℝ}
    (ρ : BernoulliRetention (Ω := Ω) H p) (v : V) (e : Finset V) (ω : Ω) : ℝ :=
  if Disjoint (e.erase v) (covered (retainedSet H ρ ω)) then 1 else 0

end LeanPool.AsymptoticTrianglePacking.Internal
end
