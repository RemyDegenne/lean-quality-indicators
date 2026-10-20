public section

noncomputable section

open MeasureTheory ProbabilityTheory Set

open scoped ENNReal

namespace TauCeti

universe u v

variable {X : Type u} {Y : Type v} [MeasurableSpace X]
  {c c' : X × Y → ℝ≥0∞} {μ : Measure X} {T S : X → Y} {a : ℝ≥0∞}

variable [MeasurableSpace Y] {ν : Measure Y}

/-- `IsKantorovichOptimalTransportMap c μ ν T` says that `T` is a transport map from `μ` to `ν`
whose cost is the *Kantorovich* value of the pair. By `TauCeti.transportCost_le_mongeCost` this
is the stronger of the two optimality notions: such a map is a Monge minimizer,
`TauCeti.IsKantorovichOptimalTransportMap.isMongeMinimizer`, and it forces the two values to
agree. It is the conclusion of the existence theorems for optimal maps, which produce a map out
of an optimal plan. -/
structure IsKantorovichOptimalTransportMap (c : X × Y → ℝ≥0∞) (μ : Measure X) (ν : Measure Y)
    (T : X → Y) : Prop extends HasLaw T ν μ where
  /-- A Kantorovich-optimal transport map attains the Kantorovich value. -/
  transportMapCost_eq : transportMapCost c μ T = transportCost c μ ν

end TauCeti
end
end
