@[expose] public section

noncomputable section

universe u v w

open Function Set

open scoped Uniformity

namespace Metric

namespace Sigma

variable {ι : Type*} {E : ι → Type*} [∀ i, MetricSpace (E i)]

/-- A `Dist` instance on the disjoint union `Σ i, E i`.
We embed isometrically each factor, set the basepoints at distance 1, arbitrarily,
and say that the distance from `a` to `b` is the sum of the distances of `a` and `b` to
their respective basepoints, plus the distance 1 between the basepoints.
Since there is an arbitrary choice in this construction, it is not an instance by default. -/
@[instance_reducible]
def instDist : Dist (Σ i, E i) :=
  ⟨Sigma.dist⟩

end Sigma
end Metric
end
end
