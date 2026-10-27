@[expose] public section

open scoped ContDiff Manifold Topology

open Set TopologicalSpace Filter

namespace RS.Cech

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

variable [T2Space X] [CompactSpace X]

/-- Support of the difference divisor, as a `Finset` (compactness). -/
noncomputable def diffSupp (D D' : RS.Divisor X) : Finset X :=
  ((D - D').finiteSupport isCompact_univ).toFinset

end RS.Cech
end
