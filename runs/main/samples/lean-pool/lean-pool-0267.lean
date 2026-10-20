@[expose] public section

open scoped ContDiff Manifold

open Set Filter Topology IsManifold

noncomputable section

namespace RS

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
  [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

omit [T2Space X] [CompactSpace X] [ConnectedSpace X] in
theorem genericKernel_empty : genericKernel X (∅ : Finset X) = ⊤ := by
  ext η
  simp [mem_genericKernel]

end RS
end
end
