@[expose] public section

open scoped ContDiff Manifold

open IsManifold Module

noncomputable section

namespace RS

universe u

variable {X : Type u} [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
  [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

variable {Y : Type u} [TopologicalSpace Y] [T2Space Y] [CompactSpace Y] [ConnectedSpace Y]
  [ChartedSpace ℂ Y] [IsManifold 𝓘(ℂ) ω Y]

theorem pullbackT_id : pullbackT (id : X → X) contMDiff_id = LinearMap.id := by
  unfold pullbackT
  rw [Form1.trace_id, LinearMap.dualMap_id]
  ext v i
  simp

end RS
end
end
