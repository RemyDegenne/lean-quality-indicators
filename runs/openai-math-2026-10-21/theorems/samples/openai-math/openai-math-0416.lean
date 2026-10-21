namespace OAI

noncomputable section

open Set Manifold Bundle Filter Function

open scoped ContDiff Topology

namespace CKSBoundarySurface

variable {M : Type*} [TopologicalSpace M] [ChartedSpace H3 M] [IsManifold I3 ∞ M]

omit [IsManifold I3 ∞ M] in
lemma lift_mem_ext_target [IsManifold I3 ∞ M] (x : M) {z : E2}
    (hz : liftHalf z ∈ (chartAt H3 x).target) :
    liftPlane z ∈ (extChartAt I3 x).target := by
  change liftPlane z ∈ ((chartAt H3 x).extend I3).target
  rw [OpenPartialHomeomorph.extend_target']
  exact ⟨liftHalf z,hz,rfl⟩

end CKSBoundarySurface
end
end OAI
