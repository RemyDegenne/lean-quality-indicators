public section

open Filter Function Set Topology

open scoped Manifold

namespace TauCeti.RiemannSurface.FiniteHolomorphicMap

variable {X Y : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
  [TopologicalSpace Y] [ChartedSpace ℂ Y]

variable [IsManifold 𝓘(ℂ) 1 X] [IsManifold 𝓘(ℂ) 1 Y] [PreconnectedSpace X]

-- Simplify nonmembership before `mem_branchValues_iff` rewrites the inner membership.
@[simp↓]
theorem notMem_branchValues_iff (f : FiniteHolomorphicMap X Y) (y : Y) :
    y ∉ f.branchValues ↔ ∀ x, f x = y → localMultiplicity f x = 1 := by
  rw [mem_branchValues_iff]
  simp only [not_exists, not_and]
  exact forall_congr' fun x ↦ imp_congr_right fun _ ↦ by
    have := localMultiplicity_pos f x
    omega

end TauCeti.RiemannSurface.FiniteHolomorphicMap
end
