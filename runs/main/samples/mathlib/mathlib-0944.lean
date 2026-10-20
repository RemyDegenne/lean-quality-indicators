@[expose] public section

open Filter Set TopologicalSpace Function

open Filter Pointwise

open scoped Topology

universe u

namespace GroupFilterBasis

variable {G : Type u} [Group G] {B : GroupFilterBasis G}

@[to_additive]
theorem nhds_one_hasBasis (B : GroupFilterBasis G) :
    HasBasis (@nhds G B.topology 1) (fun V : Set G ↦ V ∈ B) id := by
  rw [B.nhds_one_eq]
  exact B.toFilterBasis.hasBasis

end GroupFilterBasis
end
