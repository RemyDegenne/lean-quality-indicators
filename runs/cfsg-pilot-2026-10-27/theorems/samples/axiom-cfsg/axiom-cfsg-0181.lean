open CFSG

noncomputable section

open scoped Pointwise

namespace CFSG.Section8

universe u v w

public theorem mem_subgroupImage_subgroupOf_iff
    {G : Type u} [Group G] (M : Subgroup G) (W : Subgroup M) (x : M) :
    x ∈ (Section4Scratch.subgroupImage M W).subgroupOf M ↔ x ∈ W := by
  rw [subgroupImage_subgroupOf_self_eq M W]

end CFSG.Section8
end
