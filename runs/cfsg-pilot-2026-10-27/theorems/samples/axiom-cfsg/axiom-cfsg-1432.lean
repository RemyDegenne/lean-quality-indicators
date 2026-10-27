public section

open scoped BigOperators Classical

namespace CFSG.DihedralTIFusion

open Wreathed TwoRankLowerBound.Helpers

variable {G : Type} [Group G] {W : Subgroup G} {u : G}

theorem subgroupOf_normalizer_index_eq_two (hu2 : u * u = 1) (huW : u ∉ W)
    (hinvert : ∀ w ∈ W, u⁻¹ * w * u = w⁻¹)
    (hnormalizer : Subgroup.normalizer (W : Set G) = W ⊔ Subgroup.zpowers u) :
    (W.subgroupOf (Subgroup.normalizer (W : Set G))).index = 2 := by
  refine Subgroup.index_eq_two_iff_exists_notMem_and.mpr
    ⟨⟨u, mem_normalizer_of_eq_sup hnormalizer⟩, ?_, fun b => ?_⟩
  · rw [Subgroup.mem_subgroupOf]
    exact huW
  · simp only [Subgroup.mem_subgroupOf, Subgroup.coe_mul]
    exact (mem_or_mul_mem_of_mem_normalizer hu2 hinvert hnormalizer b.2).symm

end CFSG.DihedralTIFusion
end
