public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique B6

namespace E2

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem isBorelIn_top_subgroupOf {I S B : Subgroup G} (hS : IsSylowTwoOf S I)
    (hB : B = I ⊓ Subgroup.normalizer (S : Set G)) : IsBorelIn ⊤ (B.subgroupOf I) := by
  refine ⟨S.subgroupOf I, ⟨le_top, hS.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe hS.1).symm, ?_⟩,
    ?_⟩
  · have e1 : ((S.subgroupOf I).subgroupOf ⊤).index = (S.subgroupOf I).index :=
      Subgroup.relIndex_top_right _
    rw [e1]
    exact hS.2.2
  · rw [top_inf_eq, hB]
    ext y
    constructor
    · intro hy
      replace hy : (y : G) ∈ Subgroup.normalizer (S : Set G) := (Subgroup.mem_subgroupOf.mp hy).2
      rw [Subgroup.mem_normalizer_iff]
      intro z
      exact Subgroup.mem_normalizer_iff.mp hy z
    · intro hy
      show (y : G) ∈ I ⊓ Subgroup.normalizer (S : Set G)
      refine ⟨y.2, ?_⟩
      show (y : G) ∈ Subgroup.normalizer (S : Set G)
      rw [Subgroup.mem_normalizer_iff]
      intro z
      constructor
      · intro hz
        have hzI := hS.1 hz
        exact Subgroup.mem_subgroupOf.mp ((Subgroup.mem_normalizer_iff.mp hy ⟨z, hzI⟩).mp
          (Subgroup.mem_subgroupOf.mpr hz))
      · intro hz
        have hzI : z ∈ I := by
          have := I.mul_mem (I.mul_mem (I.inv_mem y.2) (hS.1 hz)) y.2
          simpa [mul_assoc] using this
        exact Subgroup.mem_subgroupOf.mp ((Subgroup.mem_normalizer_iff.mp hy ⟨z, hzI⟩).mpr
          (Subgroup.mem_subgroupOf.mpr hz))

end E2
end CFSG.Quasithin
end
