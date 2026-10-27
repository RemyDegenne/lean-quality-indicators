public section

open CFSG.Open

namespace CFSG.ComponentClassification.UniversalComponentBlock

theorem centralizing_image {G H : Type*} [Group G] [Group H]
    (equivalence : G ≃* H) (component : Subgroup G) (member : G)
    (hcentralizes : member ∈ Subgroup.centralizer (component : Set G)) :
    equivalence member ∈ Subgroup.centralizer (component.map equivalence.toMonoidHom : Set H) := by
  apply Subgroup.mem_centralizer_iff.mpr
  rintro other ⟨lift, hlift, rfl⟩
  exact (equivalence.toMonoidHom.map_mul lift member).symm.trans
    ((congrArg equivalence (Subgroup.mem_centralizer_iff.mp hcentralizes lift hlift)).trans
      (equivalence.toMonoidHom.map_mul member lift))

end CFSG.ComponentClassification.UniversalComponentBlock
end
