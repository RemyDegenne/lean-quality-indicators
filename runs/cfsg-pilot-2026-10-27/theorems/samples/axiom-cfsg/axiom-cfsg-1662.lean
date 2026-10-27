public section

open CFSG.Open

namespace CFSG.RankThreeEvenClassification.Helpers

universe u v

theorem primeComplementCore_map_equiv {G : Type u} {otherGroup : Type v}
    [Group G] [Group otherGroup] [Finite G] [Finite otherGroup]
    (prime : ℕ) (hprime : prime.Prime) (equivalence : G ≃* otherGroup) :
    (primeComplementCore G prime).map equivalence.toMonoidHom = primeComplementCore otherGroup prime := by
  apply le_antisymm (primeComplementCore_map_le prime hprime equivalence)
  apply (Subgroup.map_le_map_iff_of_injective
    (f := equivalence.symm.toMonoidHom) equivalence.symm.injective).mp
  rw [subgroup_map_equiv_symm]
  exact primeComplementCore_map_le prime hprime equivalence.symm

end CFSG.RankThreeEvenClassification.Helpers
end
