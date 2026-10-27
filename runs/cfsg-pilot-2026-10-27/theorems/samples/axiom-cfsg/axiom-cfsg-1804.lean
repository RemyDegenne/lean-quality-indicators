public section

namespace CFSG.Quasithin.EmptyFaithfulMultiple

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique

namespace InspectionData15418

variable {G : Type} [Group G] [Finite G] {I G₁ G₂ S T Z : Subgroup G}
  (d : InspectionData15418 I G₁ G₂ S T Z)

include d

theorem normal_of_index_two {K : Subgroup ↥I} (hK : CFSG.IsComponent K)
    (hidx : (K.map (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥I))).index = 2) : K.Normal := by
  set π := QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥I) with hπ
  have hN : (K.map π).Normal := Subgroup.normal_of_index_eq_two hidx
  refine Subgroup.normal_iff_map_conj_eq.mpr fun g => ?_
  set K' := K.map (MulAut.conj g).toMonoidHom with hK'
  have hK'c : CFSG.IsComponent K' := CFSG.LocalCores.isComponent_map_mulEquiv (MulAut.conj g) hK
  have hmap : K'.map π = K.map π := by
    have e : π.comp (MulAut.conj g).toMonoidHom = (MulAut.conj (π g)).toMonoidHom.comp π := by
      ext x
      simp [MulAut.conj_apply]
    rw [hK', Subgroup.map_map, e, ← Subgroup.map_map]
    exact Subgroup.Normal.map_conj_eq (H := K.map π) (π g)
  have heq : K' = K := by
    rcases CFSG.LocalCores.distinct_components_commute hK'c hK with h | h
    · exact h
    · exfalso
      have hc : ⁅K'.map π, K.map π⁆ = ⊥ := by rw [← Subgroup.map_commutator, h, Subgroup.map_bot]
      have hKc := d.isComponent_map_mk hK
      rw [hmap, Subgroup.isPerfect_iff.mp hKc.1.1] at hc
      exact (Subgroup.nontrivial_iff_ne_bot _).mp
        (CFSG.LocalCores.isQuasisimple_nontrivial hKc.1) hc
  exact heq

end InspectionData15418
end CFSG.Quasithin.EmptyFaithfulMultiple
end
