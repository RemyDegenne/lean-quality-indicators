public section

namespace CFSG.EvenSporadicStandard.HSStd.Zassenhaus

open Subgroup Wreath

variable {G : Type*} [Group G]

namespace PairData

variable {P K : Subgroup G} {t : G} (h : PairData P K t)

include h

theorem rho_mem_baseSubgroup_iff (p : ↥P) :
    h.rho p ∈ baseSubgroup ↔ K.map (MulAut.conj (p : G)).toMonoidHom = K := by
  by_cases hp : (p : G) ∈ normalizer (K : Set G)
  · rw [rho_apply, h.rhoFun_of_normalizes p hp, mem_baseSubgroup_iff, swapChar_base]
    exact iff_of_true rfl ((mem_normalizer_iff_map_eq K _).1 hp)
  · rw [rho_apply, h.rhoFun_of_not_normalizes p hp, mem_baseSubgroup_iff, map_mul,
      swapChar_base, one_mul, swapChar_tau]
    exact iff_of_false (by decide) (fun hm => hp ((mem_normalizer_iff_map_eq K _).2 hm))

end PairData
end CFSG.EvenSporadicStandard.HSStd.Zassenhaus
end
