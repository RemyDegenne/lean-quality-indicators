public section

namespace CFSG.RankThree.GF2n

open Module Polynomial

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]

theorem finrank_map_add_finrank_inf_ker (f : V →ₗ[K] V) (P : Submodule K V) :
    finrank K (P.map f) + finrank K ↥(P ⊓ LinearMap.ker f) = finrank K P := by
  have h := LinearMap.finrank_range_add_finrank_ker (f.domRestrict P)
  rw [LinearMap.range_domRestrict] at h
  have hk : LinearMap.ker (f.domRestrict P) = (LinearMap.ker f).comap P.subtype := by
    ext x
    simp
  rw [hk, ← Submodule.finrank_map_subtype_eq P, Submodule.map_comap_subtype] at h
  exact h

end CFSG.RankThree.GF2n
end
