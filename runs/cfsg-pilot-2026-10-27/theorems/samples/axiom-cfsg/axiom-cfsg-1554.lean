public section

namespace CFSG.ComponentClassification.GrSLit.L34Tw

open CFSG Subgroup CFSG.ComponentClassification.PSL3Four
  CFSG.ComponentClassification.UnbalancedLayer

namespace Map

variable {G : Type} [Group G] {M K : Subgroup G} {t : G}
  (φ : ↥(normalizer (K : Set G)) →* Equiv.Perm (Fin 42))

theorem phiG_mem_R (hφR : ∀ n, φ n ∈ R) (g : G) : phiG φ g ∈ R := by
  by_cases hg : g ∈ normalizer (K : Set G)
  · rw [phiG_of_mem φ hg]
    exact hφR _
  · rw [phiG_of_not_mem φ hg]
    exact R.one_mem

end Map
end CFSG.ComponentClassification.GrSLit.L34Tw
end
