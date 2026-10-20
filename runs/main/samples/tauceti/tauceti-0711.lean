public section

namespace TauCeti

open ContCohomology

universe u

variable (p : ℕ) (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

@[simp]
theorem abelianizationProPMk_conj (V : Subgroup G) [V.Normal] (g : G) (v : V) :
    (g : G ⧸ V) • abelianizationProPMk p G V v =
      abelianizationProPMk p G V (MulAut.conjNormal g v) := by
  simp [abelianizationProPMk, TopologicalAbelianization.mk_smul_mk]

end TauCeti
end
