public section

namespace CFSG.QuasithinUnique

open CFSG.Open CFSG.Quasithin

section Norm

variable {G : Type} [Group G]

theorem commutator_sup_sup_eq_bot' {A B C D : Subgroup G} (h1 : ⁅A, C⁆ = ⊥) (h2 : ⁅A, D⁆ = ⊥)
    (h3 : ⁅B, C⁆ = ⊥) (h4 : ⁅B, D⁆ = ⊥) : ⁅A ⊔ B, C ⊔ D⁆ = ⊥ := by
  rw [Subgroup.commutator_eq_bot_iff_le_centralizer] at h1 h2 h3 h4 ⊢
  refine sup_le ?_ ?_
  · rw [Subgroup.le_centralizer_iff]
    exact sup_le (Subgroup.le_centralizer_iff.mp h1) (Subgroup.le_centralizer_iff.mp h2)
  · rw [Subgroup.le_centralizer_iff]
    exact sup_le (Subgroup.le_centralizer_iff.mp h3) (Subgroup.le_centralizer_iff.mp h4)

end Norm
end CFSG.QuasithinUnique
end
