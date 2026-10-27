public section

namespace CFSG.StandardType

namespace LayerCores

open CFSG.Assembly

section Prod

variable {G₁ G₂ : Type*} [Group G₁] [Group G₂]

theorem iSup_prodFamily {β₁ β₂ : Type} (S₁ : β₁ → Subgroup G₁) (S₂ : β₂ → Subgroup G₂) :
    (⨆ c, prodFamily S₁ S₂ c) = (⨆ c, S₁ c).prod (⨆ c, S₂ c) := by
  rw [prodFamily, iSup_sum]
  simp only [Sum.elim_inl, Sum.elim_inr]
  rw [← Subgroup.map_iSup, ← Subgroup.map_iSup]
  refine le_antisymm (sup_le ?_ ?_) (Subgroup.prod_le_iff.mpr ⟨le_sup_left, le_sup_right⟩)
  · rintro _ ⟨x, hx, rfl⟩
    exact Subgroup.mem_prod.mpr ⟨hx, Subgroup.one_mem _⟩
  · rintro _ ⟨x, hx, rfl⟩
    exact Subgroup.mem_prod.mpr ⟨Subgroup.one_mem _, hx⟩

end Prod
end LayerCores
end CFSG.StandardType
end
