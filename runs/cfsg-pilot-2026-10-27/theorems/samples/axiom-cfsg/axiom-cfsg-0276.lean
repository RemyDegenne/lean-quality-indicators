public section

namespace CFSG.Quasithin.H13.F431.L3

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Open

section Img

variable {X G : Type} [Group X] [Group G] {N : Subgroup X} (b : ↥N →* G)

theorem subImg_le_range (Y : Subgroup X) : subImg b Y ≤ b.range := fun g hg => by
  obtain ⟨x, hx, -, rfl⟩ := mem_subImg.mp hg
  exact ⟨⟨x, hx⟩, rfl⟩

end Img
end CFSG.Quasithin.H13.F431.L3
end
