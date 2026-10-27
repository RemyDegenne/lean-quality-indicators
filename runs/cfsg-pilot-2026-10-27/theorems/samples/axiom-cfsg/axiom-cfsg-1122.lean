public section

open CFSG

namespace CFSG.BrauerThirdMainTheorem.Helpers

theorem block_subset_irr (m : Ideal BlocksAlgInt) {G : Type*} [Group G]
    {block : Set (G → ℂ)} (hblock : BlocksIsBlock m G block) : block ⊆ BlocksIrr G := by
  obtain ⟨character, _, rfl⟩ := hblock
  exact blockOf_subset_irr m G character

end CFSG.BrauerThirdMainTheorem.Helpers
end
