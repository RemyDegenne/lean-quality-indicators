namespace OAI

noncomputable section

namespace LowSpaceSubsetSum

open scoped BigOperators symmDiff

attribute [local instance] Classical.propDecidable

namespace RepresentationSetup

variable {n : ℕ} (R : RepresentationSetup n)

theorem mixerSize_add_one_le_scale :
    (mixerSize n : ℝ) + 1 ≤ inputScale R.input := by
  have hm := Finset.card_le_univ (R.mixers 0)
  rw [R.card, Fintype.card_fin] at hm
  have hnat : mixerSize n + 1 ≤ inputScale R.input := by
    unfold inputScale
    omega
  exact_mod_cast hnat

end RepresentationSetup
end LowSpaceSubsetSum
end
end OAI
