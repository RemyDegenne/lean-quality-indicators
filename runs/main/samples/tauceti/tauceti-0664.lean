public noncomputable section

universe u

open CategoryTheory Limits

namespace TauCeti.AugmentationIdeal

open _root_.Rep

variable (k G : Type u) [CommRing k] [Group G]

@[simp]
theorem singleSub_one (a : k) : singleSub k G a (1 : G) = 0 := by
  apply augmentationι_injective k G
  rw [ι_singleSub, sub_self, map_zero]

end TauCeti.AugmentationIdeal
end
