public section

namespace DoubleCoset

variable {G : Type*} [Group G]

@[simp]
theorem quotientMapOfLELeft_refl (H K : Subgroup G) :
    quotientMapOfLELeft (le_refl H) K = id := by
  funext q
  induction q using Quotient.inductionOn' with
  | h g => rw [quotientMapOfLELeft_apply_mk]; rfl

end DoubleCoset
end
