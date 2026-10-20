public section

open Function List

namespace TauCeti

variable {B G W : Type*} [Group G] [Group W]

section Relations

variable (M : CoxeterMatrix B)

@[simp]
theorem ArtinGroup.gen_zpow_eq_one_iff (i : B) (k : ℤ) :
    ArtinGroup.gen M i ^ k = 1 ↔ k = 0 := by
  refine ⟨fun h ↦ ?_, fun h ↦ by rw [h, zpow_zero]⟩
  have h₁ : ArtinGroup.exponentSum M (ArtinGroup.gen M i ^ k) = 1 := by rw [h, map_one]
  rw [map_zpow, ArtinGroup.exponentSum_gen] at h₁
  simpa using congrArg Multiplicative.toAdd h₁

end Relations
end TauCeti
end
