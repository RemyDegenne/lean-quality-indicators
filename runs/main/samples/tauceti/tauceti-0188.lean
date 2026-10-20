public section

open scoped DirectSum

namespace TauCeti.GradedLinearQuiver

universe u u' v v' w

variable (R : Type w) [CommRing R] (C : Type u) [GradedLinearQuiver.{u, v, w} R C]

variable {R C}

@[simp]
theorem homInclusion_mem_totalGrading_piece_iff {X Y : C} (n : ℤ) (f : homModule (R := R) X Y) :
    homInclusion X Y f ∈ (totalGrading R C).piece n ↔ f ∈ (grading (R := R) X Y).piece n := by
  refine ⟨fun h ↦ by simpa using homProjection_mem_piece h X Y, fun h ↦ ?_⟩
  rw [mem_totalGrading_piece_iff]
  intro X' Y'
  by_cases hXY : (X, Y) = (X', Y')
  · obtain ⟨rfl, rfl⟩ := Prod.ext_iff.1 hXY
    simpa using h
  · rw [homProjection_homInclusion_of_ne hXY]
    exact zero_mem _

end TauCeti.GradedLinearQuiver
end
