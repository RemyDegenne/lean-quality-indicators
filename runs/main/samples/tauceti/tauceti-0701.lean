public section

open ValuativeRel IsLocalRing IsNonarchimedeanLocalField

namespace TauCeti

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]

@[simp]
theorem natCard_squareClassGroup_of_isUnit_two (h2 : IsUnit (2 : 𝒪[K])) :
    Nat.card (SquareClassGroup K) = 4 := by
  rw [← natCard_multiplicativeSquareClassGroup]
  exact card_squareClass_of_odd h2

end TauCeti
end
