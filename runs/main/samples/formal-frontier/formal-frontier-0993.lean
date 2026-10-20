@[expose] public section

noncomputable section

open CategoryTheory GeneralLinearCoordinateRing UnitriangularCoordinateRing

open scoped CategoryTheory MonObj TensorProduct

namespace AlgebraicGeometry

variable (K : Type) [CommRing K] (n r : ℕ)

open UnitriangularStageCoordinateRing

set_option backward.isDefEq.respectTransparency false

theorem unitriangularStageSuccessor_inclusion :
    unitriangularStageSuccessor K n r ≫ unitriangularStageInclusion K n r =
      unitriangularStageInclusion K n (r + 1) := by
  unfold unitriangularStageSuccessor unitriangularStageInclusion
  rw [← Functor.map_comp]
  congr 1

end AlgebraicGeometry
end
end
