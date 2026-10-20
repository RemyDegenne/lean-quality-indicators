@[expose] public section

noncomputable section

open CategoryTheory UnitriangularStageCoordinateRing

open scoped CategoryTheory CategoryTheory.MonObj

namespace AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false

variable (K : Type) [CommRing K] (n r : ℕ)

@[simp] theorem unitriangularStageCoordinateMap_π (hr : 1 ≤ r)
    (ij : Matrix.UnitriangularGroup.superdiagonalIndex n r) :
    unitriangularStageCoordinateMap K n r hr ≫
        Limits.Pi.π (fun _ : Matrix.UnitriangularGroup.superdiagonalIndex n r =>
          additiveGroupScheme K) ij =
      unitriangularStageCoordinateProjection K n r hr ij := by
  simp [unitriangularStageCoordinateMap]

end AlgebraicGeometry
end
end
