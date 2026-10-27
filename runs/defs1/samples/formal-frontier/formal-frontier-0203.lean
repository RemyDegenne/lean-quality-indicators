@[expose] public section

noncomputable section

open CategoryTheory Algebra.TensorProduct

open scoped CategoryTheory MonObj TensorProduct MonoidalCategory

namespace AlgebraicGeometry

variable (K : Type) [CommRing K] (n r : ℕ)

namespace UnitriangularStageNormality

abbrev stageRing := UnitriangularStageCoordinateRing.CoordinateRing K n r

end UnitriangularStageNormality
end AlgebraicGeometry
end
end
