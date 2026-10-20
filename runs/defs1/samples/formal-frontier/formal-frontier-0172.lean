@[expose] public section

noncomputable section

open CategoryTheory Algebra.TensorProduct

open scoped CategoryTheory MonObj TensorProduct MonoidalCategory

namespace AlgebraicGeometry

variable (K : Type) [CommRing K] (n r : ℕ)

namespace UnitriangularStageNormality

/-- The algebra of functions on the affine product of the ambient group and a stage. -/
abbrev productRing :=
  @TensorProduct K (CommRing.toCommSemiring : CommSemiring K)
    (ambientRing K n) (stageRing K n r)
    ((CommRing.toCommSemiring : CommSemiring (ambientRing K n)).toAddCommMonoid)
    ((CommRing.toCommSemiring : CommSemiring (stageRing K n r)).toAddCommMonoid)
    (Algebra.toModule (R := K) (A := ambientRing K n))
    (Algebra.toModule (R := K) (A := stageRing K n r))

end UnitriangularStageNormality
end AlgebraicGeometry
end
end
