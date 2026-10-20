@[expose] public section

noncomputable section

open CategoryTheory GeneralLinearCoordinateRing DiagonalCoordinateRing

open scoped CategoryTheory.MonObj TensorProduct

universe u

namespace AlgebraicGeometry

variable (K : Type u) [CommRing K] (n : Type u) [Fintype n] [DecidableEq n]

variable (R : Type u) [CommRing R] [Algebra K R]

/-- The group equivalence with affine scheme-valued points. -/
def diagonalGroupMulEquivPoints :
    Matrix.DiagonalGroup n R ≃*
      ((Spec (.of R)).asOver (Spec (.of K)) ⟶ diagonalGroupUnderlyingScheme K n) :=
  (diagonalGroupMulEquivAlgHom K n R).trans
    (Spec.mapMulEquiv (R := K) (S := DiagonalCoordinateRing.CoordinateRing K n)
      (T := R))

end AlgebraicGeometry
end
end
