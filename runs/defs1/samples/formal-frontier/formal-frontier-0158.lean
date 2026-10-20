@[expose] public section

noncomputable section

open CategoryTheory GeneralLinearCoordinateRing UnitriangularCoordinateRing

open scoped CategoryTheory.MonObj TensorProduct

universe u

namespace AlgebraicGeometry

variable (K : Type u) [CommRing K] (n : Type u) [Fintype n] [LinearOrder n]

variable (R : Type u) [CommRing R] [Algebra K R]

/-- The multiplicative equivalence with affine scheme-valued points. -/
def unitriangularGroupMulEquivPoints :
    Matrix.UnitriangularGroup n R ≃*
      ((Spec (.of R)).asOver (Spec (.of K)) ⟶ unitriangularGroupUnderlyingScheme K n) :=
  (unitriangularGroupMulEquivAlgHom K n R).trans
    (Spec.mapMulEquiv (R := K) (S := UnitriangularCoordinateRing.CoordinateRing K n)
      (T := R))

end AlgebraicGeometry
end
end
