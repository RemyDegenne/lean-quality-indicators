@[expose] public section

noncomputable section

open CategoryTheory GeneralLinearCoordinateRing UpperTriangularCoordinateRing

open scoped CategoryTheory.MonObj TensorProduct

universe u

namespace AlgebraicGeometry

variable (K : Type u) [CommRing K] (n : Type u) [Fintype n] [LinearOrder n]

variable (R : Type u) [CommRing R] [Algebra K R]

/-- Multiplicative classification of affine scheme-valued points over any
commutative `K`-algebra; compare the field-base functor in Milne,
*Algebraic Groups* (2017), §§2.8–2.9. -/
def upperTriangularGroupMulEquivPoints :
    Matrix.UpperTriangularGroup n R ≃*
      ((Spec (.of R)).asOver (Spec (.of K)) ⟶ upperTriangularGroupUnderlyingScheme K n) :=
  (upperTriangularGroupMulEquivAlgHom K n R).trans
    (Spec.mapMulEquiv (R := K) (S := UpperTriangularCoordinateRing.CoordinateRing K n)
      (T := R))

end AlgebraicGeometry
end
end
