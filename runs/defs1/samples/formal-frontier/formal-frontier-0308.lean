@[expose] public section

noncomputable section

open CategoryTheory GeneralLinearCoordinateRing UnitriangularCoordinateRing

open scoped CategoryTheory MonObj TensorProduct

namespace AlgebraicGeometry

variable (K : Type) [CommRing K] (n r : ℕ)

open UnitriangularStageCoordinateRing

set_option backward.isDefEq.respectTransparency false

variable (R : Type) [CommRing R] [Algebra K R]

/-- Multiplicative identification with the points of the stage group scheme.
Milne, *Algebraic Groups* (2017), item 2.9 and §6.49 supply the
full-group and finer field-case subgroup antecedents. -/
def unitriangularStagePointMulEquiv :
    Matrix.UnitriangularGroup.superdiagonalSubgroup n R r ≃*
      ((Spec (.of R)).asOver (Spec (.of K)) ⟶ unitriangularStageUnderlyingScheme K n r) :=
  (unitriangularStageMulEquivAlgHom K n r R).trans
    (Spec.mapMulEquiv (R := K) (S := CoordinateRing K n r) (T := R))

end AlgebraicGeometry
end
end
