@[expose] public section

noncomputable section

open CategoryTheory GeneralLinearCoordinateRing UnitriangularCoordinateRing

open scoped CategoryTheory MonObj TensorProduct

namespace AlgebraicGeometry

variable (K : Type) [CommRing K] (n r : ℕ)

open UnitriangularStageCoordinateRing

set_option backward.isDefEq.respectTransparency false

variable (R : Type) [CommRing R] [Algebra K R]

theorem unitriangularStageFromGL_comp_quotient
    (s : Matrix.UnitriangularGroup.superdiagonalSubgroup n R r) :
    (unitriangularStageFromGL K n r R s).comp (quotient K n r) =
      unitriangularFromGL K (Fin n) R s.1 :=
  Ideal.Quotient.liftₐ_comp _ _ _

end AlgebraicGeometry
end
end
