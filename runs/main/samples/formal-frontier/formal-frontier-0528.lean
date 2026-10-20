@[expose] public section

noncomputable section

open CategoryTheory GeneralLinearCoordinateRing UnitriangularCoordinateRing

open scoped CategoryTheory MonObj TensorProduct

namespace AlgebraicGeometry

variable (K : Type) [CommRing K] (n r : ℕ)

open UnitriangularStageCoordinateRing

set_option backward.isDefEq.respectTransparency false

variable (R : Type) [CommRing R] [Algebra K R]

theorem unitriangularStageFromGL_successor
    (s : Matrix.UnitriangularGroup.superdiagonalSubgroup n R (r + 1)) :
    (unitriangularStageFromGL K n (r + 1) R s).comp (successor K n r) =
      unitriangularStageFromGL K n r R (unitriangularStagePointSuccessor n r R s) := by
  apply Ideal.Quotient.algHom_ext K
  change ((unitriangularStageFromGL K n (r + 1) R s).comp
      (successor K n r)).comp (quotient K n r) =
        (unitriangularStageFromGL K n r R
          (unitriangularStagePointSuccessor n r R s)).comp (quotient K n r)
  have hfactor : (successor K n r).comp (quotient K n r) =
      quotient K n (r + 1) := rfl
  rw [AlgHom.comp_assoc, hfactor,
    unitriangularStageFromGL_comp_quotient,
    unitriangularStageFromGL_comp_quotient]
  rfl

end AlgebraicGeometry
end
end
