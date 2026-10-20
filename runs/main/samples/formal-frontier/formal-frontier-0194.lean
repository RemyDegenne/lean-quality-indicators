@[expose] public section

noncomputable section

open CategoryTheory GeneralLinearCoordinateRing UnitriangularCoordinateRing

open scoped CategoryTheory MonObj TensorProduct

namespace AlgebraicGeometry

variable (K : Type) [CommRing K] (n r : ℕ)

open UnitriangularStageCoordinateRing

set_option backward.isDefEq.respectTransparency false

variable (R : Type) [CommRing R] [Algebra K R]

@[simp] theorem unitriangularStageFromGL_toGL (f : CoordinateRing K n r →ₐ[K] R) :
    unitriangularStageFromGL K n r R (unitriangularStageToGL K n r R f) = f := by
  apply Ideal.Quotient.algHom_ext K
  change (unitriangularStageFromGL K n r R (unitriangularStageToGL K n r R f)).comp
      (quotient K n r) = f.comp (quotient K n r)
  rw [unitriangularStageFromGL_comp_quotient]
  change unitriangularFromGL K (Fin n) R
    (unitriangularToGL K (Fin n) R (f.comp (quotient K n r))) =
      f.comp (quotient K n r)
  exact unitriangularFromGL_toGL K (Fin n) R _

end AlgebraicGeometry
end
end
