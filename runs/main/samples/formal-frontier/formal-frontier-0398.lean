@[expose] public section

noncomputable section

open CategoryTheory GeneralLinearCoordinateRing UnitriangularCoordinateRing

open scoped CategoryTheory MonObj TensorProduct

namespace AlgebraicGeometry

variable (K : Type) [CommRing K] (n r : ℕ)

open UnitriangularStageCoordinateRing

set_option backward.isDefEq.respectTransparency false

variable (R : Type) [CommRing R] [Algebra K R]

theorem unitriangularStageFromGL_natural {S : Type} [CommRing S] [Algebra K S]
    (v : R →ₐ[K] S) (s : Matrix.UnitriangularGroup.superdiagonalSubgroup n R r) :
    unitriangularStageFromGL K n r S (unitriangularStageMap n r R v.toRingHom s) =
      v.comp (unitriangularStageFromGL K n r R s) := by
  apply Ideal.Quotient.algHom_ext K
  change (unitriangularStageFromGL K n r S
      (unitriangularStageMap n r R v.toRingHom s)).comp (quotient K n r) =
        (v.comp (unitriangularStageFromGL K n r R s)).comp (quotient K n r)
  rw [AlgHom.comp_assoc, unitriangularStageFromGL_comp_quotient,
    unitriangularStageFromGL_comp_quotient]
  exact unitriangularFromGL_natural K (Fin n) R v s.1

end AlgebraicGeometry
end
end
