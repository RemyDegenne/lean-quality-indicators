set_option warningAsError true

public section

open AlgebraicGeometry

namespace ProjectiveSpace

noncomputable section

attribute [local instance] MvPolynomial.gradedAlgebra

universe u v w

variable {R : Type u} {M : Type v}

variable [CommRing R] [AddCommGroup M] [Module R M]

section LinearEquiv

variable {N : Type w} [AddCommGroup N] [Module R N]

theorem symmetricAlgebraGradedMap_symm_comp (e : M ≃ₗ[R] N) :
    (SymmetricAlgebra.gradedMap e.symm.toLinearMap).toGradedRingHom.comp
      (SymmetricAlgebra.gradedMap e.toLinearMap).toGradedRingHom =
        GradedRingHom.id
          (SymmetricAlgebra.homogeneousSubmodule (R := R) (M := M)) := by
  apply GradedRingHom.ext
  intro x
  change SymmetricAlgebra.map e.symm.toLinearMap
    (SymmetricAlgebra.map e.toLinearMap x) = x
  exact (SymmetricAlgebra.congr e).symm_apply_apply x

end LinearEquiv
end
end ProjectiveSpace
end
