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

@[simp]
theorem symmetricAlgebraProjClosedPointsEquivOfLinearEquiv_apply_coe
    (e : M ≃ₗ[R] N)
    (p : closedPoints
      (Proj (SymmetricAlgebra.homogeneousSubmodule (R := R) (M := N)))) :
    (symmetricAlgebraProjClosedPointsEquivOfLinearEquiv e p).1 =
      ProjectiveSpectrum.comapFun
        (SymmetricAlgebra.gradedMap e.toLinearMap).toGradedRingHom
        (irrelevant_le_map_of_comp_eq_id
          (𝒜 := SymmetricAlgebra.homogeneousSubmodule (R := R) (M := M))
          (ℬ := SymmetricAlgebra.homogeneousSubmodule (R := R) (M := N))
          (SymmetricAlgebra.gradedMap e.toLinearMap).toGradedRingHom
          (SymmetricAlgebra.gradedMap e.symm.toLinearMap).toGradedRingHom
          (symmetricAlgebraGradedMap_comp_symm e)) p.1 :=
  rfl

end LinearEquiv
end
end ProjectiveSpace
end
