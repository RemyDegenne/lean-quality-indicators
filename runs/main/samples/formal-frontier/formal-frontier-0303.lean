@[expose] public section

open CategoryTheory

open scoped CategoryTheory.MonObj TensorProduct

namespace AlgebraicGeometry

universe u v

variable (K Γ R : Type u)

variable [CommRing K] [CommRing R] [Algebra K R] [Fintype Γ] [Group Γ]

@[simp]
theorem finiteConstantLocallyConstantMulEquivPoints_const (g : Γ) :
    (finiteConstantLocallyConstantMulEquivPoints K Γ K
        (LocallyConstant.const (PrimeSpectrum K) g)).left =
      (finiteConstantGroupSchemePoint K Γ g).left := by
  rw [finiteConstantLocallyConstantMulEquivPoints_apply_left,
    FiniteGroupFunctions.locallyConstantMulEquivAlgHom_const]
  rfl

end AlgebraicGeometry
end
