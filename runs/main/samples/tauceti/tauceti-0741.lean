public section

universe v

namespace TauCeti.TypeBSpinCarrier

open AlgebraicGeometry CategoryTheory

open TauCeti.UniversalEnvelopingAlgebra

open scoped CategoryTheory.MonObj

attribute [local instance 100] LieRing.ofAssociativeRing

attribute [local instance high] Algebra.toModule

variable (n : ℕ)

@[simp]
theorem weightTorus_comp_carrierι :
    weightTorus n ≫ carrierι n =
      TauCeti.GeneralLinear.weightTorus (R := ℤ) (basisWeight n) := by
  simp only [weightTorus_def, carrierι, Category.assoc, eqToHom_trans_assoc, eqToHom_refl,
    Category.id_comp, kostantWeightTorusToToral_comp_ι]

end TauCeti.TypeBSpinCarrier
end
