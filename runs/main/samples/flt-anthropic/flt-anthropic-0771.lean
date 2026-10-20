namespace P2MW.S_GaloisRep_DeformationRingData_length_cotangent_le_add_of_flatCondition_insert_isUnipotentOnInertiaAt

attribute [-instance] instIsScalarTowerTensorProduct_definitions

set_option autoImplicit false

open scoped Pointwise TensorProduct

namespace FlatK1LC

open GaloisRepAdic

variable {A B : Type} [CommRing A] [IsLocalRing A] [CommRing B] [IsLocalRing B]

theorem det_apply_baseChangeAlong (φ : A →+* B) (hφ : IsLocalHom φ) (ρ : GaloisRepAdic A)
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) :
    LinearMap.det ((ρ.baseChangeAlong φ hφ).ρ σ) = φ (LinearMap.det (ρ.ρ σ)) := by
  letI : Algebra A B := φ.toAlgebra
  show LinearMap.det ((ρ.ρ σ).baseChange B) = algebraMap A B (LinearMap.det (ρ.ρ σ))
  exact LinearMap.det_baseChange (ρ.ρ σ)

end FlatK1LC
end P2MW.S_GaloisRep_DeformationRingData_length_cotangent_le_add_of_flatCondition_insert_isUnipotentOnInertiaAt
