namespace P2MW.S_GaloisRepAdic_ordinaryCondition_of_isEquiv

open scoped TensorProduct

namespace GaloisRepAdic

namespace LCSol

p2m_open

variable {A B : Type} [CommRing A] [IsLocalRing A] [CommRing B] [IsLocalRing B]

theorem det_apply_baseChangeAlong (φ : A →+* B) (hφ : IsLocalHom φ) (ρ : GaloisRepAdic A)
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) :
    LinearMap.det ((ρ.baseChangeAlong φ hφ).ρ σ) = φ (LinearMap.det (ρ.ρ σ)) := by
  letI : Algebra A B := φ.toAlgebra
  show LinearMap.det ((ρ.ρ σ).baseChange B) = algebraMap A B (LinearMap.det (ρ.ρ σ))
  exact LinearMap.det_baseChange (ρ.ρ σ)

end LCSol
end GaloisRepAdic
end P2MW.S_GaloisRepAdic_ordinaryCondition_of_isEquiv
