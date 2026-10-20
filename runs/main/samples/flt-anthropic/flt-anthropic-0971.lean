namespace P2MW.S_GaloisRepAdic_ordinaryCondition_of_isEquiv

open scoped TensorProduct

namespace GaloisRepAdic

namespace LCSol

p2m_open

variable {A B : Type} [CommRing A] [IsLocalRing A] [CommRing B] [IsLocalRing B]

theorem minimalOrdinaryCondition_of_isEquiv (𝒪 : Type) [CommRing 𝒪] [Algebra 𝒪 A]
    {ρ₁ ρ₂ : GaloisRepAdic A} (e : ρ₁.IsEquiv ρ₂) {p : ℕ} {S : Finset ℕ}
    (h : GaloisRep.minimalOrdinaryCondition 𝒪 p S ρ₁) :
    GaloisRep.minimalOrdinaryCondition 𝒪 p S ρ₂ := by
  obtain ⟨h₁, h₂⟩ := h
  exact ⟨ordinaryCondition_of_isEquiv 𝒪 e h₁,
    fun q hq hprime hqp => isUnipotentOnInertiaAt_of_isEquiv e (h₂ q hq hprime hqp)⟩

end LCSol
end GaloisRepAdic
end P2MW.S_GaloisRepAdic_ordinaryCondition_of_isEquiv
