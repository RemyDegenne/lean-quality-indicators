namespace P2MW.S_IsLocalRing_isRegular_of_systemOfParameters

open IsLocalRing RingTheory

namespace Ws14Port

universe u v

open IsLocalRing RingTheory RingTheory.Sequence Module

p2m_reactivate

p2m_reactivate

p2m_reactivate

section

p2m_open

p2m_reactivate

section Degeneration

variable (R : Type*) [CommRing R] [IsLocalRing R]

variable (M : Type*) [AddCommGroup M] [Module R M]

theorem Module.depth_eq_top_and_associatedPrimes_eq_empty_of_subsingleton [Subsingleton M] :
    Module.depth R M = ⊤ ∧ associatedPrimes R M = ∅ :=
  ⟨Module.depth_of_subsingleton R M, associatedPrimes.eq_empty_of_subsingleton⟩

end Degeneration
end
end Ws14Port
end P2MW.S_IsLocalRing_isRegular_of_systemOfParameters
