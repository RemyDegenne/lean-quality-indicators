public section

namespace TauCeti

open LieModule Matrix Module

attribute [local instance 100] LieRing.ofAssociativeRing

universe u

variable {K : Type u} [Field K] [CharZero K] {N : ℕ} {mu : Fin N → K}

/-- **The distinguished generator of `L(mu)`**, the class of the chosen highest weight vector. It
inherits the two choices the carrier is built from and is not canonical; what is known of it is
`TauCeti.isGlHighestWeightVector_glIrreducibleGenerator`. -/
noncomputable def glIrreducibleGenerator (N : ℕ) (mu : Fin N → K) : glIrreducible N mu :=
  LieSubmodule.Quotient.mk' (glCarrierCoatom K mu)
    ⟨glCarrierVector K mu, glCarrierVector_mem_glCarrierSpan⟩

end TauCeti
end
