public section

namespace TauCeti.Hodge

open scoped DirectSum

universe u

namespace HodgeStructureOn

variable {W : Type u} [AddCommGroup W] [Module ℂ W]

variable {ω : Conjugation W} {n : ℤ}

/-- The Hodge decomposition as a linear equivalence: the ambient complex vector space is the
direct sum of its Hodge components. -/
noncomputable def decomposition (hs : HodgeStructureOn W ω n) :
    W ≃ₗ[ℂ] ⨁ p, hs.piece p :=
  (LinearEquiv.ofBijective (DirectSum.coeLinearMap hs.piece) hs.isInternal_piece).symm

end HodgeStructureOn
end TauCeti.Hodge
end
