@[expose] public section

universe u v

open CategoryTheory

universe uS

namespace KTheory.K0

section PrincipalIdealDomainIntegerEquivalence

variable (R : Type u) [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]

theorem pidEquivInt_symm_apply (z : ℤ) :
    (pidEquivInt R).symm z = z • of R Rᵐᵒᵖ := by
  apply (pidEquivInt R).injective
  rw [AddEquiv.apply_symm_apply, map_zsmul, pidEquivInt_of_self]
  simp

end PrincipalIdealDomainIntegerEquivalence
end KTheory.K0
end
