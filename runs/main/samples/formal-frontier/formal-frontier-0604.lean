@[expose] public section

universe u v

open CategoryTheory

universe uS

namespace KTheory.K0

section PrincipalIdealDomainIntegerEquivalence

variable (R : Type u) [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]

@[simp]
theorem pidEquivInt_symm_one : (pidEquivInt R).symm 1 = of R Rᵐᵒᵖ := by
  rw [pidEquivInt_symm_apply, one_zsmul]

end PrincipalIdealDomainIntegerEquivalence
end KTheory.K0
end
