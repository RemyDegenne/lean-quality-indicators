@[expose] public section

universe u v

open CategoryTheory

universe uS

namespace KTheory.K0

section PrincipalIdealDomainIntegerEquivalence

variable (R : Type u) [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]

@[simp]
theorem pidEquivInt_of_module (M : Type v) [AddCommGroup M]
    [Module Rᵐᵒᵖ M] [Module.Finite Rᵐᵒᵖ M] [Module.Projective Rᵐᵒᵖ M] :
    pidEquivInt R (of R M) =
      (Module.finrank (FractionRing R)ᵐᵒᵖ
        (ModuleCat.RightExtension.Obj (algebraMap R (FractionRing R)) M) : ℤ) := by
  rw [pidEquivInt_apply, map_of, finrankHom_of_module]

end PrincipalIdealDomainIntegerEquivalence
end KTheory.K0
end
