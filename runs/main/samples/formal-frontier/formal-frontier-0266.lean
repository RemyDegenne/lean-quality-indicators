@[expose] public section

universe uR uS uT uM

open CategoryTheory CategoryTheory.Limits

open ModuleCat (FiniteProjective)

namespace KTheory

variable {R : Type uR} {S : Type uS} {T : Type uT}

variable [Ring R] [Ring S] [Ring T]

namespace ProjectiveClass

@[simp]
theorem map_of (φ : R →+* S) (M : Type uM) [AddCommGroup M] [Module Rᵐᵒᵖ M]
    [Module.Finite Rᵐᵒᵖ M] [Module.Projective Rᵐᵒᵖ M] :
    map φ (of R M) = of S (ModuleCat.RightExtension.Obj φ M) := by
  calc
    map φ (of R M) = mapValue φ (FiniteProjective.repr Rᵐᵒᵖ M) :=
      lift_of_module (R := R) (M := M) (f := mapValue φ)
        (hiso := mapValue_iso φ) (hzero := mapValue_zero φ) (hadd := mapValue_prod φ)
    _ = of S (ModuleCat.RightExtension.Obj φ M) :=
      of_eq_of_equiv S _
        (ModuleCat.RightExtension.mapLinearEquiv φ (FiniteProjective.reprEquiv Rᵐᵒᵖ M))

end ProjectiveClass
end KTheory
end
