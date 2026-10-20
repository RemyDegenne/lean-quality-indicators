@[expose] public section

universe uR uS uT uM uN

open CategoryTheory

namespace ModuleCat.RightExtension

variable {R : Type uR} {S : Type uS} [Ring R] [Ring S]

variable (f : R →+* S)

variable {M : Type uM} {N : Type uN}

variable [AddCommGroup M] [Module Rᵐᵒᵖ M]

variable [AddCommGroup N] [Module Rᵐᵒᵖ N]

section SemilinearHomEquiv

universe uX

variable {X : Type uX} [AddCommGroup X] [Module Sᵐᵒᵖ X]

@[simp]
theorem toSemilinear_apply (g : Obj f M →ₗ[Sᵐᵒᵖ] X) (m : M) :
    toSemilinear f g m = g (tmul f m 1) :=
  rfl

end SemilinearHomEquiv
end ModuleCat.RightExtension
end
