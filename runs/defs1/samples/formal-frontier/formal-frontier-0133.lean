@[expose] public section

universe uR uS uT uM uN

open CategoryTheory

namespace ModuleCat.RightExtension

variable {R : Type uR} {S : Type uS} [Ring R] [Ring S]

variable (f : R →+* S)

variable {M : Type uM} {N : Type uN}

variable [AddCommGroup M] [Module Rᵐᵒᵖ M]

variable [AddCommGroup N] [Module Rᵐᵒᵖ N]

/-- Extension of scalars carries a right-linear equivalence to a
right-linear equivalence. -/
def mapLinearEquiv (e : M ≃ₗ[Rᵐᵒᵖ] N) :
    Obj f M ≃ₗ[Sᵐᵒᵖ] Obj f N :=
  LinearEquiv.ofLinearMap (map f e.toLinearMap) (map f e.symm.toLinearMap)
    (by
      apply linearMap_ext f
      intro n s
      simp)
    (by
      apply linearMap_ext f
      intro m s
      simp)

end ModuleCat.RightExtension
end
