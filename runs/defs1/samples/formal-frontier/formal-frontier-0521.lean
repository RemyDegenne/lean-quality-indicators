@[expose] public section

universe uR uS uT uM uN

open CategoryTheory

namespace ModuleCat.RightExtension

variable {R : Type uR} {S : Type uS} [Ring R] [Ring S]

variable (f : R →+* S)

variable {M : Type uM} {N : Type uN}

variable [AddCommGroup M] [Module Rᵐᵒᵖ M]

variable [AddCommGroup N] [Module Rᵐᵒᵖ N]

/-- The canonical pure tensor in a right-module extension of scalars. -/
def tmul (m : M) (s : S) : Obj f M := by
  letI : Module R S := f.toModule
  exact BalancedTensorProduct.tmul m s

end ModuleCat.RightExtension
end
