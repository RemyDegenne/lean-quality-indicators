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
theorem fromSemilinear_tmul (h : M →ₛₗ[RingHom.op f] X) (m : M) (s : S) :
    fromSemilinear f h (tmul f m s) = MulOpposite.op s • h m := by
  let _ : Module R S := f.toModule
  change BalancedTensorProduct.lift _ (BalancedTensorProduct.tmul (R := R) m s) = _
  rw [BalancedTensorProduct.lift_tmul]

end SemilinearHomEquiv
end ModuleCat.RightExtension
end
