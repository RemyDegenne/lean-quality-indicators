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

/-- Restrict a right-linear map out of an extension of scalars to tensors with
second factor `1`. -/
def toSemilinear (g : Obj f M →ₗ[Sᵐᵒᵖ] X) : M →ₛₗ[RingHom.op f] X where
  toFun m := g (tmul f m 1)
  map_add' m n := by
    let _ : Module R S := f.toModule
    have h : tmul f (m + n) 1 = tmul f m 1 + tmul f n 1 := by
      change BalancedTensorProduct.tmul (m + n) 1 =
        BalancedTensorProduct.tmul m 1 + BalancedTensorProduct.tmul n 1
      exact BalancedTensorProduct.add_tmul m n 1
    rw [h, g.map_add]
  map_smul' r m := by
    change g (tmul f (r • m) 1) = (RingHom.op f r) • g (tmul f m 1)
    rw [← g.map_smul]
    congr 1
    rw [tmul_smul]
    simpa using smul_tmul f (MulOpposite.unop r) m 1

end SemilinearHomEquiv
end ModuleCat.RightExtension
end
