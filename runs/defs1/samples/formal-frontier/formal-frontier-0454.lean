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

/-- Extend a semilinear map from the original right module to a right-linear
map from its extension of scalars. -/
def fromSemilinear (h : M →ₛₗ[RingHom.op f] X) : Obj f M →ₗ[Sᵐᵒᵖ] X where
  __ := fromSemilinearAddHom f h
  map_smul' t x := by
    let _ : Module R S := f.toModule
    let _ : SMulCommClass R Sᵐᵒᵖ S := smulCommClass f
    let lhs : Obj f M →+ X :=
      (fromSemilinearAddHom f h).comp (BalancedTensorProduct.smulAddHom t)
    let rhs : Obj f M →+ X :=
      { toFun := fun z => t • fromSemilinearAddHom f h z
        map_zero' := by rw [(fromSemilinearAddHom f h).map_zero, smul_zero]
        map_add' := fun a b => by rw [(fromSemilinearAddHom f h).map_add, smul_add] }
    exact DFunLike.congr_fun
      (BalancedTensorProduct.hom_ext (R := R) (M := M) (N := S)
        (g := lhs) (h := rhs) fun m s => by
          change fromSemilinearAddHom f h
              (BalancedTensorProduct.smulAddHom t (BalancedTensorProduct.tmul m s)) =
            t • fromSemilinearAddHom f h (BalancedTensorProduct.tmul m s)
          simp only [fromSemilinearAddHom, BalancedTensorProduct.smulAddHom,
            BalancedTensorProduct.lift_tmul, BalancedTensorProduct.smulBalancedMap]
          exact mul_smul t (MulOpposite.op s) (h m)) x

end SemilinearHomEquiv
end ModuleCat.RightExtension
end
