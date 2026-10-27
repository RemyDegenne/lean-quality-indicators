@[expose] public section

universe uR uS uT uM uN

open CategoryTheory

namespace ModuleCat.RightExtension

variable {R : Type uR} {S : Type uS} [Ring R] [Ring S]

variable (f : R →+* S)

variable {M : Type uM} {N : Type uN}

variable [AddCommGroup M] [Module Rᵐᵒᵖ M]

variable [AddCommGroup N] [Module Rᵐᵒᵖ N]

/-- Extension of scalars on a morphism of right modules. -/
def map (g : M →ₗ[Rᵐᵒᵖ] N) : Obj f M →ₗ[Sᵐᵒᵖ] Obj f N where
  __ := mapAddHom (f := f) g
  map_smul' t x := by
    let _ : Module R S := f.toModule
    let _ : SMulCommClass R Sᵐᵒᵖ S := smulCommClass f
    exact DFunLike.congr_fun
      (BalancedTensorProduct.hom_ext (R := R) (M := M) (N := S)
        (g := (mapAddHom (f := f) g).comp (BalancedTensorProduct.smulAddHom t))
        (h := (BalancedTensorProduct.smulAddHom t).comp (mapAddHom (f := f) g))
        fun m s => by
          simp [mapAddHom, tmul, BalancedTensorProduct.smulAddHom,
            BalancedTensorProduct.smulBalancedMap]) x

end ModuleCat.RightExtension
end
