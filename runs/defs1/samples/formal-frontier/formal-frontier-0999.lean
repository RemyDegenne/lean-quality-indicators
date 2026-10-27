@[expose] public section

universe uR uS uT uM uN

open CategoryTheory

namespace ModuleCat.RightExtension

variable {R : Type uR} {S : Type uS} [Ring R] [Ring S]

variable (f : R →+* S)

variable {M : Type uM} {N : Type uN}

variable [AddCommGroup M] [Module Rᵐᵒᵖ M]

variable [AddCommGroup N] [Module Rᵐᵒᵖ N]

namespace HomEquiv

variable (M' : ModuleCat.{max uM uS} (MulOpposite R))

variable (X : ModuleCat.{max uM uS} (MulOpposite S))

/-- Send a map to a restricted right module to the corresponding map from the
extension of scalars. -/
noncomputable def fromRestriction
    (h : M' ⟶ (ModuleCat.restrictScalars.{max uM uS} (RingHom.op f)).obj X) :
    (functor f).obj M' ⟶ X :=
  ModuleCat.ofHom
    { __ := fromRestrictionAddHom f M' X h
      map_smul' := fun t x => by
        let _ : Module R S := f.toModule
        let _ : SMulCommClass R Sᵐᵒᵖ S := smulCommClass f
        let lhs : Obj f M' →+ X :=
          (fromRestrictionAddHom f M' X h).comp
            (BalancedTensorProduct.smulAddHom t)
        let rhs : Obj f M' →+ X :=
          { toFun := fun z => t • fromRestrictionAddHom f M' X h z
            map_zero' := by
              rw [(fromRestrictionAddHom f M' X h).map_zero, smul_zero]
            map_add' := fun a b => by
              rw [(fromRestrictionAddHom f M' X h).map_add, smul_add] }
        exact DFunLike.congr_fun
          (BalancedTensorProduct.hom_ext (R := R) (M := M') (N := S)
            (g := lhs) (h := rhs) fun m s => by
              simp [lhs, rhs, fromRestrictionAddHom, BalancedTensorProduct.smulAddHom,
                BalancedTensorProduct.smulBalancedMap, mul_smul]
              rfl) x }

end HomEquiv
end ModuleCat.RightExtension
end
