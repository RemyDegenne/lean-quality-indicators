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

/-- The additive homomorphism induced by a map to a restricted right module.
This is an implementation detail of `ModuleCat.RightExtension.HomEquiv.fromRestriction`. -/
noncomputable def fromRestrictionAddHom
    (h : M' ⟶ (ModuleCat.restrictScalars.{max uM uS} (RingHom.op f)).obj X) :
    Obj f M' →+ X := by
  letI : Module R S := f.toModule
  apply BalancedTensorProduct.lift
  exact
    { toFun := fun m s => MulOpposite.op s • h m
      map_zero_left := fun s => by
        rw [h.hom.map_zero, smul_zero]
        rfl
      map_add_left := fun m n s => by
        rw [h.hom.map_add, smul_add]
        rfl
      map_zero_right := fun m => by
        change (0 : Sᵐᵒᵖ) • h m = 0
        exact zero_smul Sᵐᵒᵖ (h m)
      map_add_right := fun m s t => by
        rw [MulOpposite.op_add, add_smul]
        rfl
      balance := fun r m s => by
        rw [h.hom.map_smul]
        change MulOpposite.op s • (MulOpposite.op (f r) • h m) =
          MulOpposite.op (f r * s) • h m
        rw [← mul_smul]
        rfl }

end HomEquiv
end ModuleCat.RightExtension
end
