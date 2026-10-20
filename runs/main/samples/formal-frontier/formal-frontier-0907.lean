@[expose] public section

universe u w w'

open CategoryTheory

namespace KTheory

variable (R : Type u) [Ring R]

namespace K0

theorem dualEquiv_of_module (M : Type w)
    [AddCommGroup M] [Module Rᵐᵒᵖ M]
    [Module.Finite Rᵐᵒᵖ M] [Module.Projective Rᵐᵒᵖ M] :
    dualEquiv R (K0.of R M) =
      @K0.of Rᵐᵒᵖ _
        ((ModuleCat.restrictScalars (RingEquiv.opOp R).symm.toRingHom).obj
          ((ModuleCat.rightDual R).obj (Opposite.op (ModuleCat.of Rᵐᵒᵖ M)))) _ _
        (ModuleCat.isFiniteProjective_rightDual_restrictScalars R
          (ModuleCat.of Rᵐᵒᵖ M) ⟨inferInstance, inferInstance⟩).1
        (ModuleCat.isFiniteProjective_rightDual_restrictScalars R
          (ModuleCat.of Rᵐᵒᵖ M) ⟨inferInstance, inferInstance⟩).2 := by
  simpa only [AddMonoidHom.comp_apply, AddEquiv.coe_toAddMonoidHom,
    ProjectiveClass.dualEquiv_of_module, K0.ofClass_of] using
    DFunLike.congr_fun (dualEquiv_comp_ofClass R) (ProjectiveClass.of R M)

end K0
end KTheory
end
