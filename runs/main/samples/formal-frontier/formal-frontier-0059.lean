@[expose] public section

universe u w w'

open CategoryTheory

namespace KTheory

variable (R : Type u) [Ring R]

namespace ProjectiveClass

theorem dualEquiv_of_module (M : Type w)
    [AddCommGroup M] [Module Rᵐᵒᵖ M]
    [Module.Finite Rᵐᵒᵖ M] [Module.Projective Rᵐᵒᵖ M] :
    dualEquiv R (ProjectiveClass.of R M) =
      @ProjectiveClass.of Rᵐᵒᵖ _
        ((ModuleCat.restrictScalars (RingEquiv.opOp R).symm.toRingHom).obj
          ((ModuleCat.rightDual R).obj (Opposite.op (ModuleCat.of Rᵐᵒᵖ M)))) _ _
        (ModuleCat.isFiniteProjective_rightDual_restrictScalars R
          (ModuleCat.of Rᵐᵒᵖ M) ⟨inferInstance, inferInstance⟩).1
        (ModuleCat.isFiniteProjective_rightDual_restrictScalars R
          (ModuleCat.of Rᵐᵒᵖ M) ⟨inferInstance, inferInstance⟩).2 := by
  exact canonicalDualClassHom_of R (ModuleCat.FiniteProjective.of Rᵐᵒᵖ M)

end ProjectiveClass
end KTheory
end
