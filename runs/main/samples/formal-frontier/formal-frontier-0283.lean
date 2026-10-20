@[expose] public section

universe uR uM

namespace KTheory

variable (R : Type uR) [Ring R]

namespace ProjectiveClass

@[simp]
theorem traceModCommutators_of_module (M : Type uM) [AddCommGroup M]
    [Module Rᵐᵒᵖ M] [Module.Finite Rᵐᵒᵖ M] [Module.Projective Rᵐᵒᵖ M] :
    traceModCommutators R (of R M) =
      LinearMap.traceModCommutators R M (LinearMap.id (R := Rᵐᵒᵖ) (M := M)) := by
  rw [traceModCommutators, lift_of_module]
  · exact identityTrace_equiv R (ModuleCat.FiniteProjective.reprEquiv Rᵐᵒᵖ M)
  · intro X Y e
    exact identityTrace_equiv R (ModuleCat.FiniteProjective.isoToLinearEquiv e)

end ProjectiveClass
end KTheory
end
