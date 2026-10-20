@[expose] public section

universe uR uS uT v

namespace KTheory

variable {R : Type uR} {S : Type uS} {T : Type uT}

variable [Ring R] [Ring S] [Ring T]

variable (f : R →+* S) (hf : Function.Surjective f)

variable (hker : IsNilpotent (RingHom.ker f))

namespace K0

@[simp]
theorem equivOfSurjectiveOfIsNilpotentKer_of (M : Type v)
    [AddCommGroup M] [Module Rᵐᵒᵖ M]
    [Module.Finite Rᵐᵒᵖ M] [Module.Projective Rᵐᵒᵖ M] :
    equivOfSurjectiveOfIsNilpotentKer f hf hker (of R M) =
      of S (ModuleCat.RightExtension.Obj f M) := by
  simpa only [equivOfSurjectiveOfIsNilpotentKer_apply] using map_of f M

end K0
end KTheory
end
