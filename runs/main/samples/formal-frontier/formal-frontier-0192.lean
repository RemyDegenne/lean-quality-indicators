@[expose] public section

universe u v

open CategoryTheory

namespace KTheory

variable (K : Type u) [DivisionRing K]

namespace ProjectiveClass

section DimensionEquivalence

theorem of_eq_finrankEquiv_symm (M : Type v) [AddCommGroup M] [Module Kᵐᵒᵖ M]
    [Module.Finite Kᵐᵒᵖ M] :
    of K M = (finrankEquiv K).symm (Module.finrank Kᵐᵒᵖ M) := by
  rw [← finrankEquiv_of_module K M]
  exact ((finrankEquiv K).symm_apply_apply (of K M)).symm

end DimensionEquivalence
end ProjectiveClass
end KTheory
end
