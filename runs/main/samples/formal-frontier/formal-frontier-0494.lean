@[expose] public section

universe u v

open CategoryTheory

namespace KTheory

variable (K : Type u) [DivisionRing K]

namespace K0

section DimensionEquivalence

universe w

theorem finrankEquiv_symm_natCast (n : ℕ) :
    (finrankEquiv K).symm (n : ℤ) = of K (Fin n → Kᵐᵒᵖ) := by
  rw [finrankEquiv_symm_apply, natCast_zsmul,
    ← ofClass_of K (Fin n → Kᵐᵒᵖ), ProjectiveClass.of_fin_fun_eq_nsmul,
    map_nsmul, ofClass_of]

end DimensionEquivalence
end K0
end KTheory
end
