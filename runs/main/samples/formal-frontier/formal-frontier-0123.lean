@[expose] public section

universe u v

open CategoryTheory

namespace KTheory

variable (K : Type u) [DivisionRing K]

namespace ProjectiveClass

@[simp]
theorem finrankHom_of (X : ModuleCat.FiniteProjective.{u, u} Kᵐᵒᵖ) :
    finrankHom K (of K X) = Module.finrank Kᵐᵒᵖ X := by
  rw [finrankHom_eq_lift, lift_of]

end ProjectiveClass
end KTheory
end
