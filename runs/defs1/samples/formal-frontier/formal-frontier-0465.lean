@[expose] public section

universe uι uR uS uM uN

namespace ModuleCat

namespace FiniteProjective

section Pi

variable {ι : Type uι} (Ri : ι → Type uR) [∀ i, Ring (Ri i)]

variable (Mi : ∀ i, FiniteProjective.{uR, uM} (Ri i)ᵐᵒᵖ)

variable [Finite ι]

/-- The underlying finite-projective bundle is linearly equivalent to its
coefficient-product module bundle by the identity on functions. -/
def piLinearEquiv : pi Ri Mi ≃ₗ[(∀ i, Ri i)ᵐᵒᵖ]
    ModuleCat.piRight Ri (fun i => (Mi i).obj) :=
  LinearEquiv.refl (∀ i, Ri i)ᵐᵒᵖ (ModuleCat.piRight Ri (fun i => (Mi i).obj))

end Pi
end FiniteProjective
end ModuleCat
end
