@[expose] public section

universe uι uR uS uM uN

namespace ModuleCat

namespace FiniteProjective

section Pi

variable {ι : Type uι} (Ri : ι → Type uR) [∀ i, Ring (Ri i)]

variable (Mi : ∀ i, FiniteProjective.{uR, uM} (Ri i)ᵐᵒᵖ)

variable [Finite ι]

/-- Form an element of the finite-projective coefficient product. -/
def piMk (x : ∀ i, Mi i) : pi Ri Mi := x

end Pi
end FiniteProjective
end ModuleCat
end
