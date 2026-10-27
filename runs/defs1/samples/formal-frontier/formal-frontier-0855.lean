@[expose] public section

universe uι uR uS uM uN

namespace ModuleCat

section Pi

variable {ι : Type uι} (Ri : ι → Type uR) [∀ i, Ring (Ri i)]

variable (Mi : ∀ i, ModuleCat.{uM} (Ri i)ᵐᵒᵖ)

/-- The accessible semilinear evaluation map of the bundled product. -/
def piRightEval (i : ι) : piRight Ri Mi →ₛₗ[RingHom.op (Pi.evalRingHom Ri i)] Mi i :=
  Module.piRightEval Ri (fun i => Mi i) i

end Pi
end ModuleCat
end
