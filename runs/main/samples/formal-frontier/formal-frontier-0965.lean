@[expose] public section

universe uι uR uS uM uN

namespace ModuleCat

namespace RightExtension

section Pi

variable {ι : Type uι} (Ri : ι → Type uR) [∀ i, Ring (Ri i)]

theorem piRecoverLinearEquiv_tmul
    (Mi : ∀ i, ModuleCat.{uM} (Ri i)ᵐᵒᵖ) (i : ι)
    (x : ModuleCat.piRight Ri Mi) (r : Ri i) :
    piRecoverLinearEquiv Ri Mi i (tmul (Pi.evalRingHom Ri i) x r) =
      MulOpposite.op r • x i := by
  exact fromSemilinear_tmul (Pi.evalRingHom Ri i) (ModuleCat.piRightEval Ri Mi i) x r

end Pi
end RightExtension
end ModuleCat
end
