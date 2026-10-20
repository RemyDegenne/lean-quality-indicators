@[expose] public section

universe uι uR uS uM uN

namespace ModuleCat

section Pi

variable {ι : Type uι} (Ri : ι → Type uR) [∀ i, Ring (Ri i)]

variable (Mi : ∀ i, ModuleCat.{uM} (Ri i)ᵐᵒᵖ)

@[simp]
theorem piRightLinearEquivOfIsZero_symm_apply (i : ι)
    (h : ∀ j, j ≠ i → CategoryTheory.Limits.IsZero (Mi j))
    (y : (ModuleCat.restrictScalars (RingHom.op (Pi.evalRingHom Ri i))).obj (Mi i)) :
    (piRightLinearEquivOfIsZero Ri Mi i h).symm y = piRightSingle Ri Mi i y := rfl

end Pi
end ModuleCat
end
