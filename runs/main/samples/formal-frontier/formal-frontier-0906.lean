@[expose] public section

universe uι uR uS uM uN

namespace ModuleCat

section Pi

variable {ι : Type uι} (Ri : ι → Type uR) [∀ i, Ring (Ri i)]

variable (Mi : ∀ i, ModuleCat.{uM} (Ri i)ᵐᵒᵖ)

theorem piRightSingle_add (i : ι) (x y : Mi i) :
    piRightSingle Ri Mi i (x + y) = piRightSingle Ri Mi i x + piRightSingle Ri Mi i y := by
  classical
  exact Pi.single_add (f := fun j => (Mi j : Type uM)) i x y

end Pi
end ModuleCat
end
