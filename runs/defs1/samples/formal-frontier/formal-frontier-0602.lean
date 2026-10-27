@[expose] public section

universe uι uR uS uM uN

namespace ModuleCat

section Pi

variable {ι : Type uι} (Ri : ι → Type uR) [∀ i, Ring (Ri i)]

variable (Mi : ∀ i, ModuleCat.{uM} (Ri i)ᵐᵒᵖ)

/-- The supported element with a prescribed value at one coordinate. No
finiteness or public decidable-equality hypothesis is needed for its formation. -/
noncomputable def piRightSingle (i : ι) (x : Mi i) : piRight Ri Mi :=
  @Pi.single ι (fun i => Mi i) (fun _ => inferInstance) (Classical.decEq ι) i x

end Pi
end ModuleCat
end
