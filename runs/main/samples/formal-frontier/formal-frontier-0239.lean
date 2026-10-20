@[expose] public section

universe uι uR uS uM uN

namespace KTheory

namespace K0

section Pi

variable {ι : Type uι} (Ri : ι → Type uR) [∀ i, Ring (Ri i)]

variable [Finite ι]

theorem piEquiv_toAddMonoidHom :
    (piEquiv Ri).toAddMonoidHom =
      AddMonoidHom.pi (fun i ↦ map (Pi.evalRingHom Ri i)) := by
  rfl

end Pi
end K0
end KTheory
end
