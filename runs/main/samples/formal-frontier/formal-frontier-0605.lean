@[expose] public section

universe uι uR uS uM uN

namespace KTheory

namespace ProjectiveClass

section Pi

variable {ι : Type uι} (Ri : ι → Type uR) [∀ i, Ring (Ri i)]

variable [Finite ι]

theorem piEquiv_symm_apply_pi_map (a : ProjectiveClass (∀ i, Ri i)) :
    (piEquiv Ri).symm (fun i ↦ map (Pi.evalRingHom Ri i) a) = a := by
  change (piEquiv Ri).symm (piEquiv Ri a) = a
  exact (piEquiv Ri).symm_apply_apply a

end Pi
end ProjectiveClass
end KTheory
end
