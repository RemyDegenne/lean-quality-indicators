@[expose] public section

universe uι uR uM uN uP

namespace Module

section Pi

variable {ι : Type uι} (Ri : ι → Type uR) (Mi : ι → Type uM)

variable [∀ i, Semiring (Ri i)] [∀ i, AddCommMonoid (Mi i)]

variable [∀ i, Module (Ri i)ᵐᵒᵖ (Mi i)]

variable (Ni : ι → Type uN) [∀ i, AddCommMonoid (Ni i)]

variable [∀ i, Module (Ri i)ᵐᵒᵖ (Ni i)]

theorem piRightHomAddEquiv_id (i : ι) :
    piRightHomAddEquiv Ri Mi Mi
      (@LinearMap.id (∀ i, Ri i)ᵐᵒᵖ (∀ i, Mi i) _ _ (piRightModule Ri Mi)) i =
        LinearMap.id := by
  classical
  apply LinearMap.ext
  intro m
  simp only [piRightHomAddEquiv_apply, LinearMap.id_apply, Pi.single_eq_same]

end Pi
end Module
end
