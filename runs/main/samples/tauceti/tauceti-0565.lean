public section

namespace Polynomial

open SignType Set

section Definitions

variable {R : Type*} [CommRing R] [LinearOrder R]

theorem cauchyIndex_def (p q : R[X]) (s : Set R) :
    cauchyIndex p q s = ∑ᶠ x ∈ s, cauchyJump p q x := (rfl)

end Definitions
end Polynomial
end
