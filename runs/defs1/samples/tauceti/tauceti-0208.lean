public section

namespace TauCeti

open Module

variable {n : ℕ}

/-- **The integer character `χ^μ` of the Specht module** `S^μ`. The character of `S^μ` takes
rational values, and those values are integers (`FDRep.intCharacter`); this is the
integer-valued refinement, related to the rational character by `TauCeti.spechtChar_cast`. -/
noncomputable def spechtChar (μ : n.Partition) : Equiv.Perm (Fin n) → ℤ :=
  FDRep.intCharacter (spechtModule μ)

end TauCeti
end
