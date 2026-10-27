public section

namespace TauCeti

namespace TypeBLieIndex

variable (d : TypeBLieIndex)

noncomputable section

/-- **The finite-simple-group candidate attached to a type-`B` index**: the derived subgroup of
the Steinberg fixed points, modulo the centre of that derived subgroup. No finiteness or
simplicity assertion is part of this definition, nor any identification of the spin carrier with
the pinned simply connected group scheme of type `Bₙ`. -/
abbrev Group : Type := FixedPointCandidate d.steinberg

end
end TypeBLieIndex
end TauCeti
end
