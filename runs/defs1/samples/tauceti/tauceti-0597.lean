public section

namespace TauCeti

namespace TypeTwistedDLieIndex

noncomputable section

variable (d : TypeTwistedDLieIndex)

/-- **The finite-simple-group candidate attached to `²Dₙ(q)`, formed on the spin carrier**: the
derived subgroup of the fixed points of its Steinberg map, modulo the centre of that derived
subgroup. It becomes the candidate on the pinned simply connected group along an identification of
the spin carrier with that group, as the module docstring describes. No finiteness or simplicity
assertion is part of this definition. -/
abbrev Group : Type := FixedPointCandidate d.steinberg

end
end TypeTwistedDLieIndex
end TauCeti
end
