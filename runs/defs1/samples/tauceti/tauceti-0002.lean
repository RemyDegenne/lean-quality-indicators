public section

namespace TauCeti

namespace TypeTwistedDLieIndex

noncomputable section

variable (d : TypeTwistedDLieIndex)

/-- The fixed subgroup of the Steinberg endomorphism of `²Dₙ(q)`. Its points are not the points
with entries in `𝔽_q`, which are the fixed points of the Frobenius factor alone. -/
abbrev FixedPoints : Type := ↥(fixedSubgroup d.steinberg)

end
end TypeTwistedDLieIndex
end TauCeti
end
