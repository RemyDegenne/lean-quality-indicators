public section

namespace TauCeti.DynkinType

open Function Set

/-- The squared lengths of the eight roots of the pinned rank-two type `B` datum, normalised as
`TauCeti.DynkinType.rootLength` normalises the simple ones: `1` on the four short roots
`± α₁, ± (α₀ + α₁)` and `2` on the four long ones `± α₀, ± (α₀ + 2 α₁)`. -/
@[expose] def b2Length : Fin 8 → ℤ := ![2, 1, 1, 2, 2, 1, 1, 2]

end TauCeti.DynkinType
end
