public section

namespace TauCeti

open AddSubgroup

namespace Deck

variable {𝕜 : Type*} [AddCommGroup 𝕜] [TopologicalSpace 𝕜] [IsTopologicalAddGroup 𝕜]
  {p : 𝕜}

/-- Right translation by elements of the period subgroup, as a monoid homomorphism from the
multiplicatively written `zmultiples p` to the deck transformation group of
`(↑) : 𝕜 → AddCircle p`. This bundles `addRightZMultiples`. -/
@[expose] def addRightZMultiplesHom :
    Multiplicative (zmultiples p) →* deck ((↑) : 𝕜 → AddCircle p) where
  toFun a := addRightZMultiples a.toAdd
  map_one' := addRightZMultiples_zero
  map_mul' _ _ := addRightZMultiples_add _ _

end Deck
end TauCeti
end
