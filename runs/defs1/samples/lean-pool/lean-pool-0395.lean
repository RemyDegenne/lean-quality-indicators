@[expose] public section

namespace Domain.Neighborhood.Example23

open Domain.Neighborhood NeighborhoodSystem ExampleB

/-- The codomain element selected by a parity reading: `none ↦ ⊥`, `some true ↦
true`,
`some false ↦ false`. -/
def valElt : Option Bool → T.Element
  | none => botElt
  | some true => trueElt
  | some false => falseElt

end Domain.Neighborhood.Example23
end
