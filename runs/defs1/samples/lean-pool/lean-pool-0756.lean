@[expose] public section

namespace Domain.Neighborhood.Example23

open Domain.Neighborhood NeighborhoodSystem ExampleB

/-- Scott's `⊥`: the unique partial element `{Δ}` of `T`. -/
def botElt : T.Element := Example12.neighborhoodSystem.bot

end Domain.Neighborhood.Example23
end
