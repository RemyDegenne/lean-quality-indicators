@[expose] public section

namespace Domain.Neighborhood.Exercise114

open Domain.Neighborhood NeighborhoodSystem

/-- The finite element `↑X` for a neighbourhood `X` (Scott's finite elements). -/
def fin {X : Set ℕ} (h : neighborhoodSystem.mem X) : neighborhoodSystem.Element :=
  neighborhoodSystem.principal h

end Domain.Neighborhood.Exercise114
end
