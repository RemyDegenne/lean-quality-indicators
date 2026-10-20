@[expose] public section

namespace Domain.Neighborhood.Exercise112

open Domain.Neighborhood NeighborhoodSystem

@[simp] theorem mem_top {X : Set ℕ} : top.mem X ↔ neighborhoodSystem.mem X := Iff.rfl

end Domain.Neighborhood.Exercise112
end
