@[expose] public section

namespace Domain.Neighborhood.Exercise115

open Domain.Neighborhood NeighborhoodSystem

/-- **Exercise 1.15 — the stem domain.** `𝒟 = {ℕ, {0,1}} ∪ {{n}}`. -/
def stem : NeighborhoodSystem ℕ :=
  ofNestedOrDisjoint stemMem Set.univ (Or.inl rfl) stemNOD (fun _ => Set.subset_univ _)

end Domain.Neighborhood.Exercise115
end
