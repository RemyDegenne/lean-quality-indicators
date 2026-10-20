@[expose] public section

namespace Domain.Neighborhood.Exercise425

open Domain.Neighborhood NeighborhoodSystem ApproximableMap

theorem shift_singleton (n : ℕ) : shift ({n} : Set ℕ) = {n + 1} := by
  ext k
  simp only [shift, Set.mem_singleton_iff, Set.mem_ofPred_eq]
  simp_all

end Domain.Neighborhood.Exercise425
end
