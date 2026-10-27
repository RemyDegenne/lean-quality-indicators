@[expose] public section

open scoped BigOperators Topology goldenRatio

open Filter Set

namespace Erdos346

noncomputable section

/-- Sum of the deleted terms up to index `n`. -/
def deletedPrefixSum (a : ℕ → ℕ) (D : Set ℕ) (n : ℕ) : ℕ :=
  by
    classical
    exact ∑ i ∈ (Finset.range (n + 1)).filter (fun i => i ∈ D), a i

end
end Erdos346
end
