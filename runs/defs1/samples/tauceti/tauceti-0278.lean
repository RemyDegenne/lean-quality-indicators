public section

open Finset

namespace TauCeti

/-- An **`r`-uniform hypergraph** on `V`: a finite set of unordered edges, each an `r`-element
finset of vertices. -/
structure UniformHypergraph (r : ℕ) (V : Type*) where
  /-- The edges. -/
  edges : Finset (Finset V)
  /-- Every edge has exactly `r` vertices. -/
  edge_card : ∀ e ∈ edges, e.card = r

end TauCeti
end
