namespace OAI

section

namespace Erdos3.FixedDensity

open scoped BigOperators

namespace SimplexHypergraph

theorem fullEdgeDeletion_isEdgeDeletion {k : ℕ}
    {V : Fin k → Type*} [∀ i, Fintype (V i)]
    (H : SimplexHypergraph V) :
    H.IsEdgeDeletion H.fullEdgeDeletion :=
  fun _ => Finset.Subset.rfl

end SimplexHypergraph
end Erdos3.FixedDensity
end
end OAI
