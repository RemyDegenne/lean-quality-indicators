@[expose] public section

universe u v w z

namespace IsCoveringMap

variable {E : Type u} {B : Type v} [TopologicalSpace E] [TopologicalSpace B]
  {p : E → B} (cov : IsCoveringMap p)

theorem deckMonodromyEquiv_eq_of_pathConnected [PathConnectedSpace B] [PathConnectedSpace E]
    [LocallyPathConnectedSpace E] (e₀ : E) :
    cov.deckMonodromyEquiv (p e₀) = cov.deckMonodromyEquivOfPathConnected e₀ := by
  apply MulEquiv.ext
  intro g
  rfl

end IsCoveringMap
end
