@[expose] public section

universe u v w z

namespace IsCoveringMap

variable {E : Type u} {B : Type v} [TopologicalSpace E] [TopologicalSpace B]
  {p : E → B} (cov : IsCoveringMap p)

/-- For path-connected, locally path-connected total space, restriction identifies the
deck group with the monodromy centralizer on the fiber containing a specified point.
This is the occupied-fiber form of May, Chapter 3, §7, p. 29. The base need not be path
connected or locally path connected, and the covering need not be surjective. -/
noncomputable def deckMonodromyEquivOfPathConnected [PathConnectedSpace E]
    [LocallyPathConnectedSpace E] (e₀ : E) :
    deck p ≃* Subgroup.centralizer (Set.range (cov.monodromyPerm (p e₀))) :=
  MulEquiv.ofBijective (cov.deckMonodromyHom (p e₀)) ⟨by
    intro g h hgh
    apply (deck.evalEmbedding cov.isSeparatedMap
      cov.isLocalHomeomorph.isLocallyInjective e₀).injective
    apply Subtype.ext
    exact congrArg (fun α ↦ (α.val ⟨e₀, rfl⟩).val) hgh, by
    intro α
    obtain ⟨g, hg⟩ := cov.exists_deck_smul_eq_of_pathConnected e₀ α
    exact ⟨g, Subtype.ext (Equiv.ext fun e ↦ Subtype.ext (hg e))⟩⟩

end IsCoveringMap
end
