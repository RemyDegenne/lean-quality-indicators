public section

noncomputable section

open scoped unitInterval

open Topology

variable {X : Type*} [TopologicalSpace X] (x₀ : X)

namespace TauCeti.UniversalCover

/-- **The quotient of the universal cover by the trivial subgroup is the universal cover.** The
underlying map is the quotient map `subgroupQuotientMap x₀ ⊥`, so the identification is one over
`X`. -/
def subgroupQuotientBotHomeomorph [LocallyPathConnectedSpace X]
    [SemilocallySimplyConnectedSpace X] :
    UniversalCover x₀ ≃ₜ SubgroupQuotient x₀ (⊥ : Subgroup (FundamentalGroup X x₀)) :=
  Equiv.toHomeomorphOfContinuousOpen
    (Equiv.ofBijective (subgroupQuotientMap x₀ ⊥) (by
      have h : subgroupQuotientMap x₀ (⊥ : Subgroup (FundamentalGroup X x₀)) =
          ⇑(TauCeti.MulAction.orbitRelQuotientBotEquiv
            (G := FundamentalGroup X x₀) (X := UniversalCover x₀)).symm := by
        funext e
        simp
      rw [h]
      exact (TauCeti.MulAction.orbitRelQuotientBotEquiv
        (G := FundamentalGroup X x₀) (X := UniversalCover x₀)).symm.bijective))
    (isQuotientCoveringMap_subgroupQuotientMap x₀ ⊥).isCoveringMap.continuous
    (isQuotientCoveringMap_subgroupQuotientMap x₀ ⊥).isCoveringMap.isLocalHomeomorph.isOpenMap

end TauCeti.UniversalCover
end
end
