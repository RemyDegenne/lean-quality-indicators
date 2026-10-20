public section

namespace TauCeti.UniversalCover

open _root_.FundamentalGroup

variable {X : Type*} [TopologicalSpace X] [PathConnectedSpace X] [LocallyPathConnectedSpace X]
  [SemilocallySimplyConnectedSpace X] (x₀ : X)

omit [PathConnectedSpace X] in
theorem exists_homeomorph_subgroupQuotient_of_range_eq {E : Type*} [TopologicalSpace E]
    [PathConnectedSpace E] {p : E → X} (hp : IsCoveringMap p)
    {e₀ : E} (hpe : p e₀ = x₀) (H : Subgroup (FundamentalGroup X x₀))
    (hH : (mapOfEq ⟨p, hp.continuous⟩ hpe).range = H) :
    ∃ h : E ≃ₜ SubgroupQuotient x₀ H, h e₀ = SubgroupQuotient.basepoint x₀ H ∧
      subgroupQuotientProj x₀ H ∘ h = p := by
  have := hp.isLocalHomeomorph.locallyPathConnectedSpace
  have := locallyPathConnectedSpace_subgroupQuotient x₀ H
  exact IsCoveringMap.exists_homeomorph_comp_eq_of_range_eq hp
    (isCoveringMap_subgroupQuotientProj x₀ H) hpe (subgroupQuotientProj_basepoint x₀ H)
    (hH.trans (range_mapOfEq_subgroupQuotientProj x₀ H).symm)

end TauCeti.UniversalCover
end
