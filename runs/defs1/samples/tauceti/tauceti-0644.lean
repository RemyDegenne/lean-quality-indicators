public section

noncomputable section

open CategoryTheory Limits SimplexCategory

open scoped Simplicial

universe u v w

namespace TauCeti

namespace LocalCoefficientSystem

variable {R : Type u} [Ring R] {X Y : TopCat.{v}} {m n p : SimplexCategoryᵒᵖ}

section Coefficients

variable {L K J : LocalCoefficientSystem.{u, v, max v w} R X}

/-- The morphism of twisted chains induced by a morphism of local coefficient systems. -/
def twistedChainsCoefficientMap (η : L ⟶ K) : twistedChains L ⟶ twistedChains K where
  app := twistedChainsCoefficientApp η
  naturality _ _ _ := by
    refine twistedChains_hom_ext _ fun σ ↦ ?_
    simp [ιTwistedChains_twistedChainsCoefficientApp,
      ιTwistedChains_twistedChainsCoefficientApp_assoc]

end Coefficients
end LocalCoefficientSystem
end TauCeti
end
end
