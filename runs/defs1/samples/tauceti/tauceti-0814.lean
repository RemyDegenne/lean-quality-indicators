public section

noncomputable section

open CategoryTheory MulOpposite ContinuousMap

namespace TauCeti

universe u

section Module

variable {Y Y' : Type u} {G : Type*} [TopologicalSpace Y] [TopologicalSpace Y']
  [Monoid G] [TopologicalSpace G] [ContinuousMul G]
  [MulAction Gᵐᵒᵖ Y] [ContinuousSMul Gᵐᵒᵖ Y] [MulAction Gᵐᵒᵖ Y'] [ContinuousSMul Gᵐᵒᵖ Y']
  (R : Type u) [CommRing R]

/-- The component in dimension `n` of the homotopy `g ∘ f ≃ 1` of normalized cubical chains
induced by a homotopy equivalence `e`. -/
def homotopyEquivChainHomotopy (e : Y ≃ₕ Y') (n : ℕ) :
    NormalizedCubicalChain Y R n →ₗ[R] NormalizedCubicalChain Y R (n + 1) :=
  ((HomotopyEquiv.normalizedCubicalChainComplexHomotopyEquiv R e).homotopyHomInvId.hom n
    (n + 1)).hom

end Module
end TauCeti
end
end
