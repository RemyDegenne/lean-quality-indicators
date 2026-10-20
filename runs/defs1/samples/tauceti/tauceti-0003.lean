public section

noncomputable section

open CategoryTheory Limits Set Topology Topology.RelCWComplex

universe w

namespace TauCeti

variable {X : Type w} [TopologicalSpace X] [T2Space X] {D : Set X} (C : Set X) [RelCWComplex C D]

/-- The inclusions of the skeleta into the whole complex. -/
@[expose] def skeletonCocone : Cocone (skeletonFunctor C) where
  pt := TopCat.of C
  ι := { app j := TopCat.ofHom (ContinuousMap.inclusion (skeletonLT C (j : ℕ∞)).subset_complex) }

end TauCeti
end
end
