public section

open TensorProduct

namespace TauCeti.DynkinType

universe v v'

noncomputable section

attribute [local instance 100] LieRing.ofAssociativeRing

attribute [local instance] TauCeti.moduleNNRat

attribute [local instance high] Algebra.toModule

variable (t : DynkinType) (ht : t.Valid)

/-- **The pinned simple Weyl representative in the Geck carrier.**  At node `i` this is
`xᵢ(1) x₋ᵢ(-1) xᵢ(1)`. -/
def geckSimpleWeylPoint (i : Fin t.rank) (A : Type v) [CommRing A] : t.geckPoints ht A :=
  (MulEquiv.subgroupCongr (geckPoints_eq_kostantToralPointsSubgroup t ht A).symm)
    (UniversalEnvelopingAlgebra.kostantToralWeylPoint
      (t.lieBasis ht).rootGenerator (t.lieBasis ht).h (t.geckRepresentation ht)
      (t.geckCoordinateLattice ht).toAddSubgroup
      (t.geckRepresentation_kostantForm_mem_geckCoordinateLattice ht)
      (t.isNilpotent_geckRepresentation_rootGenerator ht)
      (t.geckCoordinateBasisFin ht) (t.geckWeightFin ht) (.inl i) (.inr i) A)

end
end TauCeti.DynkinType
end
