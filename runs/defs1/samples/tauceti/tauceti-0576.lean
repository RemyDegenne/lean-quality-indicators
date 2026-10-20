public section

open AlgebraicGeometry CategoryTheory

namespace TauCeti.DynkinType

noncomputable section

variable (t : DynkinType) (ht : t.Valid)

/-- **The defining Hopf ideal of the positive Geck carrier.** It is the largest Hopf ideal in the
coordinate algebra of the ambient general linear group killed by the positive simple-root maps and
the represented weight-torus map. -/
def geckTorusPositiveDefiningIdeal :
    HopfIdeal ℤ (GeneralLinear.coordinateHopfAlgebra ℤ (t.geckDim ht)) :=
  UniversalEnvelopingAlgebra.kostantTorusSubsystemDefiningIdeal
    (t.lieBasis ht).rootGenerator (t.lieBasis ht).h (t.geckRepresentation ht)
    (t.geckCoordinateLattice ht).toAddSubgroup
    (t.geckRepresentation_kostantForm_mem_geckCoordinateLattice ht)
    (t.geckCoordinateBasisFin ht) (t.geckWeightFin ht) (Set.range Sum.inl)
    (fun i => t.isNilpotent_geckRepresentation_rootGenerator ht i.1)

end
end TauCeti.DynkinType
end
