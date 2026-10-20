public section

open AlgebraicGeometry CategoryTheory

namespace TauCeti.DynkinType

noncomputable section

variable (t : DynkinType) (ht : t.Valid)

theorem geckTorusPositiveDefiningIdeal_def :
    t.geckTorusPositiveDefiningIdeal ht =
      UniversalEnvelopingAlgebra.kostantTorusSubsystemDefiningIdeal
        (t.lieBasis ht).rootGenerator (t.lieBasis ht).h (t.geckRepresentation ht)
        (t.geckCoordinateLattice ht).toAddSubgroup
        (t.geckRepresentation_kostantForm_mem_geckCoordinateLattice ht)
        (t.geckCoordinateBasisFin ht) (t.geckWeightFin ht) (Set.range Sum.inl)
        (fun i => t.isNilpotent_geckRepresentation_rootGenerator ht i.1) := (rfl)

end
end TauCeti.DynkinType
end
