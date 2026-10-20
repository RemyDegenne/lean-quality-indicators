public section

open AlgebraicGeometry CategoryTheory TensorProduct WithConv

open scoped CategoryTheory.MonObj

namespace TauCeti.DynkinType

universe v

noncomputable section

attribute [local instance 100] LieRing.ofAssociativeRing

attribute [local instance] TauCeti.moduleNNRat

attribute [local instance high] Algebra.toModule

variable (t : DynkinType) (ht : t.Valid)

@[ext]
theorem geckGroupScheme_hom_ext {Y : _root_.CommHopfAlgCat.{0} ℤ}
    (φ ψ : t.geckGroupScheme ht ⟶
      (hopfSpec (CommRingCat.of ℤ)).obj (Opposite.op Y))
    (hroot : ∀ i, t.geckRootSubgroup ht i ≫ φ = t.geckRootSubgroup ht i ≫ ψ)
    (htorus : t.geckWeightTorus ht ≫ φ = t.geckWeightTorus ht ≫ ψ) :
    φ = ψ := by
  apply (cancel_epi (eqToHom (t.geckGroupScheme_def ht).symm)).1
  apply TauCeti.UniversalEnvelopingAlgebra.kostantToralGroupScheme_hom_ext
    (t.lieBasis ht).rootGenerator (t.lieBasis ht).h (t.geckRepresentation ht)
    (t.geckCoordinateLattice ht).toAddSubgroup
    (t.geckRepresentation_kostantForm_mem_geckCoordinateLattice ht)
    (t.isNilpotent_geckRepresentation_rootGenerator ht)
    (t.geckCoordinateBasisFin ht) (t.geckWeightFin ht)
    (eqToHom (t.geckGroupScheme_def ht).symm ≫ φ)
    (eqToHom (t.geckGroupScheme_def ht).symm ≫ ψ)
  · intro i
    simpa only [geckRootSubgroup_def, Category.assoc] using hroot i
  · simpa only [geckWeightTorus_def, Category.assoc] using htorus

end
end TauCeti.DynkinType
end
