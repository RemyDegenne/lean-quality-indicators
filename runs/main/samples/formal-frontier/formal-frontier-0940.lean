@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

open TopologicalSpace

open scoped Simplicial

noncomputable section

universe u

namespace AlgebraicTopology

@[reassoc]
theorem twoOpenReducedMayerVietorisFromBiprodZero_naturality
    {X Y : TopCat.{u}} (f : X ⟶ Y)
    (U V : Opens X) (U' V' : Opens Y)
    (hU : Set.MapsTo f U U') (hV : Set.MapsTo f V V') :
    twoOpenReducedMayerVietorisFromBiprodZero U V ≫
        TopCat.reducedSingularHomologyMap f 0 =
      biprod.map
          (TopCat.reducedSingularHomologyMap (TopCat.openMap f U U' hU) 0)
          (TopCat.reducedSingularHomologyMap (TopCat.openMap f V V' hV) 0) ≫
        twoOpenReducedMayerVietorisFromBiprodZero U' V' := by
  apply biprod.hom_ext'
  · simp only [twoOpenReducedMayerVietorisFromBiprodZero_inl_assoc,
      biprod.inl_map_assoc, twoOpenReducedMayerVietorisFromBiprodZero_inl]
    rw [← Functor.map_comp, ← Functor.map_comp, TopCat.openMap_comp_inclusion]
  · simp only [twoOpenReducedMayerVietorisFromBiprodZero_inr_assoc,
      biprod.inr_map_assoc, twoOpenReducedMayerVietorisFromBiprodZero_inr]
    rw [← Functor.map_comp, ← Functor.map_comp, TopCat.openMap_comp_inclusion]

end AlgebraicTopology
end
end
