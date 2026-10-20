@[expose] public section

open CategoryTheory Limits AlgebraicTopology

open scoped Simplicial

noncomputable section

namespace TopCat

universe u

open ContinuousMap

theorem reducedSingularHomologyZeroMap_eq_of_homotopy {X Y : TopCat.{u}}
    {f g : X ⟶ Y} (H : TopCat.Homotopy f g) :
    reducedSingularHomologyZeroMap f = reducedSingularHomologyZeroMap g := by
  apply (cancel_mono (reducedSingularHomologyZeroι Y)).1
  simp only [reducedSingularHomologyZeroMap_ι]
  have h := H.congr_homologyMap_singularChainComplexFunctor
    singularHomologyIntegerCoefficients 0
  change reducedSingularHomologyZeroι X ≫
      HomologicalComplex.homologyMap
        (((singularChainComplexFunctor (ModuleCat.{u, 0} ℤ)).obj
          singularHomologyIntegerCoefficients).map f) 0 =
    reducedSingularHomologyZeroι X ≫
      HomologicalComplex.homologyMap
        (((singularChainComplexFunctor (ModuleCat.{u, 0} ℤ)).obj
          singularHomologyIntegerCoefficients).map g) 0
  rw [h]

end TopCat
end
end
