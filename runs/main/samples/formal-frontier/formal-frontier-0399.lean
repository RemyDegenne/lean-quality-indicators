@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

open TopologicalSpace

open scoped Simplicial

noncomputable section

universe u

namespace AlgebraicTopology

theorem twoOpenMayerVietorisFromIntersection_fst {X : TopCat.{u}}
    (U V : Opens X) (n : ℕ) :
    twoOpenMayerVietorisFromIntersection U V n ≫ biprod.fst =
      (twoOpenIntersectionHomologyIso U V n).inv ≫
        HomologicalComplex.homologyMap
          (integralSingularChainMap (twoOpenIntersectionToLeft U V)) n := by
  simp only [twoOpenMayerVietorisFromIntersection,
    twoOpenIntersectionHomologyIso, twoOpenSmallShortComplex_f_eq_difference,
    twoOpenDifferenceChainMap, twoOpenMiddleHomologyIso,
    Iso.refl_inv]
  erw [Category.assoc, biprod.lift_fst]
  erw [← HomologicalComplex.homologyMap_comp, biprod.lift_fst]
  exact (Category.id_comp _).symm

end AlgebraicTopology
end
end
