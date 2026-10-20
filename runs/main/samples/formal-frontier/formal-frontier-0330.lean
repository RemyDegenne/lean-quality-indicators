@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

open TopologicalSpace

open scoped Simplicial

noncomputable section

universe u

namespace AlgebraicTopology

theorem integralSingularChainMap_twoOpenIntersectionSwapMap
    {X : TopCat.{u}} (U V : Opens X) :
    integralSingularChainMap (twoOpenIntersectionSwapMap U V) =
      (twoOpenIntersectionSwapChainIso U V).hom := by
  have hswap : (twoOpenIntersectionSwapChainIso U V).hom =
      (twoOpenIntersectionChainIso U V).hom ≫
        (subcomplexInfSwapChainIso (TopCat.openSingularSet U)
          (TopCat.openSingularSet V)).hom ≫
        (twoOpenIntersectionChainIso V U).inv := by
    have h1 : (twoOpenSmallToAmbientIso U V).hom.τ₁ =
        (twoOpenIntersectionChainIso U V).hom := rfl
    have h2 : (subcomplexUnionSwapIso (TopCat.openSingularSet U)
        (TopCat.openSingularSet V)).hom.τ₁ =
        -(subcomplexInfSwapChainIso (TopCat.openSingularSet U)
          (TopCat.openSingularSet V)).hom := rfl
    have h3 : ((twoOpenSmallToAmbientIso V U).symm).hom.τ₁ =
        (twoOpenIntersectionChainIso V U).inv := rfl
    change -(((twoOpenSmallToAmbientIso U V).hom.τ₁ ≫
        (subcomplexUnionSwapIso (TopCat.openSingularSet U)
          (TopCat.openSingularSet V)).hom.τ₁) ≫
        ((twoOpenSmallToAmbientIso V U).symm).hom.τ₁) = _
    calc
      _ = (((twoOpenSmallToAmbientIso U V).hom.τ₁ ≫
          (-((subcomplexUnionSwapIso (TopCat.openSingularSet U)
            (TopCat.openSingularSet V)).hom.τ₁))) ≫
          ((twoOpenSmallToAmbientIso V U).symm).hom.τ₁) := by
        simp only [Preadditive.comp_neg, Preadditive.neg_comp]
      _ = _ := by
        rw [h1, h2, h3]
        erw [neg_neg]
        exact Category.assoc _ _ _
  have htransport : integralSingularChainMap
      (twoOpenIntersectionSwapMap U V) ≫
      (twoOpenIntersectionChainIso V U).hom =
    (twoOpenIntersectionChainIso U V).hom ≫
      (subcomplexInfSwapChainIso (TopCat.openSingularSet U)
        (TopCat.openSingularSet V)).hom := by
    let F := (SSet.chainComplexFunctor (ModuleCat.{u} ℤ)).obj
      integerCoefficients.{u}
    change F.map (TopCat.toSSet.map (twoOpenIntersectionSwapMap U V)) ≫
          (F.map (TopCat.openSingularSetIso (V ⊓ U)).hom ≫
            F.map (SSet.Subcomplex.eqToIso
              (TopCat.openSingularSet_inf V U).symm).hom) =
      (F.map (TopCat.openSingularSetIso (U ⊓ V)).hom ≫
        F.map (SSet.Subcomplex.eqToIso
          (TopCat.openSingularSet_inf U V).symm).hom) ≫
        F.map (SSet.Subcomplex.eqToIso
          (inf_comm (TopCat.openSingularSet U)
            (TopCat.openSingularSet V))).hom
    have h := congrArg (fun k ↦ F.map k)
      (twoOpenIntersectionSwapMap_sset U V)
    simpa only [Functor.map_comp, Category.assoc] using h
  rw [hswap]
  apply (cancel_mono (twoOpenIntersectionChainIso V U).hom).1
  rw [htransport]
  have hcancel :
      (((subcomplexInfSwapChainIso (TopCat.openSingularSet U)
          (TopCat.openSingularSet V)).hom ≫
        (twoOpenIntersectionChainIso V U).inv) ≫
        (twoOpenIntersectionChainIso V U).hom) =
      (subcomplexInfSwapChainIso (TopCat.openSingularSet U)
        (TopCat.openSingularSet V)).hom := by
    let b := (subcomplexInfSwapChainIso (TopCat.openSingularSet U)
      (TopCat.openSingularSet V)).hom
    let e := twoOpenIntersectionChainIso V U
    exact (Category.assoc b e.inv e.hom).trans
      ((congrArg (b ≫ ·) e.inv_hom_id).trans (Category.comp_id b))
  exact congrArg ((twoOpenIntersectionChainIso U V).hom ≫ ·) hcancel.symm

end AlgebraicTopology
end
end
