public section

set_option warningAsError true

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

noncomputable section

universe u

namespace TopCat.Sheaf.RightDerivedPushforward

local instance presheafToSheaf_preservesZero_sheafification
    {Y : TopCat.{u}}
    [HasSheafify (Opens.grothendieckTopology Y) AddCommGrpCat.{u}] :
    (presheafToSheaf (Opens.grothendieckTopology Y)
      AddCommGrpCat.{u}).PreservesZeroMorphisms :=
  Functor.preservesZeroMorphisms_of_additive
    (presheafToSheaf (Opens.grothendieckTopology Y) AddCommGrpCat.{u})

noncomputable local instance presheafToSheaf_preservesHomology_sheafification
    {Y : TopCat.{u}}
    [HasSheafify (Opens.grothendieckTopology Y) AddCommGrpCat.{u}] :
    (presheafToSheaf (Opens.grothendieckTopology Y)
      AddCommGrpCat.{u}).PreservesHomology := inferInstance

variable {X Y : TopCat.{u}} (f : X ⟶ Y)

variable [HasSheafify
  (Opens.grothendieckTopology X) AddCommGrpCat.{u}]

variable [HasSheafify
  (Opens.grothendieckTopology Y) AddCommGrpCat.{u}]

variable [HasExt.{u} (CategoryTheory.Sheaf
  (Opens.grothendieckTopology X) AddCommGrpCat.{u})]

variable (G : CategoryTheory.Sheaf
  (Opens.grothendieckTopology X) AddCommGrpCat.{u})

section CoefficientNaturality

variable {G₁ G₂ : CategoryTheory.Sheaf
  (Opens.grothendieckTopology X) AddCommGrpCat.{u}}

@[reassoc]
lemma sheafifiedLocalCohomologyIsoRightDerivedObj_hom_coefficient_naturality
    (a : G₁ ⟶ G₂) (q : ℕ) (hq : 0 < q) :
    ((TopCat.Sheaf.sheafifiedLocalCohomologyFunctor f q).map a) ≫
        (sheafifiedLocalCohomologyIsoRightDerivedObj f G₂ q hq).hom =
      (sheafifiedLocalCohomologyIsoRightDerivedObj f G₁ q hq).hom ≫
        ((TopCat.Sheaf.pushforward AddCommGrpCat.{u} f).rightDerived q).map a := by
  have hcomp :
      (((TopCat.Sheaf.sheafifiedLocalCohomologyFunctor f q).map a ≫
          (sheafifiedLocalCohomologyIsoPushforwardResolutionHomology
            f G₂ q hq).hom) ≫
        (pushforwardIsoRightDerivedObj f G₂ q).inv) =
      (((sheafifiedLocalCohomologyIsoPushforwardResolutionHomology
            f G₁ q hq).hom ≫
        (pushforwardIsoRightDerivedObj f G₁ q).inv) ≫
        ((TopCat.Sheaf.pushforward AddCommGrpCat.{u} f).rightDerived q).map a) := by
    have h₁ :=
      sheafifiedLocalCohomologyIsoPushforwardResolutionHomology_hom_coefficient_naturality
        f a q hq
    have h₂ := pushforwardIsoRightDerivedObj_inv_coefficient_naturality f a q
    have h₂' :
        (((sheafifiedLocalCohomologyIsoPushforwardResolutionHomology
              f G₁ q hq).hom ≫
            HomologicalComplex.homologyMap
              (pushforwardResolutionSheafComplexMap f a) q) ≫
          (pushforwardIsoRightDerivedObj f G₂ q).inv) =
        (((sheafifiedLocalCohomologyIsoPushforwardResolutionHomology
              f G₁ q hq).hom ≫
            (pushforwardIsoRightDerivedObj f G₁ q).inv) ≫
          ((TopCat.Sheaf.pushforward AddCommGrpCat.{u} f).rightDerived q).map a) := by
      exact (Category.assoc _ _ _).trans
        ((congrArg
          (fun k =>
            (sheafifiedLocalCohomologyIsoPushforwardResolutionHomology
              f G₁ q hq).hom ≫ k) h₂).trans
          (Category.assoc _ _ _).symm)
    have h₁' := congrArg
      (fun k => k ≫ (pushforwardIsoRightDerivedObj f G₂ q).inv) h₁
    exact h₁'.trans h₂'
  have e₁ :
      (sheafifiedLocalCohomologyIsoRightDerivedObj f G₁ q hq).hom =
        (sheafifiedLocalCohomologyIsoPushforwardResolutionHomology
            f G₁ q hq).hom ≫
          (pushforwardIsoRightDerivedObj f G₁ q).inv := rfl
  have e₂ :
      (sheafifiedLocalCohomologyIsoRightDerivedObj f G₂ q hq).hom =
        (sheafifiedLocalCohomologyIsoPushforwardResolutionHomology
            f G₂ q hq).hom ≫
          (pushforwardIsoRightDerivedObj f G₂ q).inv := rfl
  refine (congrArg
    (fun k => (TopCat.Sheaf.sheafifiedLocalCohomologyFunctor f q).map a ≫ k)
      e₂).trans ?_
  refine (Category.assoc _ _ _).symm.trans ?_
  refine hcomp.trans ?_
  exact congrArg
    (fun k => k ≫
      ((TopCat.Sheaf.pushforward AddCommGrpCat.{u} f).rightDerived q).map a)
      e₁.symm

end CoefficientNaturality
end TopCat.Sheaf.RightDerivedPushforward
end
end
