public section

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

open TopologicalSpace TopCat

namespace TopCat.Sheaf

variable {X : TopCat.{0}}

section AcyclicResolutionSections

variable [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{0}]

variable [hExt : HasExt.{0} (CategoryTheory.Sheaf
  (Opens.grothendieckTopology X) AddCommGrpCat.{0})]

variable {A B : CategoryTheory.Sheaf
  (Opens.grothendieckTopology X) AddCommGrpCat.{0}}

@[reassoc]
lemma _root_.CategoryTheory.Abelian.Ext.AcyclicResolution.coyonedaIsoSectionsHomology_hom_naturality
    (R : Abelian.Ext.AcyclicResolution
      ((constantSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{0}).obj
        ↧(ULift ℤ)) A)
    (R' : Abelian.Ext.AcyclicResolution
      ((constantSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{0}).obj
        ↧(ULift ℤ)) B)
    (f : R.cocomplex ⟶ R'.cocomplex) (q : ℕ) :
    HomologicalComplex.homologyMap (R.homComplexMap R' f) q ≫
        (HomologicalComplex.homologyMapIso
          ((NatIso.mapHomologicalComplex (coyonedaIsoSections (X := X))
            (ComplexShape.up ℕ)).app R'.cocomplex) q).hom =
      (HomologicalComplex.homologyMapIso
        ((NatIso.mapHomologicalComplex (coyonedaIsoSections (X := X))
          (ComplexShape.up ℕ)).app R.cocomplex) q).hom ≫
        HomologicalComplex.homologyMap
          (((SheafCohomology.CompactOpenSections.sections
            (X := X) (⊤ : Opens X)).mapHomologicalComplex
            (ComplexShape.up ℕ)).map f) q := by
  change
    HomologicalComplex.homologyMap (R.homComplexMap R' f) q ≫
        HomologicalComplex.homologyMap
          ((NatIso.mapHomologicalComplex (coyonedaIsoSections (X := X))
            (ComplexShape.up ℕ)).hom.app R'.cocomplex) q =
      HomologicalComplex.homologyMap
          ((NatIso.mapHomologicalComplex (coyonedaIsoSections (X := X))
            (ComplexShape.up ℕ)).hom.app R.cocomplex) q ≫
        HomologicalComplex.homologyMap
          (((SheafCohomology.CompactOpenSections.sections
            (X := X) (⊤ : Opens X)).mapHomologicalComplex
            (ComplexShape.up ℕ)).map f) q
  rw [← HomologicalComplex.homologyMap_comp,
    ← HomologicalComplex.homologyMap_comp]
  exact congrArg (fun g => HomologicalComplex.homologyMap g q)
    ((NatIso.mapHomologicalComplex (coyonedaIsoSections (X := X))
      (ComplexShape.up ℕ)).hom.naturality f)

end AcyclicResolutionSections
end TopCat.Sheaf
end
end
