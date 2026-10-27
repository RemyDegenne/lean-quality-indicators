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

/-- Positive-degree cohomology computed by an acyclic resolution is the
homology of that resolution after taking terminal-open sections. -/
@[expose] noncomputable def _root_.CategoryTheory.Abelian.Ext.AcyclicResolution.positiveIsoSectionsHomology
    (R : Abelian.Ext.AcyclicResolution
      ((constantSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{0}).obj
        ↧(ULift ℤ)) A)
    (q : ℕ) (hq : 0 < q) :
    (CategoryTheory.Sheaf.functorH
        (Opens.grothendieckTopology X) q).obj A ≅
      (((SheafCohomology.CompactOpenSections.sections
        (X := X) (⊤ : Opens X)).mapHomologicalComplex
        (ComplexShape.up ℕ)).obj R.cocomplex).homology q :=
  R.extPositiveIsoHomologyIso q hq ≪≫
    HomologicalComplex.homologyMapIso
      ((NatIso.mapHomologicalComplex (coyonedaIsoSections (X := X))
        (ComplexShape.up ℕ)).app R.cocomplex) q

end AcyclicResolutionSections
end TopCat.Sheaf
end
end
