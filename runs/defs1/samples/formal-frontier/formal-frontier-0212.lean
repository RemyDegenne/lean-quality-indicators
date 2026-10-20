public section

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

open TopologicalSpace TopCat

namespace TopCat.Sheaf

variable {X : TopCat.{0}}

variable {I : Type} [SmallCategory I] [IsFiltered I]

variable [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{0}]

variable (F : I ⥤ Sheaf AddCommGrpCat.{0} X)

/-- Evaluation of the complex of diagrams at a stage agrees with that stage's
functorial flasque resolution. -/
@[expose] noncomputable def filteredFlasqueResolutionComplexDiagramEvalIso (i : I) :
    (((evaluation I (Sheaf AddCommGrpCat X)).obj i).mapHomologicalComplex
      (ComplexShape.up ℕ)).obj
        (filteredFlasqueResolutionComplexDiagram F) ≅
      flasqueResolution (F.obj i) :=
  HomologicalComplex.Hom.isoOfComponents (fun _ => Iso.refl _)

end TopCat.Sheaf
end
end
