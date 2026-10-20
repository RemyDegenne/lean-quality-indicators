public section

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

open TopologicalSpace TopCat

namespace TopCat.Sheaf

variable {X : TopCat.{0}}

variable {I : Type} [SmallCategory I] [IsFiltered I]

variable [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{0}]

variable (F : I ⥤ Sheaf AddCommGrpCat.{0} X)

/-- The augmentation from the colimit sheaf to the degreewise colimit of the
stagewise flasque resolutions. -/
@[expose] noncomputable def filteredFlasqueResolutionAugmentation :
    (CochainComplex.single₀ (Sheaf AddCommGrpCat X)).obj (colimit F) ⟶
      filteredFlasqueResolution F :=
  (HomologicalComplex.singleMapHomologicalComplex
      (colim (J := I) (C := Sheaf AddCommGrpCat X))
      (ComplexShape.up ℕ) 0).inv.app F ≫
    ((colim (J := I) (C := Sheaf AddCommGrpCat X)).mapHomologicalComplex
      (ComplexShape.up ℕ)).map
        (filteredFlasqueResolutionDiagramAugmentation F)

end TopCat.Sheaf
end
end
