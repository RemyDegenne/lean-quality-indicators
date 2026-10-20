public section

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

open TopologicalSpace TopCat

namespace TopCat.Sheaf

variable {X : TopCat.{0}}

variable {I : Type} [SmallCategory I] [IsFiltered I]

variable [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{0}]

variable (F : I ⥤ Sheaf AddCommGrpCat.{0} X)

variable [CompactSpace X] [PrespectralSpace X] [QuasiSeparatedSpace X]

variable [hExt : HasExt.{0} (CategoryTheory.Sheaf
  (Opens.grothendieckTopology X) AddCommGrpCat.{0})]

/-- The terminal-sections complexes of the stagewise functorial flasque
resolutions. -/
noncomputable abbrev filteredFlasqueResolutionSectionsDiagram :
    I ⥤ CochainComplex AddCommGrpCat ℕ :=
  F ⋙ (flasqueResolutionNat (X := X)).asFunctor ⋙
    (SheafCohomology.CompactOpenSections.sections
      (X := X) (⊤ : Opens X)).mapHomologicalComplex (ComplexShape.up ℕ)

end TopCat.Sheaf
end
end
