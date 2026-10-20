public section

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

open TopologicalSpace TopCat

namespace TopCat.Sheaf

variable {X : TopCat.{0}}

variable [CompactSpace X] [QuasiSeparatedSpace X] [PrespectralSpace X]

variable [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat]

variable [HasExt (CategoryTheory.Sheaf
  (Opens.grothendieckTopology X) AddCommGrpCat)]

/-- A sheaf morphism induces the corresponding map between the complexes of
terminal-open sections of their functorial flasque resolutions. -/
noncomputable abbrev flasqueResolutionSectionsMap
    {F G : Sheaf AddCommGrpCat X} (f : F ⟶ G) :
    flasqueResolutionSections F ⟶ flasqueResolutionSections G :=
  ((SheafCohomology.CompactOpenSections.sections
    (⊤ : Opens X)).mapHomologicalComplex (ComplexShape.up ℕ)).map
      ((flasqueResolutionNat (X := X)).asFunctor.map f)

end TopCat.Sheaf
end
end
