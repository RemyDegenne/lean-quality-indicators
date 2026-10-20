public section

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

open TopologicalSpace

universe u v

namespace SheafCohomology.DegreeZero

variable {X : Type u} [TopologicalSpace X]

variable [HasSheafify
  (Opens.grothendieckTopology X) AddCommGrpCat.{v}]

variable [HasExt.{v} (CategoryTheory.Sheaf
  (Opens.grothendieckTopology X) AddCommGrpCat.{v})]

variable [UnivLE.{u, v}]

variable [(Opens.grothendieckTopology X).WEqualsLocallyBijective
  AddCommGrpCat.{v}]

variable {I : Type v} [SmallCategory I] [IsFiltered I]

variable (F : I ⥤ CategoryTheory.Sheaf
  (Opens.grothendieckTopology X) AddCommGrpCat.{v})

theorem preservesColimit_functorH_zero
    [CompactSpace X] [PrespectralSpace X] [QuasiSeparatedSpace X] :
    PreservesColimit F (CategoryTheory.Sheaf.functorH
      (Opens.grothendieckTopology X) 0) := by
  exact (preservesColimit_iff_of_natIso F
    (functorHZeroIsoSections (X := X))).mpr
      (CompactOpenSections.preservesColimit_globalSections F)

end SheafCohomology.DegreeZero
end
end
