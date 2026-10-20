public section

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

open TopologicalSpace TopCat

namespace TopCat.Sheaf

variable {X : TopCat.{0}}

/-- The functorial flasque resolution after evaluation on the terminal open. -/
noncomputable abbrev flasqueResolutionSections
    (F : Sheaf AddCommGrpCat X) : CochainComplex AddCommGrpCat ℕ :=
  ((terminalSectionsFunctor (X := X)).mapHomologicalComplex (ComplexShape.up ℕ)).obj
    (flasqueResolution F)

end TopCat.Sheaf
end
end
