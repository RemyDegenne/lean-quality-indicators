public section

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

open TopologicalSpace TopCat

namespace TopCat.Sheaf

variable {X : TopCat.{0}}

variable [CompactSpace X] [PrespectralSpace X] [QuasiSeparatedSpace X]

variable [HasSheafify
  (Opens.grothendieckTopology X) AddCommGrpCat.{0}]

variable [hExt : HasExt.{0} (CategoryTheory.Sheaf
  (Opens.grothendieckTopology X) AddCommGrpCat.{0})]

/-- In degree one, derived sheaf cohomology agrees with the homology of
terminal-open sections of the functorial flasque resolution. -/
@[expose] noncomputable def derivedOneIsoFlasqueResolutionSectionsHomology
    (A : Sheaf AddCommGrpCat X) :
    (CategoryTheory.Sheaf.functorH
      (Opens.grothendieckTopology X) 1).obj
        (flasqueEnvelopeShortComplex A).X₁ ≅
      (flasqueResolutionSections A).homology 1 :=
  flasqueEnvelopeDerivedOneIsoCokernelSections A ≪≫
    (flasqueResolutionSectionsHomologyIsoCokernel' A 0).symm

end TopCat.Sheaf
end
end
