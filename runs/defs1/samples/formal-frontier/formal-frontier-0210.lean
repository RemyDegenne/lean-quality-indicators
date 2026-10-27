public section

set_option warningAsError true

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

open TopologicalSpace

namespace SheafCohomology.HigherDirectImageFilteredColimit

variable {X Y : TopCat.{0}} (f : X ⟶ Y)

variable [PrespectralSpace X] [QuasiSeparatedSpace X]

variable [PrespectralSpace Y]

variable [HasSheafify
  (Opens.grothendieckTopology X) AddCommGrpCat.{0}]

variable [HasSheafify
  (Opens.grothendieckTopology Y) AddCommGrpCat.{0}]

variable {I : Type} [Preorder I] [IsDirectedOrder I] [Nonempty I]

variable (F : I ⥤ CategoryTheory.Sheaf
  (Opens.grothendieckTopology X) AddCommGrpCat.{0})

/-- The pointwise presheaf colimit underlying the explicit colimit of the
pushforward diagram. -/
abbrev underlyingPushforwardPresheafColimit : Y.Presheaf AddCommGrpCat.{0} :=
  colimit (F ⋙ pushforward f ⋙ forgetY (Y := Y))

end SheafCohomology.HigherDirectImageFilteredColimit
end
end
