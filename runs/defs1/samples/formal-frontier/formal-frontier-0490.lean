public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

noncomputable section

universe u

namespace CategoryTheory.Sheaf.OpenCohomology

variable {X : TopCat.{u}} (U : Opens X)

variable [HasSheafify
  (Opens.grothendieckTopology X) AddCommGrpCat.{u}]

variable [HasSheafify
  ((Opens.grothendieckTopology X).over U) AddCommGrpCat.{u}]

variable [(Opens.grothendieckTopology X).WEqualsLocallyBijective
  AddCommGrpCat.{u}]

variable [(Opens.grothendieckTopology X).HasSheafCompose
  (CategoryTheory.forget AddCommGrpCat.{u})]

variable [((Opens.grothendieckTopology X).over U).HasSheafCompose
  (CategoryTheory.forget AddCommGrpCat.{u})]

/-- The canonical terminal object in the pointwise left-Kan-extension index
when the evaluated open lies below `U`. -/
@[expose] noncomputable def overLanIndexTerminalObj (V : (Opens X)ᵒᵖ)
    (hVU : V.unop ≤ U) :
    CostructuredArrow (Over.forget U).op V := by
  let o : Over U := Over.mk (Y := V.unop) (homOfLE hVU)
  exact CostructuredArrow.mk (Y := .op o) (eqToHom (by rfl))

end CategoryTheory.Sheaf.OpenCohomology
end
end
