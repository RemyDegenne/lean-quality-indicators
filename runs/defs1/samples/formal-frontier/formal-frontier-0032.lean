public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

noncomputable section

universe u

namespace CategoryTheory.Sheaf.OpenCohomology

variable {X : TopCat.{u}} {U V : Opens X} (i : V ⟶ U)

variable [globalSheafify : HasSheafify
  (Opens.grothendieckTopology X) AddCommGrpCat.{u}]

variable [overUSheafify : HasSheafify
  ((Opens.grothendieckTopology X).over U) AddCommGrpCat.{u}]

variable [overVSheafify : HasSheafify
  ((Opens.grothendieckTopology X).over V) AddCommGrpCat.{u}]

variable [overULocallyBijective :
  ((Opens.grothendieckTopology X).over U).WEqualsLocallyBijective
  AddCommGrpCat.{u}]

variable [overUSheafCompose :
  ((Opens.grothendieckTopology X).over U).HasSheafCompose
  (CategoryTheory.forget AddCommGrpCat.{u})]

variable [overVLocallyBijective :
  ((Opens.grothendieckTopology X).over V).WEqualsLocallyBijective
  AddCommGrpCat.{u}]

variable [overVSheafCompose :
  ((Opens.grothendieckTopology X).over V).HasSheafCompose
  (CategoryTheory.forget AddCommGrpCat.{u})]

/-- Restricting first to `U` and then along `V ⟶ U` agrees naturally with
restricting directly to `V`. -/
@[expose] noncomputable def restrictToOverCompIso :
    restrictToOver U ⋙ inclusionRestrict i ≅ restrictToOver V :=
  NatIso.ofComponents
    (fun F => CategoryTheory.Sheaf.pushforwardOverMapIso F i)
    (fun f => by
      ext W x
      rfl)

end CategoryTheory.Sheaf.OpenCohomology
end
end
