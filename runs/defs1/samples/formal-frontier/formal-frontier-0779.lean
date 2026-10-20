public section

set_option warningAsError true

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

noncomputable section

universe u

namespace TopCat.Sheaf.RightDerivedPushforward

local instance presheafToSheaf_preservesZero_sheafification
    {Y : TopCat.{u}}
    [HasSheafify (Opens.grothendieckTopology Y) AddCommGrpCat.{u}] :
    (presheafToSheaf (Opens.grothendieckTopology Y)
      AddCommGrpCat.{u}).PreservesZeroMorphisms :=
  Functor.preservesZeroMorphisms_of_additive
    (presheafToSheaf (Opens.grothendieckTopology Y) AddCommGrpCat.{u})

noncomputable local instance presheafToSheaf_preservesHomology_sheafification
    {Y : TopCat.{u}}
    [HasSheafify (Opens.grothendieckTopology Y) AddCommGrpCat.{u}] :
    (presheafToSheaf (Opens.grothendieckTopology Y)
      AddCommGrpCat.{u}).PreservesHomology := inferInstance

variable {X Y : TopCat.{u}} (f : X ⟶ Y)

variable [HasSheafify
  (Opens.grothendieckTopology X) AddCommGrpCat.{u}]

variable [HasSheafify
  (Opens.grothendieckTopology Y) AddCommGrpCat.{u}]

variable [HasExt.{u} (CategoryTheory.Sheaf
  (Opens.grothendieckTopology X) AddCommGrpCat.{u})]

variable (G : CategoryTheory.Sheaf
  (Opens.grothendieckTopology X) AddCommGrpCat.{u})

section CoefficientNaturality

variable {G₁ G₂ : CategoryTheory.Sheaf
  (Opens.grothendieckTopology X) AddCommGrpCat.{u}}

/-- Sheafification of the coefficient map on the pointwise homology
presheaf. -/
@[expose] noncomputable def sheafifiedPushforwardResolutionHomologyMap
    (a : G₁ ⟶ G₂) (q : ℕ) :
    (presheafToSheaf (Opens.grothendieckTopology Y)
      AddCommGrpCat.{u}).obj
        (pushforwardResolutionHomologyPresheaf f G₁ q) ⟶
      (presheafToSheaf (Opens.grothendieckTopology Y)
        AddCommGrpCat.{u}).obj
          (pushforwardResolutionHomologyPresheaf f G₂ q) :=
  (presheafToSheaf (Opens.grothendieckTopology Y)
    AddCommGrpCat.{u}).map
      (pushforwardResolutionHomologyPresheafMap f a q)

end CoefficientNaturality
end TopCat.Sheaf.RightDerivedPushforward
end
end
