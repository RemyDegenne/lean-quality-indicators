public section

set_option warningAsError true

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

noncomputable section

universe u

namespace TopCat.Sheaf.RightDerivedPushforward

local instance sheafForget_additive_suffix (Y : TopCat.{u}) :
    (TopCat.Sheaf.forget AddCommGrpCat.{u} Y).Additive where
  map_add := by intros; rfl

local instance evaluation_preservesZero_suffix (Y : TopCat.{u}) (V : Opens Y) :
    ((evaluation (Opens Y)ᵒᵖ AddCommGrpCat.{u}).obj
      (.op V)).PreservesZeroMorphisms where
  map_zero := by intros; rfl

variable {X Y : TopCat.{u}} (f : X ⟶ Y)

variable [HasSheafify
  (Opens.grothendieckTopology X) AddCommGrpCat.{u}]

variable [HasExt.{u} (CategoryTheory.Sheaf
  (Opens.grothendieckTopology X) AddCommGrpCat.{u})]

variable {G H : CategoryTheory.Sheaf
  (Opens.grothendieckTopology X) AddCommGrpCat.{u}}

/-- The coefficient map on pointwise homology of the pushed-forward fixed
injective resolution. -/
@[expose] noncomputable def pushforwardResolutionHomologyPresheafMap
    (a : G ⟶ H) (q : ℕ) :
    pushforwardResolutionHomologyPresheaf f G q ⟶
      pushforwardResolutionHomologyPresheaf f H q :=
  HomologicalComplex.homologyMap
    (pushforwardResolutionPresheafComplexMap f a) q

end TopCat.Sheaf.RightDerivedPushforward
end
end
