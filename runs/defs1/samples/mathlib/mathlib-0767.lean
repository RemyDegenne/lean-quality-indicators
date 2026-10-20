@[expose] public section

open TopologicalSpace CategoryTheory Opposite Topology

open CategoryTheory.Limits

namespace AlgebraicGeometry

universe w v v₁ v₂ u

variable {C : Type u} [Category.{v} C]

namespace PresheafedSpace.IsOpenImmersion

local notation "IsOpenImmersion" => PresheafedSpace.IsOpenImmersion

attribute [instance] IsOpenImmersion.c_iso

open CategoryTheory.Limits.WalkingCospan

section ToSheafedSpace

variable {X : PresheafedSpace C} (Y : SheafedSpace C)

/-- If `X ⟶ Y` is an open immersion, and `Y` is a SheafedSpace, then so is `X`. -/
def toSheafedSpace (f : X ⟶ Y.toPresheafedSpace) [H : IsOpenImmersion f] : SheafedSpace C where
  IsSheaf := by
    apply TopCat.Presheaf.isSheaf_of_iso (sheafIsoOfIso (isoRestrict f).symm).symm
    apply TopCat.Sheaf.pushforward_sheaf_of_sheaf
    exact (Y.restrict H.base_open).IsSheaf
  toPresheafedSpace := X

end ToSheafedSpace
end PresheafedSpace.IsOpenImmersion
end AlgebraicGeometry
end
