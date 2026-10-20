public section

set_option warningAsError true

set_option linter.style.haveILetI false

set_option backward.defeqAttrib.useBackward true

set_option backward.isDefEq.respectTransparency false

open CategoryTheory TopologicalSpace Opposite

universe v

noncomputable section

namespace AlgebraicGeometry.SheafedSpace

variable {C : Type (v + 1)} [Category.{v} C]

variable {X Y Z : SheafedSpace.{v + 1, v, v} C}

theorem restrictOnPreimage_unique (g : X ⟶ Y) (V : Opens Y)
    (arrow : X.restrict ((Opens.map g.hom.base).obj V).isOpenEmbedding ⟶
      Y.restrict V.isOpenEmbedding)
    (comm : arrow ≫ Y.ofRestrict V.isOpenEmbedding =
      X.ofRestrict ((Opens.map g.hom.base).obj V).isOpenEmbedding ≫ g) :
    arrow = restrictOnPreimage g V := by
  apply InducedCategory.hom_ext
  unfold restrictOnPreimage
  dsimp
  apply PresheafedSpace.IsOpenImmersion.lift_uniq _ _ (restrictOnPreimage_range g V)
  exact congrArg (fun morphism => morphism.hom) comm

end AlgebraicGeometry.SheafedSpace
end
end
