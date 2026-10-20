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

/-- The native sheafed-space arrow over the inverse-image open of `V`.
Its defining property is the commuting square with the restriction inclusions. -/
@[expose] def restrictOnPreimage (g : X ⟶ Y) (V : Opens Y) :
    X.restrict ((Opens.map g.hom.base).obj V).isOpenEmbedding ⟶
      Y.restrict V.isOpenEmbedding := by
  let inclusion := (Y.ofRestrict V.isOpenEmbedding).hom
  let composite := (X.ofRestrict ((Opens.map g.hom.base).obj V).isOpenEmbedding ≫ g).hom
  haveI : PresheafedSpace.IsOpenImmersion inclusion := by
    dsimp [inclusion]
    infer_instance
  exact InducedCategory.homMk (PresheafedSpace.IsOpenImmersion.lift
    inclusion composite (restrictOnPreimage_range g V))

end AlgebraicGeometry.SheafedSpace
end
end
