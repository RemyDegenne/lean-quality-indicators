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

theorem restrictOnNamedPreimage_fac (g : X ⟶ Y) (V : Opens Y)
    (U : Opens X) (h : U = (Opens.map g.hom.base).obj V) :
    restrictOnNamedPreimage g V U h ≫ Y.ofRestrict V.isOpenEmbedding =
      X.ofRestrict U.isOpenEmbedding ≫ g := by
  subst U
  simpa [restrictOnNamedPreimage] using restrictOnPreimage_fac g V

end AlgebraicGeometry.SheafedSpace
end
end
