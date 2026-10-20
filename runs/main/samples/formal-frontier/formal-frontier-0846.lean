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

theorem restrictOnNamedPreimage_id
    (X : SheafedSpace.{v + 1, v, v} C) (V : Opens X) :
    restrictOnNamedPreimage (𝟙 X) V V (Opens.map_id_obj V).symm =
      𝟙 (X.restrict V.isOpenEmbedding) := by
  apply (cancel_mono (X.ofRestrict V.isOpenEmbedding)).1
  simpa only [Category.id_comp, Category.comp_id] using
    restrictOnNamedPreimage_fac (𝟙 X) V V (Opens.map_id_obj V).symm

end AlgebraicGeometry.SheafedSpace
end
end
