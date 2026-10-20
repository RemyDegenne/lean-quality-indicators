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

theorem ofRestrict_c_app_self
    (X : SheafedSpace.{v + 1, v, v} C) (U : Opens X) :
    (X.ofRestrict U.isOpenEmbedding).hom.c.app (op U) =
      eqToHom (restrict_Γ_obj X U).symm ≫
        (X.restrict U.isOpenEmbedding).presheaf.map
          (eqToHom (congrArg op (show
            (Opens.map (X.ofRestrict U.isOpenEmbedding).hom.base).obj U = ⊤ by
              change (Opens.map U.inclusion').obj U = ⊤
              exact Opens.inclusion'_map_eq_top U).symm)) := by
  rw [ofRestrict_hom_c_app, Opens.adjunction_counit_app_self U]
  simp only [eqToHom_op, eqToHom_map]
  exact (eqToHom_trans _ _).symm

end AlgebraicGeometry.SheafedSpace
end
end
