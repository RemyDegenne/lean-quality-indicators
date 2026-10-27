@[expose] public section

noncomputable section

universe v' u' v u

open CategoryTheory Opposite CategoryTheory.Category CategoryTheory.Functor CategoryTheory.Limits
  TopCat TopCat.Presheaf TopologicalSpace

variable {J : Type u'} [Category.{v'} J] {C : Type u} [Category.{v} C]

namespace AlgebraicGeometry

namespace PresheafedSpace

attribute [local simp] eqToHom_map

variable [HasColimitsOfShape J TopCat.{v}]

variable [∀ X : TopCat.{v}, HasLimitsOfShape Jᵒᵖ (X.Presheaf C)]

variable [HasLimitsOfShape Jᵒᵖ C]

namespace ColimitCoconeIsColimit

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Auxiliary definition for `AlgebraicGeometry.PresheafedSpace.colimitCoconeIsColimit`.
-/
def descCApp (F : J ⥤ PresheafedSpace.{_, _, v} C) (s : Cocone F) (U : (Opens s.pt.carrier)ᵒᵖ) :
    s.pt.presheaf.obj U ⟶
      (colimit.desc (F ⋙ PresheafedSpace.forget C) ((PresheafedSpace.forget C).mapCocone s) _*
            limit (pushforwardDiagramToColimit F).leftOp).obj
        U := by
  refine
    limit.lift _
        { pt := s.pt.presheaf.obj U
          π :=
            { app := fun j => ?_
              naturality := fun j j' f => ?_ } } ≫
      (limitObjIsoLimitCompEvaluation _ _).inv
  -- We still need to construct the `app` and `naturality'` fields omitted above.
  · refine (s.ι.app (unop j)).c.app U ≫ (F.obj (unop j)).presheaf.map (eqToHom ?_)
    dsimp
    rw [← Opens.map_comp_obj]
    simp
  · dsimp
    rw [PresheafedSpace.congr_app (s.w f.unop).symm U]
    have w :=
      Functor.congr_obj
        congr(Opens.map $(colimit.ι_desc ((PresheafedSpace.forget C).mapCocone s) (unop j)))
        (unop U)
    simp only [Opens.map_comp_obj_unop] at w
    replace w := congr(op $w)
    have w' := NatTrans.congr (F.map f.unop).c w
    rw [w']
    simp

end ColimitCoconeIsColimit
end PresheafedSpace
end AlgebraicGeometry
end
end
