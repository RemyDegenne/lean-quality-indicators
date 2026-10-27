@[expose] public section

universe v₁ v₂ v u₁ u₂ u

open CategoryTheory Functor

namespace CategoryTheory.Limits

variable {J : Type u₁} {K : Type u₂} [Category.{v₁} J] [Category.{v₂} K]

variable {C : Type u} [Category.{v} C]

section

variable [HasColimitsOfShape K C] [HasLimitsOfShape J C] (F : J ⥤ K ⥤ C)

/-- Given a bifunctor `F : J ⥤ K ⥤ C`, and assuming that `C` has colimits of shape `K`,
the colimit of `F.flip` is `F ⋙ colim`. -/
@[no_expose]
noncomputable def colim.isColimitCoconeFlip : IsColimit (colim.coconeFlip F) :=
  evaluationJointlyReflectsColimits _ (fun _ ↦ colimit.isColimit _)

end
end CategoryTheory.Limits
end
