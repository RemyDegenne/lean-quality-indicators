public section

set_option warningAsError true

set_option backward.isDefEq.respectTransparency.types false

set_option backward.defeqAttrib.useBackward true

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopCat.Sheaf.AbelianForget

universe v

namespace AlgebraicGeometry.SheafedSpace.AbelianForget

variable {J : Type v} [SmallCategory J] [IsFiltered J]

/-- Forgetting coefficients and transporting the inverse-image diagram preserves
the colimit of the actual projection-mate cocone of an additive native cone. -/
noncomputable def isColimit_conePullbackCocone_underlying
    (S : Jᵒᵖ ⥤ SheafedSpace AddCommGrpCat.{v}) (C : Cone S)
    (hK : IsColimit (SheafedSpace.conePullbackCocone AddCommGrpCat.{v} S C)) :
    IsColimit (SheafedSpace.conePullbackCocone (Type v) (S ⋙ underlying)
      (underlying.mapCone C)) := by
  let D := SheafedSpace.conePullback AddCommGrpCat.{v} S
    ((SheafedSpace.forget AddCommGrpCat.{v}).mapCone C)
  let F := underlyingSheaf (C.pt : TopCat)
  have hMapped : IsColimit
      (F.mapCocone (SheafedSpace.conePullbackCocone AddCommGrpCat.{v} S C)) :=
    Classical.choice ((preservesFilteredSheafColimit (C.pt : TopCat) D).preserves hK)
  have hPre := (IsColimit.precomposeHomEquiv
    (conePullbackIso S ((SheafedSpace.forget AddCommGrpCat.{v}).mapCone C)) _).symm hMapped
  refine hPre.ofIsoColimit (Cocone.ext (Iso.refl _) (fun i ↦ ?_))
  change (conePullbackIso S ((SheafedSpace.forget AddCommGrpCat.{v}).mapCone C)).hom.app i ≫
      (underlyingSheaf (C.pt : TopCat)).map
        ((SheafedSpace.conePullbackCocone AddCommGrpCat.{v} S C).ι.app i) =
      (SheafedSpace.conePullbackCocone (Type v) (S ⋙ underlying)
        (underlying.mapCone C)).ι.app i
  exact (conePullbackCocone_forget_ι S C i).symm

end AlgebraicGeometry.SheafedSpace.AbelianForget
end
end
