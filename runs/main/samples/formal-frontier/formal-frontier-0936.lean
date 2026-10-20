public section

set_option warningAsError true

set_option backward.isDefEq.respectTransparency.types false

set_option backward.defeqAttrib.useBackward true

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopCat.Sheaf.CommRingForget

universe v vj wj

namespace AlgebraicGeometry.SheafedSpace.CommRingForget

variable {J : Type wj} [Category.{vj} J]

theorem conePullbackCocone_forget_ι (S : Jᵒᵖ ⥤ SheafedSpace CommRingCat.{v})
    (c : Cone S) (i : J) :
    (SheafedSpace.conePullbackCocone (Type v) (S ⋙ underlying) (underlying.mapCone c)).ι.app i =
      (conePullbackIso S ((SheafedSpace.forget CommRingCat.{v}).mapCone c)).hom.app i ≫
        (underlyingSheaf (c.pt : TopCat)).map
          ((SheafedSpace.conePullbackCocone CommRingCat.{v} S c).ι.app i) := by
  rw [SheafedSpace.conePullbackCocone_ι_app,
    SheafedSpace.conePullbackCocone_ι_app, conePullbackIso_hom_app]
  exact underlying_sheafMate (c.π.app (op i))

end AlgebraicGeometry.SheafedSpace.CommRingForget
end
end
