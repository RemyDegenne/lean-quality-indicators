@[expose] public section

open CategoryTheory Limits Opposite MonoidalCategory

universe v u w

namespace CategoryTheory.Subfunctor

variable {C : Type u} [Category.{v} C] {F G H : Cᵒᵖ ⥤ Type w}

variable {W : MorphismProperty C} [W.HasPullbacks] [W.IsStableUnderBaseChange]
  [W.IsStableUnderComposition] {D : Subfunctor F} [GrpObj D.toFunctor]

theorem IsOneCoverDense.grpObj_mul_ι_app (hD : D.IsOneCoverDense W)
    (hF : ∀ {X U : C} (f : U ⟶ X), W f →
      Presieve.IsSheafFor F (Presieve.singleton f))
    (X : Cᵒᵖ) (a b : D.toFunctor.obj X) :
    ((hD.grpObj hF).toMonObj.mul).app X ((D.ι ⊗ₘ D.ι).app X (a, b)) =
      D.ι.app X ((MonObj.mul (X := D.toFunctor)).app X (a, b)) := by
  calc
    _ = (((D.ι ⊗ₘ D.ι).app X ≫ ((hD.grpObj hF).toMonObj.mul).app X)
        (a, b)) := (types_comp_apply _ _ _).symm
    _ = (((MonObj.mul (X := D.toFunctor)).app X ≫ D.ι.app X) (a, b)) := by
      simpa only [NatTrans.comp_app] using
        congrArg (fun φ => φ.app X (a, b)) (hD.grpObj_mul_ι hF).symm
    _ = _ := types_comp_apply _ _ _

end CategoryTheory.Subfunctor
end
