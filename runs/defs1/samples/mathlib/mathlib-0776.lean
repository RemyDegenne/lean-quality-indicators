@[expose] public section

noncomputable section

universe v₁ v₂ u₁ u₂

open CategoryTheory CategoryTheory.Category CategoryTheory.Limits CategoryTheory.Functor

namespace CategoryTheory.Limits

section

variable {C : Type u₁} [Category.{v₁} C]

variable {D : Type u₂} [Category.{v₂} D]

variable (G : C ⥤ D)

section Pushout

variable {X Y Z : C} {f : X ⟶ Y} {g : X ⟶ Z}

variable [HasPushout f g] [HasPushout (G.map f) (G.map g)]

variable [PreservesColimit (span f g) G]

set_option backward.defeqAttrib.useBackward true in
/-- A pushout cocone in `C` is colimit iff it becomes limit
after the application of `yoneda.obj X` for all `X : C`. -/
def PushoutCocone.isColimitYonedaEquiv (c : PushoutCocone f g) :
    IsColimit c ≃ ∀ (X : C), IsLimit (c.op.map (yoneda.obj X)) :=
  (Limits.Cocone.isColimitYonedaEquiv c).trans
    (Equiv.piCongrRight (fun X ↦
      (IsLimit.whiskerEquivalenceEquiv walkingSpanOpEquiv.symm).trans
        ((IsLimit.postcomposeHomEquiv
          (isoWhiskerRight (cospanOp f g).symm (yoneda.obj X)) _).symm.trans
            (Equiv.trans (IsLimit.equivIsoLimit
              (by exact Cone.ext (Iso.refl _) (by rintro (_ | _ | _) <;> cat_disch)))
                (c.op.isLimitMapConeEquiv (yoneda.obj X))))))

end Pushout
end
end CategoryTheory.Limits
end
end
