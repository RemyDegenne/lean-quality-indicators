@[expose] public section

open CategoryTheory Limits Opposite

universe v u w

namespace CategoryTheory.Subfunctor

variable {C : Type u} [Category.{v} C] {F : Cᵒᵖ ⥤ Type w}

/-- Extend a map from a one-cover dense subfunctor by singleton Čech descent. -/
noncomputable def extendOneCover
    {W : MorphismProperty C} [W.HasPullbacks] [W.IsStableUnderBaseChange]
    {D : Subfunctor F} (hD : D.IsOneCoverDense W) {Y : Cᵒᵖ ⥤ Type w}
    (hY : ∀ {X U : C} (f : U ⟶ X), W f →
      Presieve.IsSheafFor Y (Presieve.singleton f))
    (φ : D.toFunctor ⟶ Y) : F ⟶ Y :=
  (oneCoverExtensionEquiv hD hY).symm φ

end CategoryTheory.Subfunctor
end
