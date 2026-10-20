@[expose] public section

open CategoryTheory Limits Opposite MonoidalCategory

universe v u w

namespace CategoryTheory.Subfunctor

variable {C : Type u} [Category.{v} C] {F G H : Cᵒᵖ ⥤ Type w}

variable {W : MorphismProperty C} [W.HasPullbacks] [W.IsStableUnderBaseChange]
  [W.IsStableUnderComposition] {D : Subfunctor F} [GrpObj D.toFunctor]

omit [W.IsStableUnderComposition] [GrpObj D.toFunctor] in
theorem leftTensorRestriction_injective
    (hD : D.IsOneCoverDense W)
    (hF : ∀ {X U : C} (f : U ⟶ X), W f →
      Presieve.IsSheafFor F (Presieve.singleton f)) :
    Function.Injective (fun φ : (𝟙_ (Cᵒᵖ ⥤ Type w)) ⊗ F ⟶ F =>
      (𝟙 (𝟙_ (Cᵒᵖ ⥤ Type w)) ⊗ₘ D.ι) ≫ φ) := by
  intro φ ψ hφψ
  change (𝟙 (𝟙_ (Cᵒᵖ ⥤ Type w)) ⊗ₘ D.ι) ≫ φ =
    (𝟙 (𝟙_ (Cᵒᵖ ⥤ Type w)) ⊗ₘ D.ι) ≫ ψ at hφψ
  apply (cancel_epi (λ_ F).inv).1
  apply (oneCoverExtensionEquiv hD hF).injective
  simp only [oneCoverExtensionEquiv_apply]
  simpa only [← Category.assoc, id_tensorHom,
    ← leftUnitor_inv_naturality D.ι] using
      congrArg (fun θ : (𝟙_ (Cᵒᵖ ⥤ Type w)) ⊗ D.toFunctor ⟶ F =>
        (λ_ D.toFunctor).inv ≫ θ) hφψ

end CategoryTheory.Subfunctor
end
