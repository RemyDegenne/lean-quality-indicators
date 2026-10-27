@[expose] public section

namespace Lean4GlCoalgebras

open Split

/-- Carrier coalgebra of the cut-based left interpolation proof, abstracted over the right
interpolant proof `𝕐₂` and its root `y₂`. -/
noncomputable def partialInterpolationLeftAlpha {𝕏 : Proof} [fin_X : Fintype 𝕏.X]
    (x : 𝕏.X) (𝕐₂ : Split.Proof) (y₂ : 𝕐₂.X) :
    (Unit ⊕ (partialEquationLeft x).X ⊕ 𝕐₂.X) →
      (Ext.T x (@leftInterpolantSequent 𝕏 _)).obj (Unit ⊕ (partialEquationLeft x).X ⊕ 𝕐₂.X)
  | Sum.inl _ =>
      ⟨Ext.RuleApp.cutᵣ (leftInterpolantSequent x) (interpolant 𝕏 (equation x)),
        [Sum.inr (Sum.inl (partialEquationLeft x).root), Sum.inr (Sum.inr y₂)]⟩
  | Sum.inr (Sum.inl z₁) =>
      ⟨Ext.r (partialEquationLeft x).α z₁,
        List.map (Sum.inr ∘ Sum.inl) (Ext.p (partialEquationLeft x).α z₁)⟩
  | Sum.inr (Sum.inr z₂) =>
      ⟨splitToExt (r 𝕐₂.α z₂), List.map (Sum.inr ∘ Sum.inr) (p 𝕐₂.α z₂)⟩

end Lean4GlCoalgebras
end
