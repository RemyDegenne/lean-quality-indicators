@[expose] public section

open CategoryTheory CategoryTheory.Limits FintypeCat Opposite

universe u

namespace Profinite

variable {I J : Type u} [SmallCategory I] [IsCofiltered I]
    [SmallCategory J] [IsCofiltered J]

@[simp] theorem indDualRealizationPresentationIso_refl
    {Q : (Ind FintypeCat.Skeleton.{u}ᵒᵖ)ᵒᵖ}
    (X : I ⥤ FintypeCat.Skeleton.{u}) (e : Q ≅ finiteDiagramIndDual X)
    (c : Cone ((X ⋙ FintypeCat.Skeleton.incl) ⋙ FintypeCat.toProfinite))
    (hc : IsLimit c) :
    indDualRealizationPresentationIso X e c hc X e c hc = Iso.refl c.pt := by
  exact (indDualRealizationComparisonOfIso X e c hc).symm_self_id

end Profinite
end
