@[expose] public section

open CategoryTheory CategoryTheory.Limits FintypeCat Opposite

universe u

namespace Profinite

variable {I J : Type u} [SmallCategory I] [IsCofiltered I]
    [SmallCategory J] [IsCofiltered J]

theorem indDualRealizationComparisonOfIso_inv_map
    {Q : (Ind FintypeCat.Skeleton.{u}ᵒᵖ)ᵒᵖ}
    (X : I ⥤ FintypeCat.Skeleton.{u}) (e : Q ≅ finiteDiagramIndDual X)
    (c : Cone ((X ⋙ FintypeCat.Skeleton.incl) ⋙ FintypeCat.toProfinite))
    (hc : IsLimit c) :
    (indDualRealizationComparisonOfIso X e c hc).inv ≫
        indDualRealization.map e.hom =
      (indDualRealizationComparison X c hc).inv := by
  rw [indDualRealizationComparisonOfIso_inv, Category.assoc, ← Functor.map_comp]
  rw [e.inv_hom_id, indDualRealization.map_id, Category.comp_id]

end Profinite
end
