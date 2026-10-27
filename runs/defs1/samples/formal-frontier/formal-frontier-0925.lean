@[expose] public section

open CategoryTheory CategoryTheory.Limits FintypeCat Opposite

universe u

namespace Profinite

variable {I J : Type u} [SmallCategory I] [IsCofiltered I]
    [SmallCategory J] [IsCofiltered J]

/-- Two supplied presentations of the same object give canonically
isomorphic specified limits through its realization. -/
noncomputable def indDualRealizationPresentationIso
    {Q : (Ind FintypeCat.Skeleton.{u}ᵒᵖ)ᵒᵖ}
    (X : I ⥤ FintypeCat.Skeleton.{u}) (e : Q ≅ finiteDiagramIndDual X)
    (c : Cone ((X ⋙ FintypeCat.Skeleton.incl) ⋙ FintypeCat.toProfinite))
    (hc : IsLimit c)
    (Y : J ⥤ FintypeCat.Skeleton.{u}) (e' : Q ≅ finiteDiagramIndDual Y)
    (d : Cone ((Y ⋙ FintypeCat.Skeleton.incl) ⋙ FintypeCat.toProfinite))
    (hd : IsLimit d) : c.pt ≅ d.pt :=
  (indDualRealizationComparisonOfIso X e c hc).symm ≪≫
    indDualRealizationComparisonOfIso Y e' d hd

end Profinite
end
