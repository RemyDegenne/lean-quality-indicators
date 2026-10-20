@[expose] public section

open CategoryTheory CategoryTheory.Limits FintypeCat Opposite

universe u

namespace Profinite

variable {I J K : Type u} [SmallCategory I] [IsCofiltered I]
    [SmallCategory J] [IsCofiltered J] [SmallCategory K] [IsCofiltered K]

@[simp] theorem finiteDiagramIndDualContinuousEquiv_id
    (X : I ⥤ FintypeCat.Skeleton.{u})
    (c : Cone ((X ⋙ FintypeCat.Skeleton.incl) ⋙ FintypeCat.toProfinite))
    (hc : IsLimit c) :
    finiteDiagramIndDualContinuousEquiv X X c hc c hc
      (𝟙 (finiteDiagramIndDual X)) = 𝟙 c.pt := by
  apply hc.hom_ext
  intro i
  rw [finiteDiagramIndDualContinuousEquiv_apply_class X X c hc c hc
    (𝟙 _) i i (𝟙 _) (finiteDiagramIndDualHomMap_id X i)]
  simp

end Profinite
end
