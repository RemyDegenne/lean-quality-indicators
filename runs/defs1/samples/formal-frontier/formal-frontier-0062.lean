@[expose] public section

open CategoryTheory CategoryTheory.Limits FintypeCat Opposite

universe u

namespace Profinite

/-- Realize every dual ind-object of the finite-set skeleton as a profinite
space. -/
noncomputable def indDualRealization :
    (Ind FintypeCat.Skeleton.{u}ᵒᵖ)ᵒᵖ ⥤ Profinite.{u} where
  obj Q := (indDualPresentationCone Q).pt
  map f := indDualRealizationMap f
  map_id Q := by
    change indDualRealizationMap (𝟙 Q) = 𝟙 _
    simpa only [indDualRealizationMap, Category.id_comp, Iso.hom_inv_id] using
      finiteDiagramIndDualContinuousEquiv_id
        (indDualPresentationDiagram Q)
        (indDualPresentationCone Q) (Profinite.limitConeIsLimit _)
  map_comp := by
    intro Q R S f g
    change indDualRealizationMap (f ≫ g) =
      indDualRealizationMap f ≫ indDualRealizationMap g
    simp only [indDualRealizationMap]
    calc
      _ = finiteDiagramIndDualContinuousEquiv
          (indDualPresentationDiagram Q) (indDualPresentationDiagram S)
          (indDualPresentationCone Q) (Profinite.limitConeIsLimit _)
          (indDualPresentationCone S) (Profinite.limitConeIsLimit _)
          (((indDualPresentationIso Q).hom ≫ f ≫ (indDualPresentationIso R).inv) ≫
            ((indDualPresentationIso R).hom ≫ g ≫ (indDualPresentationIso S).inv)) := by
            congr 1
            simp only [Category.assoc, Iso.inv_hom_id_assoc]
      _ = _ := finiteDiagramIndDualContinuousEquiv_comp
        (indDualPresentationDiagram Q) (indDualPresentationDiagram R)
        (indDualPresentationDiagram S)
        (indDualPresentationCone Q) (Profinite.limitConeIsLimit _)
        (indDualPresentationCone R) (Profinite.limitConeIsLimit _)
        (indDualPresentationCone S) (Profinite.limitConeIsLimit _)
        ((indDualPresentationIso Q).hom ≫ f ≫ (indDualPresentationIso R).inv)
        ((indDualPresentationIso R).hom ≫ g ≫ (indDualPresentationIso S).inv)

end Profinite
end
