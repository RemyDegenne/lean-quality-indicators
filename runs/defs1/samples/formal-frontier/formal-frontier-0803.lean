@[expose] public section

open CategoryTheory CategoryTheory.Limits FintypeCat Opposite

universe u

namespace Profinite

/-- Morphisms between arbitrary dual ind-objects correspond to the continuous
maps between their realized profinite spaces.

Uses Mathlib’s `Ind` presentations and `FiniteDiagramIndDual` in one universe; the
pro-category paragraph in Neukirch–Schmidt–Wingberg, *Cohomology of Number Fields*, Ch. I
§1 is motivation, not this profinite-space Hom equivalence. -/
noncomputable def indDualRealizationHomEquiv
    (Q R : (Ind FintypeCat.Skeleton.{u}ᵒᵖ)ᵒᵖ) :
    (Q ⟶ R) ≃ (indDualRealization.obj Q ⟶ indDualRealization.obj R) :=
  (indDualPresentationHomEquiv Q R).trans
    (finiteDiagramIndDualContinuousEquiv
      (indDualPresentationDiagram Q) (indDualPresentationDiagram R)
      (indDualPresentationCone Q) (Profinite.limitConeIsLimit _)
      (indDualPresentationCone R) (Profinite.limitConeIsLimit _))

end Profinite
end
