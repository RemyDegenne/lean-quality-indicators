namespace P2MW.S_AlgebraicGeometry_TwoGluedCurves_IsNodeUnitModule_pullback_baseChangeSnd

set_option autoImplicit false

set_option linter.unusedSectionVars false

set_option quotPrecheck false

universe u v

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.RelPicard NeronModelInfra AlgebraicGeometry.TwoGluedCurves Opposite TopologicalSpace

noncomputable section

namespace TwoGluedLinesBCAux

variable {κ : Type u} [Field κ] [IsAlgClosed κ]
  {X : Scheme.{u}} (x : X ⟶ Spec (.of κ))
  {C₁ C₂ : Scheme.{u}} {c₁ : C₁ ⟶ Spec (.of κ)} {c₂ : C₂ ⟶ Spec (.of κ)}
  (i₁ : SchemeHomOver c₁ x) (i₂ : SchemeHomOver c₂ x)
  {ι : Type v} [Finite ι] (p₁ : ι → SchemeHomOver (𝟙 (Spec (.of κ))) c₁) (p₂ : ι → SchemeHomOver (𝟙 (Spec (.of κ))) c₂)
  {T T' : Scheme.{u}} {h : T ⟶ Spec (.of κ)} {h' : T' ⟶ Spec (.of κ)} (ψ : SchemeHomOver h' h)

local notation "XT" => pullback x h

local notation "XT'" => pullback x h'

local notation "Ψ" => baseChangeSnd x ψ

local notation "ι₁" => curveChange i₁.1 i₁.2 h

local notation "ι₂" => curveChange i₂.1 i₂.2 h

local notation "ι₁'" => curveChange i₁.1 i₁.2 h'

local notation "ι₂'" => curveChange i₂.1 i₂.2 h'

local notation "φ₁" => baseChangeSnd c₁ ψ

local notation "φ₂" => baseChangeSnd c₂ ψ

local notation "σ¹" => nodeSectionFst p₁ h

local notation "σ²" => nodeSectionSnd p₂ h

local notation "σ¹'" => nodeSectionFst p₁ h'

local notation "σ²'" => nodeSectionSnd p₂ h'

local notation "nl" => nodeLocus x i₁ i₂ p₁ p₂ h

local notation "nl'" => nodeLocus x i₁ i₂ p₁ p₂ h'

open TwoGluedLinesBCGenAux

abbrev PSnd (T₀ : Scheme.{u}) (h₀ : T₀ ⟶ Spec (.of κ)) : (pullback x h₀).Modules :=
  (Scheme.Modules.pushforward (curveChange i₂.1 i₂.2 h₀)).obj
    (SheafOfModules.unit (pullback c₂ h₀).ringCatSheaf)

end TwoGluedLinesBCAux
end
end P2MW.S_AlgebraicGeometry_TwoGluedCurves_IsNodeUnitModule_pullback_baseChangeSnd
