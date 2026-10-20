namespace P2MW.S_AlgebraicGeometry_TwoGluedCurves_exists_isInvertible_isNodeUnitModule

set_option autoImplicit false

universe u v

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.RelPicard NeronModelInfra AlgebraicGeometry.TwoGluedCurves Opposite TopologicalSpace

noncomputable section

p2m_reactivate

p2m_reactivate

namespace TwoGluedCurvesNodeUnitAux

open TwoGluedCurvesSubsheafAux TwoGluedCurvesFrameAux

variable {κ : Type u} [Field κ]
  {X C₁ C₂ : Scheme.{u}} {x : X ⟶ Spec (.of κ)}
  {c₁ : C₁ ⟶ Spec (.of κ)} {c₂ : C₂ ⟶ Spec (.of κ)}
  {i₁ : SchemeHomOver c₁ x} {i₂ : SchemeHomOver c₂ x}
  {ι : Type v} {p₁ : ι → SchemeHomOver (𝟙 (Spec (.of κ))) c₁} {p₂ : ι → SchemeHomOver (𝟙 (Spec (.of κ))) c₂}
  {T : Scheme.{u}} {h : T ⟶ Spec (.of κ)} (u : ι → Γ(T, ⊤)ˣ)

local notation "XT" => pullback x h

local notation "C₁T" => pullback c₁ h

local notation "C₂T" => pullback c₂ h

set_option quotPrecheck false in
local notation "i₁T" => curveChange i₁.1 i₁.2 h

set_option quotPrecheck false in
local notation "i₂T" => curveChange i₂.1 i₂.2 h

local notation "σ¹" => nodeSectionFst p₁ h

local notation "σ²" => nodeSectionSnd p₂ h

local notation "nl" => nodeLocus x i₁ i₂ p₁ p₂ h

set_option quotPrecheck false in

local notation "P¹" => (Scheme.Modules.pushforward (curveChange i₁.1 i₁.2 h)).obj
  (SheafOfModules.unit (pullback c₁ h).ringCatSheaf)

set_option quotPrecheck false in

local notation "P²" => (Scheme.Modules.pushforward (curveChange i₂.1 i₂.2 h)).obj
  (SheafOfModules.unit (pullback c₂ h).ringCatSheaf)

lemma fn₁_injective (W : (XT).Opens) : Function.Injective (fn₁ (i₁ := i₁) W) := fun _ _ e => e

end TwoGluedCurvesNodeUnitAux
end
end P2MW.S_AlgebraicGeometry_TwoGluedCurves_exists_isInvertible_isNodeUnitModule
