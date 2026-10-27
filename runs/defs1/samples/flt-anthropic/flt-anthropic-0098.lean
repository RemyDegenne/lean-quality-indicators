namespace P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_normModule_frameKit_of_isClosedImmersion

attribute [-instance] TwoChartCech.Sections.M0_moduleA TwoChartCech.Sections.M1_module TwoChartCech.Cover.A01_algebra TwoChartCech.Cover.A0_algebra TwoChartCech.Cover.A1_commRing TwoChartCech.Cover.A1_algebra TwoChartCech.Sections.M01_module TwoChartCech.Sections.M0_addCommGroup TwoChartCech.Sections.M0_tower TwoChartCech.Sections.M01_addCommGroup TwoChartCech.Cover.A0_commRing TwoChartCech.Sections.M1_tower TwoChartCech.Sections.M01_moduleA TwoChartCech.Sections.M0_module TwoChartCech.Sections.M1_moduleA TwoChartCech.Sections.M1_addCommGroup TwoChartCech.Cover.A01_commRing TwoChartCech.Sections.M01_tower CoherentBaseChange.TwoTermComplex.C0_module CoherentBaseChange.TwoTermComplex.C0_addCommGroup CoherentBaseChange.TwoTermComplex.C1_module CoherentBaseChange.TwoTermComplex.C1_addCommGroup CoherentBaseChange.TwoTermComplex.C0_free CoherentBaseChange.TwoTermComplex.C1_finite CoherentBaseChange.TwoTermComplex.C0_finite CoherentBaseChange.TwoTermComplex.C1_free AlgebraicGeometry.Scheme.Modules.preservesBinaryProducts_opensMap AlgebraicGeometry.Scheme.Modules.pullback_monoidal AlgebraicGeometry.Scheme.Modules.sheafify_isLocalization' AlgebraicGeometry.Scheme.Modules.preservesTerminal_opensMap AlgebraicGeometry.Scheme.Modules.pullback₀_monoidal AlgebraicGeometry.Scheme.Modules.preservesFiniteProducts_opensMap AlgebraicGeometry.Scheme.Modules.instLiftingPresheafOfModulesSheafifyPresheafWOpensCarrierCarrierCommRingCatGrothendieckTopologyObjFunctorOppositeIsSheafSheafCompPullback₀Pullback PresheafOfModules.PullbackMonoidal.pullback_monoidal PresheafOfModules.PullbackMonoidal.isIso_δ PresheafOfModules.pushforward_laxMonoidal PresheafOfModules.PullbackMonoidal.isIso_η PresheafOfModules.free_monoidal PresheafOfModules.restrictScalars_laxMonoidal PresheafOfModules.PullbackMonoidal.isIso_δ_gS

attribute [-instance] PresheafOfModules.pullback_oplaxMonoidal PresheafOfModules.PullbackMonoidal.instPreservesColimitsOfSizeCompOppositeCommRingCatRingCatForget₂RingHomCarrierCarrierPb PresheafOfModules.pullback_monoidal'

set_option autoImplicit false

universe u v

p2m_open

p2m_open

set_option backward.isDefEq.respectTransparency false

namespace NormKit

p2m_open

variable {X Z Z₀ Z₁ : Scheme.{u}} (π : Z ⟶ X) (ι₀ : Z₀ ⟶ Z) (ι₁ : Z₁ ⟶ Z) (d d₀ d₁ : ℕ) (L : Z.Modules)

def S (W : X.Opens) : Set (Γ(normModule π d L, W) ×
    Γ(normModule (ι₀ ≫ π) d₀ ((Scheme.Modules.pullback ι₀).obj L) ⊗
      normModule (ι₁ ≫ π) d₁ ((Scheme.Modules.pullback ι₁).obj L), W)) :=
  {pq | ∃ (hW : good π d W) (hW₀ : good (ι₀ ≫ π) d₀ W) (hW₁ : good (ι₁ ≫ π) d₁ W) (s : Γ(L, π ⁻¹ᵁ W)),
    IsFrameOn s (π ⁻¹ᵁ W) ∧ pq = (δ L hW s, qSec π ι₀ ι₁ d₀ d₁ L hW₀ hW₁ s)}

end NormKit
end P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_normModule_frameKit_of_isClosedImmersion
