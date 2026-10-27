namespace P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_tensorProduct_sections_linearEquiv_sections_box_natural_of_isInvertible

attribute [-instance] PresheafOfModules.PullbackMonoidal.pullback_monoidal PresheafOfModules.PullbackMonoidal.isIso_δ PresheafOfModules.pushforward_laxMonoidal PresheafOfModules.PullbackMonoidal.isIso_η PresheafOfModules.free_monoidal PresheafOfModules.restrictScalars_laxMonoidal PresheafOfModules.PullbackMonoidal.isIso_δ_gS PresheafOfModules.pullback_oplaxMonoidal PresheafOfModules.PullbackMonoidal.instPreservesColimitsOfSizeCompOppositeCommRingCatRingCatForget₂RingHomCarrierCarrierPb PresheafOfModules.pullback_monoidal' AlgebraicGeometry.Scheme.Modules.preservesBinaryProducts_opensMap AlgebraicGeometry.Scheme.Modules.pullback_monoidal AlgebraicGeometry.Scheme.Modules.sheafify_isLocalization' AlgebraicGeometry.Scheme.Modules.preservesTerminal_opensMap AlgebraicGeometry.Scheme.Modules.pullback₀_monoidal AlgebraicGeometry.Scheme.Modules.preservesFiniteProducts_opensMap AlgebraicGeometry.Scheme.Modules.instLiftingPresheafOfModulesSheafifyPresheafWOpensCarrierCarrierCommRingCatGrothendieckTopologyObjFunctorOppositeIsSheafSheafCompPullback₀Pullback

set_option autoImplicit false

universe u

p2m_open

set_option maxHeartbeats 1600000

noncomputable section

namespace L4Box

p2m_open

variable {k : Type u} [Field k] {X Y : Scheme.{u}}
  (πX : X ⟶ Spec (CommRingCat.of k)) (πY : Y ⟶ Spec (CommRingCat.of k)) (F : X.Modules) (G : Y.Modules)

def fwd₀ (U : X.Opens) (V : Y.Opens) (s : Γ(F, U)) (t : Γ(G, V)) : Γ(NN πX πY F G, box πX πY U V) :=
  tensorSections (ρ₁ πX πY F U V s) (ρ₂ πX πY G U V t)

end L4Box
end
end P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_tensorProduct_sections_linearEquiv_sections_box_natural_of_isInvertible
