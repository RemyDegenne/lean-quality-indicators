namespace P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_isFrameOn_topDifferentials_forall_topFormMap_appLE_mul_eq

attribute [-instance] PresheafOfModules.PullbackMonoidal.pullback_monoidal PresheafOfModules.PullbackMonoidal.isIso_δ PresheafOfModules.pushforward_laxMonoidal PresheafOfModules.PullbackMonoidal.isIso_η PresheafOfModules.free_monoidal PresheafOfModules.restrictScalars_laxMonoidal PresheafOfModules.PullbackMonoidal.isIso_δ_gS PresheafOfModules.pullback_oplaxMonoidal PresheafOfModules.PullbackMonoidal.instPreservesColimitsOfSizeCompOppositeCommRingCatRingCatForget₂RingHomCarrierCarrierPb PresheafOfModules.pullback_monoidal' AlgebraicGeometry.Scheme.Modules.preservesBinaryProducts_opensMap AlgebraicGeometry.Scheme.Modules.pullback_monoidal AlgebraicGeometry.Scheme.Modules.sheafify_isLocalization' AlgebraicGeometry.Scheme.Modules.preservesTerminal_opensMap AlgebraicGeometry.Scheme.Modules.pullback₀_monoidal AlgebraicGeometry.Scheme.Modules.preservesFiniteProducts_opensMap AlgebraicGeometry.Scheme.Modules.instLiftingPresheafOfModulesSheafifyPresheafWOpensCarrierCarrierCommRingCatGrothendieckTopologyObjFunctorOppositeIsSheafSheafCompPullback₀Pullback

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry NeronModelInfra GoodReductionJacobian

universe u

noncomputable section

namespace KeyLeftSkel

variable {K : Type u} [Field K] {G : Scheme.{u}} (g : G ⟶ Spec (CommRingCat.of K)) (LG : RelativeGroupLaw K g) (d : ℕ)

variable (V : G.Opens) (hV : IsAffineOpen V)

abbrev baseV : Spec (CommRingCat.of Γ(G, V)) ⟶ Spec (CommRingCat.of K) :=
  letI := g.sectionsAlgebra V
  Spec.map (CommRingCat.ofHom (algebraMap K Γ(G, V)))

end KeyLeftSkel
end
end P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_isFrameOn_topDifferentials_forall_topFormMap_appLE_mul_eq
