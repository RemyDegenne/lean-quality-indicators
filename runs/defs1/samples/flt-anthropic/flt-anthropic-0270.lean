namespace P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_isFrameOn_tensorPow_three_of_forall_nonempty_pullback_tensor_iso

attribute [-instance] PresheafOfModules.PullbackMonoidal.pullback_monoidal PresheafOfModules.PullbackMonoidal.isIso_δ PresheafOfModules.pushforward_laxMonoidal PresheafOfModules.PullbackMonoidal.isIso_η PresheafOfModules.free_monoidal PresheafOfModules.restrictScalars_laxMonoidal PresheafOfModules.PullbackMonoidal.isIso_δ_gS PresheafOfModules.pullback_oplaxMonoidal PresheafOfModules.PullbackMonoidal.instPreservesColimitsOfSizeCompOppositeCommRingCatRingCatForget₂RingHomCarrierCarrierPb PresheafOfModules.pullback_monoidal' AlgebraicGeometry.Scheme.Modules.preservesBinaryProducts_opensMap AlgebraicGeometry.Scheme.Modules.pullback_monoidal AlgebraicGeometry.Scheme.Modules.sheafify_isLocalization' AlgebraicGeometry.Scheme.Modules.preservesTerminal_opensMap AlgebraicGeometry.Scheme.Modules.pullback₀_monoidal AlgebraicGeometry.Scheme.Modules.preservesFiniteProducts_opensMap AlgebraicGeometry.Scheme.Modules.instLiftingPresheafOfModulesSheafifyPresheafWOpensCarrierCarrierCommRingCatGrothendieckTopologyObjFunctorOppositeIsSheafSheafCompPullback₀Pullback

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

set_option autoImplicit false

section l3_solution

p2m_open

open scoped CategoryTheory.MonObj

namespace L3Sol

variable {k : Type u} [Field k] {X : Scheme.{u}} (t : X ⟶ Spec (CommRingCat.of k)) [GrpObj (Over.mk t)]

noncomputable abbrev invT : X ⟶ X := ((𝟙 (Over.mk t))⁻¹ : Over.mk t ⟶ Over.mk t).left

end L3Sol
end l3_solution
end P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_isFrameOn_tensorPow_three_of_forall_nonempty_pullback_tensor_iso
