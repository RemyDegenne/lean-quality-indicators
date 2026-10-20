namespace P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_locIsoOnBase_of_isCanonicalPol_of_forall_isLocalRing_of_isUnit_two

attribute [-instance] PresheafOfModules.PullbackMonoidal.pullback_monoidal PresheafOfModules.PullbackMonoidal.isIso_δ PresheafOfModules.pushforward_laxMonoidal PresheafOfModules.PullbackMonoidal.isIso_η PresheafOfModules.free_monoidal PresheafOfModules.restrictScalars_laxMonoidal PresheafOfModules.PullbackMonoidal.isIso_δ_gS PresheafOfModules.pullback_oplaxMonoidal PresheafOfModules.PullbackMonoidal.instPreservesColimitsOfSizeCompOppositeCommRingCatRingCatForget₂RingHomCarrierCarrierPb PresheafOfModules.pullback_monoidal' AlgebraicGeometry.Scheme.Modules.preservesBinaryProducts_opensMap AlgebraicGeometry.Scheme.Modules.pullback_monoidal AlgebraicGeometry.Scheme.Modules.sheafify_isLocalization' AlgebraicGeometry.Scheme.Modules.preservesTerminal_opensMap AlgebraicGeometry.Scheme.Modules.pullback₀_monoidal AlgebraicGeometry.Scheme.Modules.preservesFiniteProducts_opensMap AlgebraicGeometry.Scheme.Modules.instLiftingPresheafOfModulesSheafifyPresheafWOpensCarrierCarrierCommRingCatGrothendieckTopologyObjFunctorOppositeIsSheafSheafCompPullback₀Pullback SheafOfModules.isIso_ihomModelToIhom

set_option autoImplicit false

set_option linter.unusedSectionVars false

universe u

noncomputable section

p2m_open

namespace AlgebraicGeometry

namespace Scheme

namespace Modules

namespace SpreadUniq

p2m_open

section Transfer

variable {X Y Z : Scheme.{u}} (k : X ⟶ Y) (q : Y ⟶ Z) (p : X ⟶ Z) (w : k ≫ q = p)

def unUp {M M' : Z.Modules}
    (φ : (Scheme.Modules.pullback k).obj ((Scheme.Modules.pullback q).obj M)
      ≅ (Scheme.Modules.pullback k).obj ((Scheme.Modules.pullback q).obj M')) :
    (Scheme.Modules.pullback p).obj M ≅ (Scheme.Modules.pullback p).obj M' :=
  pullbackIsoComp k q p w M ≪≫ φ ≪≫ (pullbackIsoComp k q p w M').symm

end Transfer
end SpreadUniq
end Modules
end Scheme
end AlgebraicGeometry
end
end P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_locIsoOnBase_of_isCanonicalPol_of_forall_isLocalRing_of_isUnit_two
