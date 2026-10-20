namespace P2MW.S_CuspForm_TWLevel_HeckeRing_finite_and_isLocalRing_and_isAdicComplete

attribute [-instance] IharaLemma.IdempotentSplitting.isScalarTower_base_cornerModule IharaLemma.IdempotentSplitting.isScalarTower_base_cornerRing IharaLemma.IdempotentSplitting.algebraBaseCornerRing IharaLemma.IdempotentSplitting.smulCornerModule IharaLemma.IdempotentSplitting.moduleCornerModule IharaLemma.IdempotentSplitting.isLocalRing_cornerRing IharaLemma.IdempotentSplitting.coeOutCornerRing IharaLemma.IdempotentSplitting.isMaximal_𝔪 IharaLemma.IdempotentSplitting.isScalarTower_cornerModule IharaLemma.IdempotentSplitting.isLocalization_cornerRing

set_option autoImplicit false

set_option synthInstance.maxHeartbeats 1600000

set_option maxHeartbeats 3200000

noncomputable section

open IsLocalRing

namespace TQStruct

theorem isNoetherianRing_of_finite {𝒪 : Type*} [CommRing 𝒪] [IsNoetherianRing 𝒪] (A : Type*)
    [CommRing A] [Algebra 𝒪 A] [Module.Finite 𝒪 A] : IsNoetherianRing A := by
  have : IsNoetherian 𝒪 A := inferInstance
  exact isNoetherian_of_tower 𝒪 this

end TQStruct
end
end P2MW.S_CuspForm_TWLevel_HeckeRing_finite_and_isLocalRing_and_isAdicComplete
