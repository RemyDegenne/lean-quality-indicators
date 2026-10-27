namespace P2MW.S_CohCarrier_HeckeData_exists_linearEquiv_ML_of_toML_op_sub_opAlgHom_pow_mem

attribute [-instance] IharaLemma.IdempotentSplitting.isScalarTower_base_cornerModule IharaLemma.IdempotentSplitting.isScalarTower_base_cornerRing IharaLemma.IdempotentSplitting.algebraBaseCornerRing IharaLemma.IdempotentSplitting.smulCornerModule IharaLemma.IdempotentSplitting.moduleCornerModule IharaLemma.IdempotentSplitting.isLocalRing_cornerRing IharaLemma.IdempotentSplitting.coeOutCornerRing IharaLemma.IdempotentSplitting.isMaximal_𝔪 IharaLemma.IdempotentSplitting.isScalarTower_cornerModule IharaLemma.IdempotentSplitting.isLocalization_cornerRing

set_option autoImplicit false

set_option synthInstance.maxHeartbeats 1600000

set_option maxHeartbeats 3200000

attribute [local instance] CohCarrier.HeckeData.moduleFreeAlg

noncomputable section

open CohCarrier IsLocalRing

namespace TWExt

section Setting

variable {𝒪 : Type} [CommRing 𝒪] [IsLocalRing 𝒪]
  {k : Type} [Field k] [Algebra 𝒪 k]
  {V : Type} [AddCommGroup V] [Module 𝒪 V]
  (DV DE : HeckeData 𝒪 V k) (σ : DV.Gen ⊕ Unit ≃ DE.Gen)
  (hop : ∀ g : DV.Gen, DE.op (σ (Sum.inl g)) = DV.op g) (z₀ : DV.FreeAlg)

local notation "FV" => DV.FreeAlg

local notation "FE" => DE.FreeAlg

local notation "SV" => DV.mTheta.primeCompl

local notation "SE" => DE.mTheta.primeCompl

local notation "Z♭" => DE.op (σ (Sum.inr ()))

local notation "N♯" => Car FE DV.ML (modN DV DE σ hop)

scoped instance instTowerN : IsScalarTower 𝒪 FE N♯ := (DML DV DE σ hop).V_isScalarTower

def ren : FV →ₐ[𝒪] FE := MvPolynomial.rename (fun g => σ (Sum.inl g))

end Setting
end TWExt
end
end P2MW.S_CohCarrier_HeckeData_exists_linearEquiv_ML_of_toML_op_sub_opAlgHom_pow_mem
