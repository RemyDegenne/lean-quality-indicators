namespace P2MW.S_CohCarrier_exists_perfect_selfAdjoint_degeneracyAdjoint_pairing_map_iDegL_parabolicHoms

attribute [-instance] ModularCurve.PDPairing.isFreeGroup_inf ModularCurve.PDPairing.instFintypeCusp ModularCurve.PDPairing.iotaDeg0_range_finiteIndex ModularCurve.PDPairing.CentralExt.instInv ModularCurve.PDPairing.CentralExt.instGroup ModularCurve.PDPairing.CentralExt.instMul ModularCurve.PDPairing.CentralExt.instOne ModularCurve.PDPairing.Gamma0Upper_finiteIndex ModularCurve.Period.parabolicHoms_int_moduleFinite ModularCurve.Period.instGroupFG_SL2Z ModularCurve.Period.instIsNoetherian_addHom_int ModularCurve.Period.instGroupFG_Gamma0 HeckeEis.instFiniteIndexHeckeUpper

set_option autoImplicit false

open CongruenceSubgroup CohCarrier

open scoped MatrixGroups

namespace CohL2

namespace Head

variable (𝒪 : Type) [CommRing 𝒪]

variable (M : ℕ) (H : Subgroup (ZMod M)ˣ) (h₁ : LevelLE M M ⊤ H 1)

noncomputable def sEquiv [NeZero M] (hu : IsUnit ((H.index : ℕ) : 𝒪)) : ↥(Par 𝒪 M) ≃ₗ[𝒪] ↥(W 𝒪 M H h₁) :=
  LinearEquiv.ofBijective (sMap 𝒪 M H h₁) ⟨sMap_injective 𝒪 M H h₁ hu, sMap_surjective 𝒪 M H h₁⟩

end Head
end CohL2
end P2MW.S_CohCarrier_exists_perfect_selfAdjoint_degeneracyAdjoint_pairing_map_iDegL_parabolicHoms
