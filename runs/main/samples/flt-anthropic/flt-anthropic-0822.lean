namespace P2MW.S_ModularCurve_FullLevel_AuxLevelOne_formallySmooth_fiber_maximalIdeal_blowupChart_of_drinfeldChartWitness_of_dvd

attribute [-instance] ModularCurve.PhiGen.instNeZeroPhiGenCosetA

set_option autoImplicit false

set_option maxHeartbeats 12800000

set_option synthInstance.maxHeartbeats 1600000

open CategoryTheory AlgebraicGeometry IsLocalRing AlgebraicCurve.TwoChartIntegralModel

open scoped MatrixGroups

namespace SpecialFibreAssembly

theorem gamma_le_gammaH (N : ℕ) [NeZero N] (H : Subgroup (ZMod N)ˣ) :
    CongruenceSubgroup.Gamma N ≤ CohCarrier.GammaH N H := by
  intro γ hγ
  rw [CohCarrier.mem_GammaH_iff]
  rw [CongruenceSubgroup.Gamma_mem] at hγ
  have h0 : γ ∈ CongruenceSubgroup.Gamma0 N := by
    rw [CongruenceSubgroup.Gamma0_mem]; exact hγ.2.2.1
  refine ⟨h0, ?_⟩
  have : CohCarrier.gamma0Units N ⟨γ, h0⟩ = 1 := by
    ext
    rw [CohCarrier.val_gamma0Units, Units.val_one]
    exact hγ.2.2.2
  rw [this]; exact one_mem H

end SpecialFibreAssembly
end P2MW.S_ModularCurve_FullLevel_AuxLevelOne_formallySmooth_fiber_maximalIdeal_blowupChart_of_drinfeldChartWitness_of_dvd
