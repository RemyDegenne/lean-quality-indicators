namespace P2MW.S_ModularCurve_exists_algHom_qExpFunctionFieldC_gammaH_eq_slot_and_diamondPullbackModL_eq_qTwist

attribute [-instance] CohCarrier.HeckeData.V_isScalarTower CohCarrier.HeckeData.opSubalgebra_isMulCommutative CohCarrier.HeckeData.mTheta_isPrime

set_option autoImplicit false

set_option linter.unusedSectionVars false

set_option linter.unusedVariables false

set_option synthInstance.maxHeartbeats 1600000

noncomputable section

open Complex UpperHalfPlane ModularForm CongruenceSubgroup Function ModularCurve HahnSeries

open scoped Real MatrixGroups ModularForm Manifold Pointwise

namespace XHCuspChart

local notation "Γᴳ(" M ", " H ")" =>
  ((CohCarrier.GammaH M H : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ))

local notation "ℤ̄" => (integralClosure ℤ ℂ)

section Lifts

variable {M : ℕ} [NeZero M]

variable (K : Type*) [Field K] (φ : ℤ̄ →+* K)

variable {H : Subgroup (ZMod M)ˣ} {k : ℤ}

def liftI (P : PowerSeries ℂ) (h : ∀ n, IsIntegral ℤ (P.coeff n)) : PowerSeries ℤ̄ :=
  PowerSeries.mk fun n => ⟨P.coeff n, h n⟩

end Lifts
end XHCuspChart
end
end P2MW.S_ModularCurve_exists_algHom_qExpFunctionFieldC_gammaH_eq_slot_and_diamondPullbackModL_eq_qTwist
