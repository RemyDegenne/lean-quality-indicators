namespace P2MW.S_WeierstrassCurve_Affine_IsogenyEndDatum_exists_restrictAlong_placeOfPoint_eq_add

attribute [-instance] WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy

set_option autoImplicit false

set_option linter.unusedVariables false

set_option linter.unusedSectionVars false

set_option linter.unusedSimpArgs false

set_option maxHeartbeats 3200000

noncomputable section

scoped instance instFactNatPrime2_s13e2 : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

scoped instance instFactNatPrime3_s13e2 : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩

scoped instance instFactNatPrime7_s13e2 : Fact (Nat.Prime 7) := ⟨by norm_num⟩

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

set_option synthInstance.maxHeartbeats 800000

set_option maxHeartbeats 6400000

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

section

p2m_reactivate

section

section

noncomputable section

set_option linter.unusedSectionVars false

p2m_open

namespace WeierstrassCurve

namespace Affine

p2m_open

universe u

variable {F : Type u} [Field F] [DecidableEq F] [IsAlgClosed F] [CharZero F]

variable (W : Affine F) [W.IsElliptic] [WeierstrassCurve.Affine.GenusOnePlaceGate W] [WeierstrassCurve.Affine.GenusOnePlaceGate.IsCentred W] [WeierstrassCurve.Affine.AbelTheorem W]

def placeOfPointEquiv : W.Point ≃ AlgebraicCurve.Place F W.FunctionField :=
  Equiv.ofBijective placeOfPoint
    ⟨placeOfPoint_injective, placeOfPoint_surjective (Δ_ne_zero_of_isElliptic W)⟩

end Affine
end WeierstrassCurve
end
end
end
end
end
end P2MW.S_WeierstrassCurve_Affine_IsogenyEndDatum_exists_restrictAlong_placeOfPoint_eq_add
