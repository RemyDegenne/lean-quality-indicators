namespace P2MW.S_WeierstrassCurve_exists_veluFunctionFieldHom_restrictAlong_placeOfPoint_eq

attribute [-instance] WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly

set_option autoImplicit false

set_option linter.unusedVariables false

set_option linter.unusedSectionVars false

set_option linter.unusedSimpArgs false

set_option maxHeartbeats 3200000

set_option synthInstance.maxHeartbeats 1600000

noncomputable section

scoped instance instFactNatPrime2_s13s2c : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

scoped instance instFactNatPrime3_s13s2c : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩

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

section

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

section

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

section

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

p2m_reactivate

section

section

p2m_open

p2m_open_scoped

noncomputable section

namespace WeierstrassCurve

namespace Affine

p2m_open

p2m_open

universe u

variable {F : Type u} [Field F] {W : Affine F}

section InverseOnX

variable [DecidableEq F] (hΔ : W.Δ ≠ 0) {a b : F} (hA : W.Equation a b)

local notation "ι" => algebraMap F W.FunctionField

include hΔ hA in
theorem translationAlgEquivOf_addXFun_negY :
    translationAlgEquivOf hΔ hA (W.addXFun a (W.negY a b)) = polyToFunctionField W X := by
  have key := addFun_neg_cancel_X hΔ hA
  rw [Affine.slope_of_X_ne (addXFun_ne_algebraMap hΔ hA)] at key
  rw [addXFun, Affine.slope_of_X_ne (polyToFunctionField_X_ne_algebraMap a)]
  set τ := translationAlgEquivOf hΔ hA
  have hτX : τ (polyToFunctionField W X) = W.addXFun a b :=
    translationAlgEquivOf_polyToFunctionField_X hΔ hA
  have hτY : τ (yGen W) = W.addYFun a b := translationAlgEquivOf_yGen hΔ hA
  have hτι : ∀ c : F, τ (ι c) = ι c := fun c => τ.commutes c
  simp only [Affine.addX, map_a₁, map_a₂] at key ⊢
  simp only [map_sub, map_add, map_mul, map_pow, map_div₀, hτX, hτY, hτι]
  exact key

end InverseOnX
end Affine
end WeierstrassCurve
end
end
end
end
end
end
end
end
end
end
end P2MW.S_WeierstrassCurve_exists_veluFunctionFieldHom_restrictAlong_placeOfPoint_eq
