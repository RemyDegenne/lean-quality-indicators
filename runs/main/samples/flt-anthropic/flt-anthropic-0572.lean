namespace P2MW.S_ModularCurve_exists_monoidHom_gamma0_algEquiv_qExpFunctionFieldC_gammaH

attribute [-instance] TateModule.instModule TateModule.instSMul GaloisRepAdic.instAddCommGroup GaloisRepAdic.instFree GaloisRepAdic.instFinite GaloisRepAdic.instModule ResidualGaloisRep.instModule ResidualGaloisRep.instModuleFinite ResidualGaloisRep.instAddCommGroup WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv CohCarrier.HeckeData.V_isScalarTower CohCarrier.HeckeData.opSubalgebra_isMulCommutative CohCarrier.HeckeData.mTheta_isPrime

set_option autoImplicit false

noncomputable section

open scoped MatrixGroups ModularForm

open UpperHalfPlane

namespace ModularCurve

p2m_open

namespace DiamondAct

local notation "Γ₁ℝ" M => ((CongruenceSubgroup.Gamma1 M : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ))

local notation "Γᴴℝ" M "," H => ((CohCarrier.GammaH M H : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ))

section QExp

variable {M : ℕ} [NeZero M] {H : Subgroup (ZMod M)ˣ} {k : ℤ}

theorem isIntegralQExp_mul {k₁ k₂ : ℤ} {f : ModularForm (Γᴴℝ M, H) k₁} {g : ModularForm (Γᴴℝ M, H) k₂}
    {p r : PowerSeries ℤ} (hf : IsIntegralQExp (⇑f) p) (hg : IsIntegralQExp (⇑g) r) :
    IsIntegralQExp (⇑(f.mul g)) (p * r) := by
  unfold IsIntegralQExp at hf hg ⊢
  rw [ModularForm.coe_mul, qExpansion_mul (analyticAt_form f) (analyticAt_form g), map_mul, hf, hg]

end QExp
end DiamondAct
end ModularCurve
end
end P2MW.S_ModularCurve_exists_monoidHom_gamma0_algEquiv_qExpFunctionFieldC_gammaH
