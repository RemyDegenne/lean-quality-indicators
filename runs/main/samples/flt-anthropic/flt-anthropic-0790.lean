namespace P2MW.S_ModularCurve_LevelRelabelling_exists_natural_zsmul_gamma1Point

attribute [-instance] WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly ModularCurve.LevelP.instCommRingUnivBase ModularCurve.LevelP.instAwayMvPolynomialFinOfNatNatIntPDeltaUnivBase ModularCurve.LevelP.instCommRingTorsionPointRing ModularCurve.LevelP.instCommRingPsiRoot ModularCurve.LevelP.instIsScalarTowerTwoPointRingBasisRing ModularCurve.LevelP.instAlgebraPsiRoot ModularCurve.LevelP.instIsScalarTowerPsiRootTorsionPointRing ModularCurve.LevelP.instAlgebraMvPolynomialFinOfNatNatIntUnivBase ModularCurve.LevelP.instAlgebraTwoPointRing ModularCurve.LevelP.instIsScalarTowerTorsionPointRingTwoPointRing ModularCurve.LevelP.instAwayTwoPointRingIndepDenomBasisRing ModularCurve.LevelP.instCommRingBasisRing ModularCurve.LevelP.instAlgebraTorsionPointRing ModularCurve.LevelP.instAlgebraPsiRootTorsionPointRing ModularCurve.LevelP.instAlgebraBasisRing ModularCurve.LevelP.instAlgebraTwoPointRingBasisRing AlgebraicCurve.Place.instIsScalarTowerSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Divisor.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instSMulAlgEquiv AlgebraicCurve.Place.instIsPrincipalIdealRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instIsDiscreteValuationRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Pic0.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instAlgebraSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instMulActionAlgEquiv AlgebraicCurve.Pic0.instSMulAlgEquiv AlgebraicCurve.CurveModel.isProper AlgebraicCurve.CurveModel.isIntegral AlgebraicCurve.CurveModel.smooth instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv

set_option autoImplicit false

set_option linter.unusedVariables false

noncomputable section

p2m_open

open scoped Classical

attribute [local instance] MvPolynomial.gradedAlgebra

universe u

namespace ModularCurve

namespace LevelRelabelling

namespace DiamAlg

p2m_open

variable {T : Type u} [CommRing T] {W : WeierstrassCurve.Projective T} (G : RelativeGroupLaw T (projModelStrCR W))

theorem zsmulSection_eq_zpow (n : ℤ) (x : Section W) :
    letI := G.pointGroup (𝟙 _); zsmulSection G n x = x ^ n := by
  letI := G.pointGroup (𝟙 _)
  cases n with
  | ofNat k =>
    show G.nsmul (𝟙 _) k x = x ^ ((k : ℕ) : ℤ)
    rw [nsmul_eq_pow, zpow_natCast]
  | negSucc k =>
    show G.inv (𝟙 _) (G.nsmul (𝟙 _) (k + 1) x) = x ^ (Int.negSucc k)
    rw [nsmul_eq_pow, zpow_negSucc]
    rfl

end DiamAlg
end LevelRelabelling
end ModularCurve
end
end P2MW.S_ModularCurve_LevelRelabelling_exists_natural_zsmul_gamma1Point
