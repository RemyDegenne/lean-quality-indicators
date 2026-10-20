namespace P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_hasValue_iff_hasValue_residueFst_zero_jIntegralClosure_of_sp_eq_spPlace

attribute [-instance] AlgebraicCurve.CurveModel.algebraAdjoin AlgebraicCurve.CurveModel.isDedekindDomain_chartRing AlgebraicCurve.CurveModel.isIntegralClosure AlgebraicCurve.CurveModel.finite_chartRing AlgebraicCurve.CurveModel.centre_isPrime AlgebraicCurve.CurveModel.isFractionRing_chartRing AlgebraicCurve.CurveModel.finiteType_chartRing AlgebraicCurve.CurveModel.isNoetherianRing_chartRing AlgebraicCurve.CurveModel.isScalarTower_base_adjoin AlgebraicCurve.CurveModel.isScalarTower_adjoin AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly ModularCurve.ElevenA1.instDecidableEquation ModularCurve.ElevenA1.instDecidableNonsingular ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.TatePoint.instIsElliptic_nearCurve ModularCurve.instIsElliptic_tateLaurent ModularCurve.B3.instIsElliptic_goodModel WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral GaloisRepAdic.instAddCommGroup GaloisRepAdic.instFree GaloisRepAdic.instFinite GaloisRepAdic.instModule ResidualGaloisRep.instModule ResidualGaloisRep.instModuleFinite ResidualGaloisRep.instAddCommGroup WeierstrassCurve.Affine.Point.instFinite AlgebraicCurve.CurveModel.isProper AlgebraicCurve.CurveModel.isIntegral AlgebraicCurve.CurveModel.smooth ModularCurve.IgusaScheme.isOpenImmersion_fInf

attribute [-instance] ModularCurve.IgusaScheme.isOpenImmersion_ιInf ModularCurve.IgusaScheme.fact_jFull_ne_zero ModularCurve.IgusaScheme.isOpenImmersion_ιFin ModularCurve.IgusaScheme.isOpenImmersion_fFin AlgebraicCurve.CurveModel.locallyOfFiniteType_gluedToBase AlgebraicCurve.CurveModel.isFractionRing_overlap AlgebraicCurve.CurveModel.isLocallyNoetherian_glued AlgebraicCurve.CurveModel.jacobsonSpace_glued AlgebraicCurve.CurveModel.isOpenImmersion_ι₀ AlgebraicCurve.CurveModel.isIntegral_glued AlgebraicCurve.CurveModel.quasiSeparated_gluedToBase AlgebraicCurve.CurveModel.compactSpace_glued AlgebraicCurve.CurveModel.isIntegral_adjoin_chartRing AlgebraicCurve.CurveModel.isFractionRing_overlap_functionField AlgebraicCurve.CurveModel.isProper_gluedToBase AlgebraicCurve.CurveModel.isOpenImmersion_ιU AlgebraicCurve.CurveModel.isOpenImmersion_f₀ AlgebraicCurve.CurveModel.isOpenImmersion_fInf AlgebraicCurve.CurveModel.isOpenImmersion_ιInf AlgebraicCurve.CurveModel.algebra_overlap_functionField AlgebraicCurve.CurveModel.quasiCompact_gluedToBase AlgebraicCurve.CurveModel.chartRing_finitePresentation ModularCurve.instIsElliptic_tateBase ModularCurve.NodeLocalized.isLocalization_nodeDenominators ModularCurve.NodeLocalized.algebraEvalRange ModularCurve.NodeLocalized.isLocalRing_modularLocalizedAtPoint instTopologicallyFGOfFiniteType AdicCompletion.instIsLocalRingMaximalIdeal

set_option synthInstance.maxHeartbeats 1600000

set_option maxHeartbeats 3200000

set_option autoImplicit false

set_option linter.unusedVariables false

set_option linter.unusedSectionVars false

p2m_open

p2m_open

p2m_open

noncomputable section

p2m_reactivate

p2m_reactivate

namespace ModularCurve

namespace PlaceSpecialization

p2m_open

section ResidueHoms

variable {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
  {N : ℕ} [NeZero N] {k : Type*} [Field k] [CharP k q] {red : A →+* k}
  {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
  {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q}
  {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
  {P : PlaceSpecialization A q N data hKr k red hα hβ} (R : ProlongationTuple P)

variable (K : IntermediateField ℚ (AlgebraicClosure ℚ))

theorem c4_coe_g₂_cst (hqN : ¬ q ∣ N) (a : ↥(coeffSubring A K)) :
    ((c4_g₂ R K hqN (c4_cst K a) : ↥(c4D k N)) : modularFunctionFieldC k N)
      = algebraMap k (modularFunctionFieldC k N) (redRestrict red K a) := by
  rw [c4_coe_g₂, ← c4_res₂C_apply R K hqN, c4_res₂C_eq R K hqN]
  have hW : ProlongationTuple.atkinLehnerBar N q (c4_toBar K (c4_cst K a))
      = algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)) (a : AlgebraicClosure ℚ) := by
    rw [c4_toBar_cst]
    exact (ProlongationTuple.atkinLehnerBar N q).commutes (a : AlgebraicClosure ℚ)
  obtain ⟨h', hres⟩ := penC_residue_const R ⟨(a : AlgebraicClosure ℚ), a.2.1⟩
  rw [show (⟨ProlongationTuple.atkinLehnerBar N q (c4_toBar K (c4_cst K a)), c4_atkinLehnerBar_mem_integersFst R K hqN (c4_cst K a)⟩
      : ↥R.R₁.integers) = ⟨_, h'⟩ from Subtype.ext hW]
  exact hres

end ResidueHoms
end PlaceSpecialization
end ModularCurve
end
end P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_hasValue_iff_hasValue_residueFst_zero_jIntegralClosure_of_sp_eq_spPlace
