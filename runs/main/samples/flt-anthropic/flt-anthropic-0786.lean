namespace P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_forall_isUnit_mul_pow_nodeIntegers_and_ord_residueFst_eq_and_forall_ord_eq_zero

attribute [-instance] AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly ModularCurve.ElevenA1.instDecidableEquation ModularCurve.ElevenA1.instDecidableNonsingular ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.TatePoint.instIsElliptic_nearCurve ModularCurve.instIsElliptic_tateLaurent ModularCurve.B3.instIsElliptic_goodModel WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral ModularCurve.instAlgebraJLineBar ModularCurve.instModuleJLineBar AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions

attribute [-instance] AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion ModularCurve.instIsScalarTowerJAdjoin WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4 ModularCurve.NodeLocalized.isScalarTower_K_fieldOver_bar ModularCurve.NodeLocalized.algebraFieldOverBar ModularCurve.NodeLocalized.algebra_isIntegral_fieldOver_bar ModularCurve.NodeLocalized.isScalarTower_fieldOver_bar_laurent ModularCurve.NodeLocalized.charZero_fieldOver ModularCurve.NodeLocalized.algebraFieldOver ModularCurve.NodeLocalized.charZero_laurentSeries_algClosure ValuationSubring.instIsAlgClosedResidueField ModularCurve.numberField_of_finiteDimensional ModularCurve.instIsElliptic_tateBase

set_option synthInstance.maxHeartbeats 1600000

set_option maxHeartbeats 1600000

set_option autoImplicit false

open AlgebraicCurve IsLocalRing ModularCurve

open ModularCurve.PlaceSpecialization ModularCurve.PlaceSpecialization.ProlongationTuple

noncomputable section

namespace P2mWs18V56

variable {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N]
  {k : Type*} [Field k] [CharP k q] {red : A →+* k}
  {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
  {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q} {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
  {P : PlaceSpecialization A q N data hKr k red hα hβ}
  (R : ProlongationTuple P) [IsAlgClosed k] [DecidableEq k] (hqN : ¬ q ∣ N)
  (W : Finset (Place k (modularFunctionFieldC k N))) (hW : ∀ w, w ∈ W ↔ w ∈ ssPlaces q N k)
  (hreg : R.RegularityLaw W) (hO : R.OrderLawFixed)

local notation "𝔽" => modularFunctionFieldBar (N * q)

local notation "Pl0" => Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))

local notation "Plk" => Place k (modularFunctionFieldC k N)

section Clearing

variable (hmodel : R.IsModel) (hval : R.NodeValueLaw W)
  (T : Finset (Place k (modularFunctionFieldC k N))) (hTW : ∀ t ∈ T, t ∉ W)

include hqN hW hreg hO hmodel hval hTW in

theorem exists_mover {V₀ : Pl0} (hV₀ : P.reduceFst V₀ ∈ T) :
    ∃ g : 𝔽, MoverLike R W g ∧ V₀.ord g = 1 ∧ ∀ V : Pl0, V ≠ V₀ → P.reduceFst V ∈ T → V.ord g = 0 := by
  classical
  have hT : ∀ t ∈ T, t ∉ ssPlaces q N k := fun t ht hss => hTW t ht ((hW t).2 hss)
  obtain ⟨g, D, hg0, ⟨h₁, h₂, hr₁, hr₂⟩, hD, hDV₀, hstrict, hnotT, -⟩ :=
    exists_ord_eq_one_forall_isStrict_reduceFst_reduceSnd_notMem_forall_inertia_smul_eq_of_isModel q A N k red data
      hKr hα hβ hqN P W hW R hmodel hreg hval hO T hT V₀ (Or.inl hV₀)
  refine ⟨g, ⟨hg0, ⟨h₁, residue_ne_zero_of_residue₁_ne_zero R hr₁⟩, ⟨h₂, residue_ne_zero_of_residue₂_ne_zero R hr₂⟩,
    fun w hw V hVw => ?_⟩, ?_, fun V hne hVT => ?_⟩
  ·
    rw [← hD]
    by_contra hne0
    have hVs : V ∈ D.support := Finsupp.mem_support_iff.mpr hne0
    have hVne : V ≠ V₀ := by
      rintro rfl
      exact hTW _ hV₀ (by rw [hVw]; exact hw)
    have hfix : frobOnPlacesGeomLevel k N data hKr (frobOnPlacesGeomLevel k N data hKr (P.reduceFst V))
        = P.reduceFst V := by
      rw [hVw]; exact fixed_of_mem_W hqN W hW hw
    rcases hstrict V hVs hVne with hs | hs
    · exact not_isStrictFst_of_fixed hfix hs
    · exact not_isStrictSnd_of_fixed hfix hs
  · rw [← hD]; exact hDV₀
  · rw [← hD]
    by_contra hne0
    exact (hnotT V (Finsupp.mem_support_iff.mpr hne0) hne).1 hVT

end Clearing
end P2mWs18V56
end
end P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_forall_isUnit_mul_pow_nodeIntegers_and_ord_residueFst_eq_and_forall_ord_eq_zero
