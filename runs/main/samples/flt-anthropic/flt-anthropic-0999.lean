namespace P2MW.S_ModularCurve_FullLevel_comap_gauss_eq_iff_redQ_smul_lineInfty_eq_of_levelAutBar_apply

attribute [-instance] AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion ModularCurve.PhiGen.instNeZeroPhiGenCosetA ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois

attribute [-instance] ModularCurve.instIsElliptic_tateBase ModularCurve.instIsElliptic_tateLaurent ModularCurve.KatzGamma0Form.instModule ModularCurve.KatzGamma0Form.instZero ModularCurve.KatzLevelPForm.instSMul ModularCurve.KatzGamma0Form.instAdd ModularCurve.KatzLevelPForm.instAddCommGroup ModularCurve.KatzGamma0Form.instNeg ModularCurve.KatzGamma0Form.instAddCommGroup ModularCurve.KatzLevelPForm.instAdd ModularCurve.KatzLevelPForm.instSub ModularCurve.KatzLevelPForm.instNeg ModularCurve.KatzGamma0Form.instSMul ModularCurve.KatzGamma0Form.instSub ModularCurve.KatzLevelPForm.instZero ModularCurve.KatzLevelPForm.instModule KatzModularForm.instAddCommGroup KatzModularForm.instSub KatzModularForm.instZero KatzModularForm.instModule KatzModularForm.instAdd KatzModularForm.instNeg KatzModularForm.instSMul WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4 ModularCurve.ElevenA1.instDecidableEquation ModularCurve.ElevenA1.instDecidableNonsingular ModularCurve.Gamma0Pair.isElliptic CuspForm.instModuleZModIntTwoCuspForms CuspForm.instAddCommGroupIntTwoCuspForms ModularCurve.instAlgebraIntermediateFieldLaurent

attribute [-instance] ModularCurve.instIsScalarTowerKaehlerIntermediateFieldLaurent ModularCurve.instIsScalarTowerIntermediateFieldLaurent ModularCurve.instModuleKaehlerIntermediateFieldLaurent CuspForm.instModuleTwoCuspForms CuspForm.instIsScalarTowerTwoCuspForms CuspForm.instAddCommGroupTwoCuspForms CuspForm.instIsScalarTowerSelfTwoCuspForms CuspForm.instModuleQuotientTwoCuspForms CuspForm.GammaH_finiteIndex

set_option autoImplicit false

open scoped MatrixGroups

p2m_open

theorem solution
    (q : ℕ) [Fact q.Prime] (hq : 5 ≤ q) (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M')
    (L : Type) [Field L] [CharZero L]
    (ζ : L) (hζ : IsPrimitiveRoot ζ q)
    (hι : ∃ ι : L →+* ℂ, ι ζ = Complex.exp (2 * Real.pi * Complex.I / q))
    [Algebra.IsAlgebraic ℚ L]
    (K : IntermediateField L (LaurentSeries L))
    (hK : K = ModularCurve.laurentBaseChange L
      (ModularCurve.xHFunctionField (q ^ 2 * M') (ModularCurve.FullLevel.levelH q M')))
    (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Algebra A L] [IsFractionRing A L]
    (hAq : (q : A) ∈ IsLocalRing.maximalIdeal A) (hζA : ∃ x : A, algebraMap A L x = ζ)
    (W₀ : ValuationSubring ↥K)
    (hW₀ : ∀ f : ↥K, f ∈ W₀ ↔ ∃ x y : PowerSeries A, y.map (IsLocalRing.residue A) ≠ 0 ∧
      (f : LaurentSeries L) * HahnSeries.ofPowerSeries ℤ L (y.map (algebraMap A L))
        = HahnSeries.ofPowerSeries ℤ L (x.map (algebraMap A L)))
    (τ : SL(2, ℤ) → (↥K ≃ₐ[L] ↥K))
    (hτ : ∀ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma0 M' →
      ModularCurve.FullLevel.IsLevelAutAt L q ζ q (q ^ 2 * M') (ModularCurve.FullLevel.levelH q M') γ⁻¹ K (τ γ))

    (e : L →+* AlgebraicClosure ℚ)
    (A' : ValuationSubring (AlgebraicClosure ℚ)) (hA' : A'.LiesOverPrime q)
    (ζ' : ModularCurve.FullLevel.Idx q) (hζ' : ζ'.val = e ζ)
    (ιK : ↥K →+* ↥(ModularCurve.FullLevel.fieldBar q M'))
    (hιK : ∀ x : ↥K, ((ιK x : ↥(ModularCurve.FullLevel.fieldBar q M')) : LaurentSeries (AlgebraicClosure ℚ)) =
      ModularCurve.coeffMap e (x : LaurentSeries L))
    (O : ValuationSubring ↥(ModularCurve.FullLevel.fieldBar q M'))
    (hO : ∀ f : ↥(ModularCurve.FullLevel.fieldBar q M'), f ∈ O ↔
      ∃ x y : LaurentSeries ↥A', ModularCurve.coeffMap (IsLocalRing.residue ↥A') y ≠ 0 ∧
        (f : LaurentSeries (AlgebraicClosure ℚ)) * ModularCurve.coeffMap A'.subtype y = ModularCurve.coeffMap A'.subtype x)
    (hOW : ∀ f : ↥K, ιK f ∈ O ↔ f ∈ W₀)
    (hIT : ∀ ε : SL(2, ℤ), ε ∈ CongruenceSubgroup.Gamma0 M' → ∀ σ : ↥K ≃ₐ[L] ↥K,
      ModularCurve.FullLevel.IsLevelAutAt L q ζ q (q ^ 2 * M') (ModularCurve.FullLevel.levelH q M') ε K σ →
      ∀ x : ↥K, ιK (σ x) = ModularCurve.FullLevel.levelAutBar q M' ζ' ε (ιK x))
    (φ : ↥K ≃ₐ[L] ↥K) (ε : SL(2, ℤ)) (hε : ε ∈ CongruenceSubgroup.Gamma0 M')
    (hφ : ∀ x : ↥K, ιK (φ x) = ModularCurve.FullLevel.levelAutBar q M' ζ' ε (ιK x)) :
    W₀.comap φ.toAlgHom.toRingHom = W₀ ↔
      ModularCurve.FullLevel.redQ q ε • ModularCurve.FullLevel.lineInfty q = ModularCurve.FullLevel.lineInfty q := by
  classical
  haveI hqne : NeZero q := ⟨(Fact.out : q.Prime).ne_zero⟩
  subst hK

  have fix : ∀ (ψ : ↥(laurentBaseChange L (xHFunctionField (q ^ 2 * M') (levelH q M'))) ≃ₐ[L]
      ↥(laurentBaseChange L (xHFunctionField (q ^ 2 * M') (levelH q M')))) (ρ : SL(2, ℤ)),
      ρ ∈ Gamma0 M' → (∀ x, ιK (ψ x) = levelAutBar q M' ζ' ρ (ιK x)) →
      redQ q ρ • lineInfty q = lineInfty q → W₀.comap ψ.toAlgHom.toRingHom = W₀ := by
    intro ψ ρ hρ hψ hfixρ
    have hO' := ModularCurve.FullLevel.comap_levelAutBar_eq_of_redQ_smul_lineInfty_eq
      q hq M' hqM' A' hA' ζ' O hO ρ hρ hfixρ
    ext f
    rw [ValuationSubring.mem_comap]
    change ψ f ∈ W₀ ↔ f ∈ W₀
    rw [← hOW (ψ f), ← hOW f, hψ f]
    conv_rhs => rw [← hO', ValuationSubring.mem_comap]
    rfl
  refine ⟨fun hW => ?_, fix φ ε hε hφ⟩
  by_contra hne

  have hc : ((ε 1 0 : ℤ) : ZMod q) ≠ 0 := fun h => hne ((StabElem.redQ_smul_lineInfty_eq_iff q ε).2 h)
  set a : ZMod q := ((ε 0 0 : ℤ) : ZMod q) with ha
  set c : ZMod q := ((ε 1 0 : ℤ) : ZMod q) with hcdef
  set xz : ℤ := (((-a * c⁻¹ : ZMod q).val : ℕ) : ℤ) with hxz
  have hxzq : ((xz : ℤ) : ZMod q) = -a * c⁻¹ := by
    rw [hxz, Int.cast_natCast, ZMod.natCast_zmod_val]
  let βM : Matrix (Fin 2) (Fin 2) ℤ := !![1, xz; 0, 1]
  have hβdet : βM.det = 1 := by simp [βM, Matrix.det_fin_two_of]
  let β : SL(2, ℤ) := ⟨βM, hβdet⟩
  have hβ10 : ((β 1 0 : ℤ) : ZMod q) = 0 := by
    show (((βM 1 0 : ℤ)) : ZMod q) = 0
    simp [βM]
  have hβ0 : β ∈ Gamma0 M' := by
    rw [Gamma0_mem]
    show (((βM 1 0 : ℤ)) : ZMod M') = 0
    simp [βM]
  have hβfix : redQ q β • lineInfty q = lineInfty q := (StabElem.redQ_smul_lineInfty_eq_iff q β).2 hβ10
  have hprod : (q : ℤ) ∣ ((β * ε : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 0 0 := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    have hentry : ((β * ε : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 0 0 = (ε 0 0 : ℤ) + xz * (ε 1 0 : ℤ) := by
      rw [Matrix.SpecialLinearGroup.coe_mul]
      show (βM * (ε : Matrix (Fin 2) (Fin 2) ℤ)) 0 0 = _
      simp [βM, Matrix.mul_apply, Fin.sum_univ_two]
    rw [hentry]
    push_cast
    rw [hxzq, ← ha, ← hcdef]
    rw [mul_assoc, inv_mul_cancel₀ hc, mul_one, add_neg_cancel]

  have hτβ : IsLevelAutAt L q ζ q (q ^ 2 * M') (levelH q M') β
      (laurentBaseChange L (xHFunctionField (q ^ 2 * M') (levelH q M'))) (τ β⁻¹) := by
    have := hτ β⁻¹ (inv_mem hβ0)
    rwa [inv_inv] at this
  have hφβ : ∀ x, ιK (τ β⁻¹ x) = levelAutBar q M' ζ' β (ιK x) := hIT β hβ0 (τ β⁻¹) hτβ
  have hWβ : W₀.comap (τ β⁻¹).toAlgHom.toRingHom = W₀ := fix (τ β⁻¹) β hβ0 hφβ hβfix
  set χ := (τ β⁻¹).trans φ with hχdef
  have hχ : ∀ x, ιK (χ x) = levelAutBar q M' ζ' (β * ε) (ιK x) := by
    intro x
    rw [hχdef, AlgEquiv.trans_apply, hφ, hφβ,
      ModularCurve.FullLevel.levelAutBar_mul q M' hqM' ζ' β ε hβ0 hε, AlgEquiv.trans_apply]
  have e1 : ∀ g, φ g ∈ W₀ ↔ g ∈ W₀ := fun g => by
    have := SetLike.ext_iff.mp hW g
    rwa [ValuationSubring.mem_comap] at this
  have e2 : ∀ g, τ β⁻¹ g ∈ W₀ ↔ g ∈ W₀ := fun g => by
    have := SetLike.ext_iff.mp hWβ g
    rwa [ValuationSubring.mem_comap] at this
  have hWχ : W₀.comap χ.toAlgHom.toRingHom = W₀ := by
    ext f
    rw [ValuationSubring.mem_comap]
    change χ f ∈ W₀ ↔ f ∈ W₀
    rw [hχdef, AlgEquiv.trans_apply, e1, e2]

  have hjQ : jqModC ℚ ∈ xHFunctionField (q ^ 2 * M') (levelH q M') :=
    intFormRatiosC_subset ℚ _ (ModularCurve.jqModC_mem_intFormRatiosC ℚ _)
  set jK : ↥(laurentBaseChange L (xHFunctionField (q ^ 2 * M') (levelH q M'))) :=
    ⟨coeffEmb L (jqModC ℚ), coeffEmb_mem_laurentBaseChange L hjQ⟩ with hjKdef
  have hjcoe : (jK : LaurentSeries L) = jqModC L := map_jqModC (algebraMap ℚ L)
  have hιKj : ((ιK jK : ↥(fieldBar q M')) : LaurentSeries (AlgebraicClosure ℚ)) = jqModC (AlgebraicClosure ℚ) := by
    rw [hιK, hjcoe]; exact map_jqModC e
  have hgmem : jqModC (AlgebraicClosure ℚ) ∈
      laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ (Gamma0 M')) := by
    have h0 : jqModC ℚ ∈ qExpFunctionFieldC ℚ (Gamma0 M') :=
      intFormRatiosC_subset ℚ _ (ModularCurve.jqModC_mem_intFormRatiosC ℚ _)
    have h1 := coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) h0
    have h2 : coeffEmb (AlgebraicClosure ℚ) (jqModC ℚ) = jqModC (AlgebraicClosure ℚ) := map_jqModC _
    rwa [h2] at h1
  have hLj := ModularCurve.FullLevel.coe_levelAutBar_apply_eq_qExpand_sq_of_dvd_of_mem_laurentBaseChange_gamma0
    q M' hqM' ζ' (β * ε) (mul_mem hβ0 hε) hprod (jqModC (AlgebraicClosure ℚ)) hgmem (ιK jK) hιKj
  have hχj : ((χ jK : ↥(laurentBaseChange L (xHFunctionField (q ^ 2 * M') (levelH q M')))) : LaurentSeries L) =
      qExpand L (q ^ 2) (jqModC L) := by
    apply StabElem.coeffMap_injective e e.injective
    rw [← hιK, hχ jK, hLj, StabElem.coeffMap_qExpand, ← hjcoe, ← hιK, hιKj]
  exact ModularCurve.comap_gauss_ne_of_coe_apply_eq_qExpand_sq_jqModC q L _ A hAq W₀ hW₀ χ jK hjcoe hχj hWχ

end P2MW.S_ModularCurve_FullLevel_comap_gauss_eq_iff_redQ_smul_lineInfty_eq_of_levelAutBar_apply
