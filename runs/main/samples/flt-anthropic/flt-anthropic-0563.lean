namespace P2MW.S_ModularCurve_FullLevel_mem_iff_mem_igusaGaussRing_of_coe_eq_qExpand_of_forall_mem_integers_mem_of_eq_three

attribute [-instance] ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt ModularCurve.instIsElliptic_tateBase ModularCurve.instIsElliptic_tateLaurent ModularCurve.KatzGamma0Form.instModule ModularCurve.KatzGamma0Form.instZero ModularCurve.KatzLevelPForm.instSMul ModularCurve.KatzGamma0Form.instAdd ModularCurve.KatzLevelPForm.instAddCommGroup ModularCurve.KatzGamma0Form.instNeg ModularCurve.KatzGamma0Form.instAddCommGroup ModularCurve.KatzLevelPForm.instAdd ModularCurve.KatzLevelPForm.instSub ModularCurve.KatzLevelPForm.instNeg ModularCurve.KatzGamma0Form.instSMul ModularCurve.KatzGamma0Form.instSub ModularCurve.KatzLevelPForm.instZero ModularCurve.KatzLevelPForm.instModule KatzModularForm.instAddCommGroup KatzModularForm.instSub KatzModularForm.instZero KatzModularForm.instModule KatzModularForm.instAdd KatzModularForm.instNeg KatzModularForm.instSMul WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite

attribute [-instance] WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4

set_option autoImplicit false

p2m_open

open scoped MatrixGroups

attribute [local instance] ModularCurve.instDecidableEqResidueFieldSemistable
  ModularCurve.instAlgebraResidueFieldModularFunctionFieldCSemistable

set_option maxHeartbeats 3200000 in
set_option synthInstance.maxHeartbeats 1600000 in

theorem KSharpPin3.mem_comap_iotaSharp_iff_of_mem_adjoin
    (q : ℕ) [Fact q.Prime] (M' : ℕ) [NeZero M']
    (A : ValuationSubring (AlgebraicClosure ℚ))
    [Algebra ↥A ↥(laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ (Gamma0 M')))] [Algebra ↥A ↥(fieldBar q M')]
    (halgK : ∀ a : ↥A, algebraMap ↥A ↥(laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ (Gamma0 M'))) a =
      algebraMap (AlgebraicClosure ℚ) ↥(laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ (Gamma0 M'))) (a : AlgebraicClosure ℚ))
    (halgF : ∀ a : ↥A, algebraMap ↥A ↥(fieldBar q M') a =
      algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M') (a : AlgebraicClosure ℚ))
    (R : RegularProlongation A ↥(laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ (Gamma0 M'))) ↥(qExpFunctionFieldC (ResidueField ↥A) (Gamma0 M')))
    (hRpin : ∀ (y : LaurentSeries ↥A)
        (hy : coeffMap A.subtype y ∈ laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ (Gamma0 M'))),
        ∃ hO : (⟨coeffMap A.subtype y, hy⟩ : ↥(laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ (Gamma0 M')))) ∈ R.integers,
          ((R.residue ⟨_, hO⟩ : ↥(qExpFunctionFieldC (ResidueField ↥A) (Gamma0 M'))) :
              LaurentSeries (ResidueField ↥A)) = coeffMap (IsLocalRing.residue ↥A) y)
    (jb : ↥(laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ (Gamma0 M'))))
    (hPserK : ∀ P : Polynomial ↥A,
      ((Polynomial.aeval jb P : ↥(laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ (Gamma0 M')))) : LaurentSeries (AlgebraicClosure ℚ)) =
        coeffMap A.subtype (P.eval₂ (HahnSeries.C : ↥A →+* LaurentSeries ↥A) (jqModC ↥A)))
    (J' : ↥(fieldBar q M'))
    (hιalg : ∀ c : AlgebraicClosure ℚ, ModularCurve.KSharpPin.iotaSharp q M' (algebraMap (AlgebraicClosure ℚ) ↥(laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ (Gamma0 M'))) c) =
      algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M') c)
    (hιaeval : ∀ P : Polynomial ↥A, ModularCurve.KSharpPin.iotaSharp q M' (Polynomial.aeval jb P) = Polynomial.aeval J' P)
    (V : ValuationSubring ↥(fieldBar q M'))
    (hVc : ∀ c : AlgebraicClosure ℚ, algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M') c ∈ V ↔ c ∈ A)
    (hVgen : ∀ P : Polynomial ↥A, P.map (IsLocalRing.residue ↥A) ≠ 0 →
        Polynomial.aeval J' P ∈ V ∧ (Polynomial.aeval J' P)⁻¹ ∈ V)
    (e : ↥(laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ (Gamma0 M'))))
    (he : e ∈ IntermediateField.adjoin (AlgebraicClosure ℚ) ({jb} : Set ↥(laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ (Gamma0 M'))))) :
    e ∈ V.comap (ModularCurve.KSharpPin.iotaSharp q M') ↔ e ∈ R.integers := by
  classical
  have hPres : ∀ P : Polynomial ↥A, P.map (IsLocalRing.residue ↥A) ≠ 0 →
      coeffMap (IsLocalRing.residue ↥A) (P.eval₂ (HahnSeries.C : ↥A →+* LaurentSeries ↥A) (jqModC ↥A)) ≠ 0 := by
    intro P hP
    rw [ModularCurve.KSharpPin.coeffMap_residue_eval₂_C_jqModC]
    exact ModularCurve.KSharpPin.aeval_jqModC_ne_zero hP
  rw [IntermediateField.mem_adjoin_simple_iff] at he
  obtain ⟨r, s, rfl⟩ := he
  rw [ValuationSubring.mem_comap]

  by_cases hr : r = 0
  · subst hr; simp
  by_cases hs : s = 0
  · subst hs; simp
  obtain ⟨cr, P, hcr, hP, hrP⟩ := ModularCurve.KSharpPin.exists_eq_smul_map A r hr
  obtain ⟨cs, Q, hcs, hQ, hsQ⟩ := ModularCurve.KSharpPin.exists_eq_smul_map A s hs
  have hcompK : (algebraMap (AlgebraicClosure ℚ) ↥(laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ (Gamma0 M')))).comp A.subtype = algebraMap ↥A ↥(laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ (Gamma0 M'))) :=
    RingHom.ext fun a => (halgK a).symm
  have hmapaeval : ∀ P : Polynomial ↥A, Polynomial.aeval jb (P.map A.subtype) = Polynomial.aeval jb P := fun P => by
    rw [Polynomial.aeval_def, Polynomial.eval₂_map, Polynomial.aeval_def, hcompK]
  have haevr : Polynomial.aeval jb r = algebraMap (AlgebraicClosure ℚ) ↥(laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ (Gamma0 M'))) cr * Polynomial.aeval jb P := by
    rw [hrP, map_smul, Algebra.smul_def, hmapaeval]
  have haevs : Polynomial.aeval jb s = algebraMap (AlgebraicClosure ℚ) ↥(laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ (Gamma0 M'))) cs * Polynomial.aeval jb Q := by
    rw [hsQ, map_smul, Algebra.smul_def, hmapaeval]

  have hPne : (Polynomial.aeval jb P : ↥(laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ (Gamma0 M')))) ≠ 0 := by
    intro h
    apply ModularCurve.KSharpPin.coeffMap_subtype_ne_zero A (hPres P hP)
    rw [← hPserK, h]; rfl
  have hQne : (Polynomial.aeval jb Q : ↥(laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ (Gamma0 M')))) ≠ 0 := by
    intro h
    apply ModularCurve.KSharpPin.coeffMap_subtype_ne_zero A (hPres Q hQ)
    rw [← hPserK, h]; rfl
  have hcsK : algebraMap (AlgebraicClosure ℚ) ↥(laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ (Gamma0 M'))) cs ≠ 0 := by
    rw [map_ne_zero_iff _ (algebraMap (AlgebraicClosure ℚ) ↥(laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ (Gamma0 M')))).injective]; exact hcs

  set e : ↥(laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ (Gamma0 M'))) := Polynomial.aeval jb r / Polynomial.aeval jb s with he_def
  have hrel : e * Polynomial.aeval jb Q = algebraMap (AlgebraicClosure ℚ) ↥(laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ (Gamma0 M'))) (cr / cs) * Polynomial.aeval jb P := by
    rw [he_def, haevr, haevs, map_div₀]
    field_simp

  have hunitR : ∀ P : Polynomial ↥A, P.map (IsLocalRing.residue ↥A) ≠ 0 →
      Polynomial.aeval jb P ∈ R.integers ∧ (Polynomial.aeval jb P)⁻¹ ∈ R.integers := by
    intro P hP
    have hmem : coeffMap A.subtype (P.eval₂ (HahnSeries.C : ↥A →+* LaurentSeries ↥A) (jqModC ↥A)) ∈ (laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ (Gamma0 M'))) := by
      rw [← hPserK]; exact (Polynomial.aeval jb P).2
    obtain ⟨h0, hres⟩ := hRpin _ hmem
    have heq : Polynomial.aeval jb P = ⟨_, hmem⟩ := Subtype.ext (hPserK P)
    have hres_ne : R.residue ⟨⟨_, hmem⟩, h0⟩ ≠ 0 := by
      intro h
      apply hPres P hP
      rw [← hres, h]
      rfl
    have hunit : IsUnit (⟨⟨_, hmem⟩, h0⟩ : ↥R.integers) := R.isUnit_of_residue_ne_zero hres_ne
    obtain ⟨-, hzinv⟩ := (ModularCurve.KSharpPin.isUnit_iff_inv_mem _ _).mp hunit
    rw [heq]
    exact ⟨h0, hzinv⟩
  have hrelF : ModularCurve.KSharpPin.iotaSharp q M' e * Polynomial.aeval J' Q =
      algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M') (cr / cs) * Polynomial.aeval J' P := by
    rw [← hιaeval, ← hιaeval, ← hιalg, ← map_mul, ← map_mul, hrel]
  have hPne' : (Polynomial.aeval J' P : ↥(fieldBar q M')) ≠ 0 := by
    rw [← hιaeval]; exact fun h => hPne ((ModularCurve.KSharpPin.iotaSharp q M').injective (by rw [h, map_zero]))
  have hQne' : (Polynomial.aeval J' Q : ↥(fieldBar q M')) ≠ 0 := by
    rw [← hιaeval]; exact fun h => hQne ((ModularCurve.KSharpPin.iotaSharp q M').injective (by rw [h, map_zero]))
  have key1 := ModularCurve.KSharpPin.mem_iff_const_mem_of_rel A (algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) V hVc
    _ _ _ hPne' hQne' (hVgen P hP).1 (hVgen P hP).2 (hVgen Q hQ).1 (hVgen Q hQ).2 hrelF
  have key2 := ModularCurve.KSharpPin.mem_iff_const_mem_of_rel A (algebraMap (AlgebraicClosure ℚ) ↥(laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ (Gamma0 M')))) R.integers
    R.algebraMap_mem_iff _ _ _ hPne hQne (hunitR P hP).1 (hunitR P hP).2 (hunitR Q hQ).1 (hunitR Q hQ).2 hrel
  exact key1.trans key2.symm

end P2MW.S_ModularCurve_FullLevel_mem_iff_mem_igusaGaussRing_of_coe_eq_qExpand_of_forall_mem_integers_mem_of_eq_three
