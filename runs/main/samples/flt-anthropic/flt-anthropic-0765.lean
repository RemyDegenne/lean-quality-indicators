namespace P2MW.S_ModularCurve_FullLevel_supersingularProlongation_ends_of_affineChart_of_eq_three

attribute [-instance] AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion

set_option autoImplicit false

set_option synthInstance.maxHeartbeats 1600000

set_option maxHeartbeats 1600000

p2m_reactivate

open AlgebraicCurve ModularCurve ModularCurve.FullLevel IsLocalRing CongruenceSubgroup

open scoped MatrixGroups

attribute [local instance] ModularCurve.instDecidableEqResidueFieldSemistable
  ModularCurve.instAlgebraResidueFieldModularFunctionFieldCSemistable

theorem solution
    (q : ℕ) [Fact q.Prime] (hq3 : q = 3) (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M')
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime q)
    (W : Finset (Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')))
    (hW : ∀ w, w ∈ W ↔ w ∈ ssPlaces q M' (ResidueField A))
    (hle : modularFunctionFieldBar M' ≤ fieldBar q M')
    (s : ↥W)
    (k₀ : IntermediateField ℚ (AlgebraicClosure ℚ))
    (Kb : IntermediateField ↥k₀ (AlgebraicClosure ℚ)) (Ab : ValuationSubring ↥Kb) (hAb : ∀ x : ↥Kb, x ∈ Ab ↔ (x : (AlgebraicClosure ℚ)) ∈ A) (ϖb : ↥Ab)
    (inst : Algebra (GaloisField q 2) (ResidueField ↥A)) (hdomC : IsDomain (DrinfeldCurve.CoordRing q (ResidueField ↥A)))
    (B : Subring ↥(fieldBar q M')) (alg : Algebra ↥Ab ↥B)
    (hM5b : (∀ (ζ : Idx q) (γ : SL(2, ℤ)), γ ∈ Gamma0 M' → ∀ f : ↥(fieldBar q M'), f ∈ B → levelAutBar q M' ζ γ f ∈ B))
    (FSS : Type) [Field FSS] [Algebra (ResidueField ↥A) FSS] (R : RegularProlongation A ↥(fieldBar q M') FSS)
    (hBR : ∀ f : ↥(fieldBar q M'), f ∈ B → f ∈ R.integers)
    (Cs : Subgroup (rootsOfUnity (q + 1) (GaloisField q 2)))
    (ρ : ↥B →+* ↥(DrinfeldCurve.quotField q (ResidueField ↥A) Cs))
    (hρrange : ∀ z : ↥(DrinfeldCurve.quotField q (ResidueField ↥A) Cs), z ∈ Set.range ρ ↔
      (z : DrinfeldCurve.drinfeldFunctionField q (ResidueField ↥A)) ∈ Set.range (algebraMap (DrinfeldCurve.CoordRing q (ResidueField ↥A)) (DrinfeldCurve.drinfeldFunctionField q (ResidueField ↥A))))
    (e : FSS ≃ₐ[(ResidueField ↥A)] ↥(DrinfeldCurve.quotField q (ResidueField ↥A) Cs)) (he : ∀ b : ↥B, e (R.residue ⟨((b : ↥B) : ↥(fieldBar q M')), hBR _ (b).2⟩) = ρ b) :
    ∃ N : Finset (Place (ResidueField ↥A) FSS),
      N.card = q + 1 ∧
      (∀ Q : Place (ResidueField ↥A) FSS, Q ∉ N ↔ ∀ b : ↥B, R.residue ⟨((b : ↥B) : ↥(fieldBar q M')), hBR _ (b).2⟩ ∈ Q.toValuationSubring) ∧
      (∀ τ ∈ Subgroup.closure {τ : ↥(fieldBar q M') ≃ₐ[AlgebraicClosure ℚ] ↥(fieldBar q M') |
          ∃ (ζ : Idx q) (γ : SL(2, ℤ)), γ ∈ Gamma0 M' ∧ τ = levelAutBar q M' ζ γ},
        ∀ (hτ : ∀ f : ↥(fieldBar q M'), τ f ∈ R.integers ↔ f ∈ R.integers) (Q : Place (ResidueField ↥A) FSS),
          (R.resAut τ hτ • Q ∈ N ↔ Q ∈ N)) := by
  classical
  haveI hκ : IsAlgClosed (ResidueField ↥A) := ValuationSubring.isAlgClosed_residueField_algebraicClosure_rat A

  obtain ⟨N', hN'card, hN'iff⟩ := B3Ends.exists_finset q (ResidueField ↥A) Cs

  let eR : FSS ≃+* ↥(DrinfeldCurve.quotField q (ResidueField ↥A) Cs) := e.toRingEquiv
  have heR : ∀ a : ResidueField ↥A, eR (algebraMap (ResidueField ↥A) FSS a) =
      algebraMap (ResidueField ↥A) ↥(DrinfeldCurve.quotField q (ResidueField ↥A) Cs) a := fun a => e.commutes a
  let Φ := AlgebraicCurve.Place.congrEquiv eR heR
  have memΦ : ∀ (Q : Place (ResidueField ↥A) FSS) (z : ↥(DrinfeldCurve.quotField q (ResidueField ↥A) Cs)),
      z ∈ (Φ Q).toValuationSubring ↔ e.symm z ∈ Q.toValuationSubring := fun Q z => by
    change z ∈ (AlgebraicCurve.Place.congrRingEquiv eR heR Q).toValuationSubring ↔ _
    rw [AlgebraicCurve.Place.congrRingEquiv_toValuationSubring, ValuationSubring.mem_comap]
    rfl
  refine ⟨N'.map Φ.symm.toEmbedding, by rw [Finset.card_map, hN'card], ?_⟩
  have memN : ∀ Q : Place (ResidueField ↥A) FSS, Q ∈ N'.map Φ.symm.toEmbedding ↔ Φ Q ∈ N' := fun Q => by
    rw [Finset.mem_map_equiv, Equiv.symm_symm]

  have iffQ : ∀ Q : Place (ResidueField ↥A) FSS, Q ∉ N'.map Φ.symm.toEmbedding ↔
      ∀ b : ↥B, R.residue ⟨((b : ↥B) : ↥(fieldBar q M')), hBR _ (b).2⟩ ∈ Q.toValuationSubring := by
    intro Q
    rw [memN, hN'iff]
    constructor
    · intro hP b
      have hr : ((ρ b : ↥(DrinfeldCurve.quotField q (ResidueField ↥A) Cs)) :
          DrinfeldCurve.drinfeldFunctionField q (ResidueField ↥A)) ∈
          Set.range (algebraMap (DrinfeldCurve.CoordRing q (ResidueField ↥A))
            (DrinfeldCurve.drinfeldFunctionField q (ResidueField ↥A))) := (hρrange (ρ b)).mp ⟨b, rfl⟩
      have h1 := (memΦ Q (ρ b)).mp (hP (ρ b) hr)
      rwa [← he b, AlgEquiv.symm_apply_apply] at h1
    · intro hB z hz
      obtain ⟨b, rfl⟩ := (hρrange z).mpr hz
      rw [memΦ, ← he b, AlgEquiv.symm_apply_apply]
      exact hB b
  refine ⟨iffQ, ?_⟩

  intro τ hτmem

  have stab : (∀ f : ↥(fieldBar q M'), f ∈ B → τ f ∈ B) ∧ (∀ f : ↥(fieldBar q M'), f ∈ B → τ⁻¹ f ∈ B) := by
    induction hτmem using Subgroup.closure_induction with
    | mem σ hσ =>
      obtain ⟨ζ', γ, hγ, rfl⟩ := hσ
      refine ⟨hM5b ζ' γ hγ, ?_⟩
      have hγ' : γ⁻¹ ∈ Gamma0 M' := inv_mem hγ
      have h11 := ModularCurve.FullLevel.levelAutBar_mul q M' hqM' ζ' 1 1 (one_mem _) (one_mem _)
      rw [mul_one] at h11
      have hone : ∀ x : ↥(fieldBar q M'), levelAutBar q M' ζ' 1 x = x := by
        intro x
        have h2 := congrArg (fun σ : ↥(fieldBar q M') ≃ₐ[AlgebraicClosure ℚ] ↥(fieldBar q M') =>
          σ ((levelAutBar q M' ζ' 1).symm x)) h11
        simp only [AlgEquiv.trans_apply, AlgEquiv.apply_symm_apply] at h2
        exact h2.symm
      have hmul := ModularCurve.FullLevel.levelAutBar_mul q M' hqM' ζ' γ γ⁻¹ hγ hγ'
      rw [mul_inv_cancel] at hmul
      have hkey : ∀ x : ↥(fieldBar q M'), levelAutBar q M' ζ' γ⁻¹ (levelAutBar q M' ζ' γ x) = x := by
        intro x
        have h3 := congrArg (fun σ : ↥(fieldBar q M') ≃ₐ[AlgebraicClosure ℚ] ↥(fieldBar q M') => σ x) hmul
        simp only [AlgEquiv.trans_apply] at h3
        rw [← h3]
        exact hone x
      intro f hf
      have h4 : (levelAutBar q M' ζ' γ)⁻¹ f = levelAutBar q M' ζ' γ⁻¹ f := by
        rw [AlgEquiv.aut_inv]
        conv_rhs => rw [← (levelAutBar q M' ζ' γ).apply_symm_apply f]
        exact (hkey _).symm
      rw [h4]
      exact hM5b ζ' γ⁻¹ hγ' f hf
    | one =>
      exact ⟨fun f hf => by rw [AlgEquiv.one_apply]; exact hf,
        fun f hf => by rw [inv_one, AlgEquiv.one_apply]; exact hf⟩
    | mul σ σ' _ _ h h' =>
      exact ⟨fun f hf => by rw [AlgEquiv.mul_apply]; exact h.1 _ (h'.1 f hf),
        fun f hf => by rw [mul_inv_rev, AlgEquiv.mul_apply]; exact h'.2 _ (h.2 f hf)⟩
    | inv σ _ h =>
      exact ⟨fun f hf => h.2 f hf, fun f hf => by rw [inv_inv]; exact h.1 f hf⟩
  intro hτ Q
  have stab2 : ∀ f : ↥(fieldBar q M'), f ∈ B → τ.symm f ∈ B := fun f hf => by
    rw [← AlgEquiv.aut_inv]; exact stab.2 f hf

  have hres : ∀ b : ↥B, (R.resAut τ hτ).symm (R.residue ⟨((b : ↥B) : ↥(fieldBar q M')), hBR _ (b).2⟩) =
      R.residue ⟨τ.symm ((b : ↥B) : ↥(fieldBar q M')), hBR _ (stab2 _ b.2)⟩ := by
    intro b
    rw [AlgEquiv.symm_apply_eq, AlgebraicCurve.RegularProlongation.resAut_residue]
    congr 1
    apply Subtype.ext
    exact (τ.apply_symm_apply _).symm
  suffices key : R.resAut τ hτ • Q ∉ N'.map Φ.symm.toEmbedding ↔ Q ∉ N'.map Φ.symm.toEmbedding from
    not_iff_not.mp key
  rw [iffQ, iffQ]
  constructor
  · intro h b
    have hb' := h ⟨τ ((b : ↥B) : ↥(fieldBar q M')), stab.1 _ b.2⟩
    rw [AlgebraicCurve.Place.smul_toValuationSubring, ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem,
      AlgEquiv.smul_def, AlgEquiv.aut_inv, hres] at hb'
    have e1 : (⟨((b : ↥B) : ↥(fieldBar q M')), hBR _ (b).2⟩ : ↥R.integers) =
        ⟨τ.symm (((⟨τ ((b : ↥B) : ↥(fieldBar q M')), stab.1 _ b.2⟩ : ↥B) : ↥(fieldBar q M'))),
          hBR _ (stab2 _ (stab.1 _ b.2))⟩ :=
      Subtype.ext (show ((b : ↥B) : ↥(fieldBar q M')) = τ.symm (τ ((b : ↥B) : ↥(fieldBar q M'))) from
        (τ.symm_apply_apply _).symm)
    rw [e1]
    exact hb'
  · intro h b
    rw [AlgebraicCurve.Place.smul_toValuationSubring, ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem,
      AlgEquiv.smul_def, AlgEquiv.aut_inv, hres]
    exact h ⟨τ.symm ((b : ↥B) : ↥(fieldBar q M')), stab2 _ b.2⟩

end P2MW.S_ModularCurve_FullLevel_supersingularProlongation_ends_of_affineChart_of_eq_three
