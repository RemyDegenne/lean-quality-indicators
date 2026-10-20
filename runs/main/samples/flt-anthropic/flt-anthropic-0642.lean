namespace P2MW.S_AutomorphicForm_exists_entire_eq_godementEisenstein_fe_norm_le_of_mem_schwartzBruhat2

attribute [-instance] instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions instCountableOfNumberField_definitions FixedPoints.instMulActionElemFixedPointsOfSMulCommClass_definitions FixedPoints.module FixedPoints.instSMulElemFixedPointsOfSMulCommClass_definitions FixedPoints.instAddCommMonoidElemFixedPoints_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions Submodule.instIsTopologicalModuleSubtypeMem Pi.instTopologicalModule IsTopologicalModule.toContinuousSMul IsTopologicalModule.toContinuousAdd instMeasurableSpaceRestrictedProduct_definitions instBorelSpaceRestrictedProduct_definitions MeasureTheory.instMeasurableNegSubtypeMemAddSubgroup_definitions MeasureTheory.instMeasurableMulSubtypeMemSubgroup_definitions MeasureTheory.instMeasurableMul₂SubtypeMemSubgroup_definitions MeasureTheory.instMeasurableMul₂SubtypeMemAddSubgroup_definitions MeasureTheory.instMeasurableAddSubtypeMemAddSubgroup_definitions MeasureTheory.instMeasurableInvSubtypeMemSubgroup_definitions AutomorphicForm.compactSpace_maximalCompactAway AutomorphicForm.compactSpace_adelicMaximalCompact AutomorphicForm.isProbabilityMeasure_maximalCompactHaar AutomorphicForm.isHaarMeasure_maximalCompactHaar AutomorphicForm.compactSpace_maximalCompactAt AutomorphicForm.isProbabilityMeasure_maximalCompactAwayHaar AutomorphicForm.isHaarMeasure_maximalCompactAwayHaar AutomorphicForm.isProbabilityMeasure_maximalCompactAtHaar AutomorphicForm.isHaarMeasure_maximalCompactAtHaar

attribute [-instance] HeckePair.instSMulCommClassSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instAlgebraSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instOneSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instIsScalarTowerSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instRingSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instMulSubtypeForallMemSubmoduleHeckeAlgebra FLT.SmoothVectors.RightTranslationFn.instAddCommMonoid FLT.SmoothVectors.RightTranslationFn.instMulAction FLT.SmoothVectors.RightTranslationFn.instDistribMulAction instContinuousSMulOfDiscreteTopologyOfContinuousSMulDiscrete

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicFourier NumberField.AdelicBox NumberField.AdelicLevel

open AutomorphicForm AutomorphicForm.WindowedSiegel

open scoped NNReal

open LanglandsTunnell.RankinSelberg

open Ws1.GEAsm in

theorem solution
    (F : Type) [Field F] [NumberField F]
    [MeasurableSpace (AdeleRing (𝓞 F) F)ˣ] [BorelSpace (AdeleRing (𝓞 F) F)ˣ]
    (ν₀ : Measure (AdeleRing (𝓞 F) F)ˣ) [ν₀.IsHaarMeasure]
    [MeasurableSpace (AdeleRing (𝓞 F) F)] [BorelSpace (AdeleRing (𝓞 F) F)]
    (μ₁ : Measure (AdeleRing (𝓞 F) F)) [μ₁.IsAddHaarMeasure]
    (_hμ₁ : μ₁ (adelicBox F) = 1)
    (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ) (_hψ : IsGlobalAddChar F ψ) :
    let α : (AdeleRing (𝓞 F) F)ˣ →* ℝˣ :=
      ((NNReal.toRealHom : ℝ≥0 →+* ℝ).toMonoidHom.comp
        (distribHaarChar (AdeleRing (𝓞 F) F))).toHomUnits
    ∀ (hα : ∀ x, 0 < ((α x : ℝˣ) : ℝ))
      (_hprin : IsPrincipalTrivial (R := 𝓞 F) (K := F) α)
      (μ ν : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ)
      (_hμ : IsUnitaryChar (𝓞 F) F μ) (_hν : IsUnitaryChar (𝓞 F) F ν)
      (_hμic : IsIdeleClassChar (𝓞 F) F μ) (_hνic : IsIdeleClassChar (𝓞 F) F ν)
      (_hμc : Continuous fun x : (AdeleRing (𝓞 F) F)ˣ => ((μ x : ℂˣ) : ℂ))
      (_hνc : Continuous fun x : (AdeleRing (𝓞 F) F)ˣ => ((ν x : ℂˣ) : ℂ))
      (Φ : (Fin 2 → AdeleRing (𝓞 F) F) → ℂ) (_hΦ : Φ ∈ schwartzBruhat2 F),
    let f : ℂ → AdelicGL2 (𝓞 F) F → ℂ := fun s g => godementSection F ν₀ μ ν α hα Φ s g
    let f' : ℂ → AdelicGL2 (𝓞 F) F → ℂ := fun s g => godementSection F ν₀ ν μ α hα (reflectPair ψ μ₁ Φ) s g
    let E : ℂ → AdelicGL2 (𝓞 F) F → ℂ := fun s g =>
      f s g + ∑' ξ : F, f s (adelicWeyl (𝓞 F) F * unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) ξ) * g)
    let E' : ℂ → AdelicGL2 (𝓞 F) F → ℂ := fun s g =>
      f' s g + ∑' ξ : F, f' s (adelicWeyl (𝓞 F) F * unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) ξ) * g)
    ((∀ τ : ℝ, μ * ν⁻¹ ≠ NumberField.TateGlobal.normPowChar F τ) →
      ∃ H H' : ℂ → AdelicGL2 (𝓞 F) F → ℂ,
        (∀ g : AdelicGL2 (𝓞 F) F, Differentiable ℂ (fun s : ℂ => H s g)) ∧
        (∀ g : AdelicGL2 (𝓞 F) F, Differentiable ℂ (fun s : ℂ => H' s g)) ∧
        (Continuous fun p : ℂ × AdelicGL2 (𝓞 F) F => H p.1 p.2) ∧
        (Continuous fun p : ℂ × AdelicGL2 (𝓞 F) F => H' p.1 p.2) ∧
        (∀ s : ℂ, (1 / 2 : ℝ) < s.re → ∀ g : AdelicGL2 (𝓞 F) F,
          H s g = E s g) ∧
        (∀ s : ℂ, (1 / 2 : ℝ) < s.re → ∀ g : AdelicGL2 (𝓞 F) F,
          H' s g = E' s g) ∧
        (∀ (s : ℂ) (g : AdelicGL2 (𝓞 F) F), H s g = H' (-s) g) ∧
        (∀ (σ₁ σ₂ c u : ℝ) (t : AdelicGL2 (𝓞 F) F), 0 < c →
          ∃ (A : ℝ) (N : ℕ), ∀ s : ℂ, σ₁ ≤ s.re → s.re ≤ σ₂ →
            ∀ g ∈ integralWindowedSiegelSet F c u,
              ‖H s (g * t)‖ ≤ A * (1 + |s.im|) ^ N * (1 + archHeight F (glArch (𝓞 F) F g)) ^ N) ∧
        (∀ (σ₁ σ₂ c u : ℝ) (t : AdelicGL2 (𝓞 F) F), 0 < c →
          ∃ (A : ℝ) (N : ℕ), ∀ s : ℂ, σ₁ ≤ s.re → s.re ≤ σ₂ →
            ∀ g ∈ integralWindowedSiegelSet F c u,
              ‖H' s (g * t)‖ ≤ A * (1 + |s.im|) ^ N * (1 + archHeight F (glArch (𝓞 F) F g)) ^ N)) ∧
    (∀ τ : ℝ, μ * ν⁻¹ = NumberField.TateGlobal.normPowChar F τ →
      ∃ H H' : ℂ → AdelicGL2 (𝓞 F) F → ℂ,
        (∀ g : AdelicGL2 (𝓞 F) F, Differentiable ℂ (fun s : ℂ => H s g)) ∧
        (∀ g : AdelicGL2 (𝓞 F) F, Differentiable ℂ (fun s : ℂ => H' s g)) ∧
        (Continuous fun p : ℂ × AdelicGL2 (𝓞 F) F => H p.1 p.2) ∧
        (Continuous fun p : ℂ × AdelicGL2 (𝓞 F) F => H' p.1 p.2) ∧
        (∀ s : ℂ, (1 / 2 : ℝ) < s.re → ∀ g : AdelicGL2 (𝓞 F) F,
          H s g = (s - ((1 : ℂ) - (τ : ℂ) * Complex.I) / 2) * (s + ((1 : ℂ) + (τ : ℂ) * Complex.I) / 2) * E s g) ∧
        (∀ s : ℂ, (1 / 2 : ℝ) < s.re → ∀ g : AdelicGL2 (𝓞 F) F,
          H' s g = (s - ((1 : ℂ) + (τ : ℂ) * Complex.I) / 2) * (s + ((1 : ℂ) - (τ : ℂ) * Complex.I) / 2) * E' s g) ∧
        (∀ (s : ℂ) (g : AdelicGL2 (𝓞 F) F), H s g = H' (-s) g) ∧
        (∀ (σ₁ σ₂ c u : ℝ) (t : AdelicGL2 (𝓞 F) F), 0 < c →
          ∃ (A : ℝ) (N : ℕ), ∀ s : ℂ, σ₁ ≤ s.re → s.re ≤ σ₂ →
            ∀ g ∈ integralWindowedSiegelSet F c u,
              ‖H s (g * t)‖ ≤ A * (1 + |s.im|) ^ N * (1 + archHeight F (glArch (𝓞 F) F g)) ^ N) ∧
        (∀ (σ₁ σ₂ c u : ℝ) (t : AdelicGL2 (𝓞 F) F), 0 < c →
          ∃ (A : ℝ) (N : ℕ), ∀ s : ℂ, σ₁ ≤ s.re → s.re ≤ σ₂ →
            ∀ g ∈ integralWindowedSiegelSet F c u,
              ‖H' s (g * t)‖ ≤ A * (1 + |s.im|) ^ N * (1 + archHeight F (glArch (𝓞 F) F g)) ^ N)) := by
  intro α hα hprin μ ν hμ hν hμic hνic hμc hνc Φ hΦ f f' E E'
  obtain ⟨R, R', X, w, c₁, c₀, p₁, p₀, hRd, hR'd, hRc, hR'c, hRb, hR'b, hXc, hw, hX, hc0, hpin, hE, hE', hFE⟩ :=
    LanglandsTunnell.RankinSelberg.exists_entire_sub_polarPart_godementEisenstein_isUniformlySiegelBounded_fe_poles_of_mem_schwartzBruhat2
      F ν₀ μ₁ _hμ₁ ψ _hψ hα hprin μ ν hμ hν hμic hνic hμc hνc Φ hΦ

  have hEE : ∀ s g, E s g = godementEisenstein F ν₀ μ ν (moduleChar F) hα Φ s g := fun s g => rfl
  have hEE' : ∀ s g, E' s g = godementEisenstein F ν₀ ν μ (moduleChar F) hα (reflectPair ψ μ₁ Φ) s g :=
    fun s g => rfl

  have hX1 : ∀ g, ‖X g‖ = 1 := by
    intro g
    rw [hX g, norm_mul, hμ, norm_cpowChar_apply, hw, Real.rpow_zero, mul_one]
  have hHpos : ∀ g : AdelicGL2 (𝓞 F) F, 0 ≤ archHeight F (glArch (𝓞 F) F g) :=
    fun g => (archHeight_pos F _).le
  refine ⟨fun hne => ?_, fun τ hτ => ?_⟩
  ·
    obtain ⟨h1, h0⟩ := hc0 hne
    refine ⟨R, R', hRd, hR'd, hRc, hR'c, ?_, ?_, hFE, ?_, ?_⟩
    · intro s hs g
      rw [hEE, hE s hs g, h1, h0]; simp
    · intro s hs g
      rw [hEE', hE' s hs g, h1, h0]; simp
    · intro σ₁ σ₂ c u t hc
      obtain ⟨A, N, hA⟩ := hRb σ₁ σ₂ c u t hc
      exact ⟨max A 0, N, fun s h1 h2 g hg => strip_bound₀ A N s _ (hHpos g) _ (hA s h1 h2 g hg)⟩
    · intro σ₁ σ₂ c u t hc
      obtain ⟨A, N, hA⟩ := hR'b σ₁ σ₂ c u t hc
      exact ⟨max A 0, N, fun s h1 h2 g hg => strip_bound₀ A N s _ (hHpos g) _ (hA s h1 h2 g hg)⟩
  ·
    obtain ⟨hp1, hp0⟩ := hpin τ hτ
    set H : ℂ → AdelicGL2 (𝓞 F) F → ℂ :=
      fun s g => (s - p₁) * (s - p₀) * R s g + (c₁ * (s - p₀) + c₀ * (s - p₁)) * X g with hH
    set H' : ℂ → AdelicGL2 (𝓞 F) F → ℂ :=
      fun s g => (s - (-p₀)) * (s - (-p₁)) * R' s g + (-c₁ * (s - (-p₀)) + -c₀ * (s - (-p₁))) * X g with hH'
    have hp1re : p₁.re = 1 / 2 := by rw [hp1]; norm_num
    have hp0re : p₀.re = -(1 / 2) := by rw [hp0]; norm_num
    refine ⟨H, H', ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro g
      simp only [hH]
      exact (((differentiable_id.sub_const _).mul (differentiable_id.sub_const _)).mul (hRd g)).add
        ((((differentiable_id.sub_const _).const_mul _).add ((differentiable_id.sub_const _).const_mul _)).mul_const _)
    · intro g
      simp only [hH']
      exact (((differentiable_id.sub_const _).mul (differentiable_id.sub_const _)).mul (hR'd g)).add
        ((((differentiable_id.sub_const _).const_mul _).add ((differentiable_id.sub_const _).const_mul _)).mul_const _)
    · simp only [hH]
      have hs : Continuous fun p : ℂ × AdelicGL2 (𝓞 F) F => p.1 := continuous_fst
      exact (((hs.sub continuous_const).mul (hs.sub continuous_const)).mul hRc).add
        ((((hs.sub continuous_const).const_mul _).add ((hs.sub continuous_const).const_mul _)).mul
          (hXc.comp continuous_snd))
    · simp only [hH']
      have hs : Continuous fun p : ℂ × AdelicGL2 (𝓞 F) F => p.1 := continuous_fst
      exact (((hs.sub continuous_const).mul (hs.sub continuous_const)).mul hR'c).add
        ((((hs.sub continuous_const).const_mul _).add ((hs.sub continuous_const).const_mul _)).mul
          (hXc.comp continuous_snd))
    · intro s hs g
      have hs1 : s - p₁ ≠ 0 := by
        intro h; have := congrArg Complex.re (sub_eq_zero.mp h); rw [hp1re] at this; linarith
      have hs0 : s - p₀ ≠ 0 := by
        intro h; have := congrArg Complex.re (sub_eq_zero.mp h); rw [hp0re] at this; linarith
      have e1 : s - ((1 : ℂ) - (τ : ℂ) * Complex.I) / 2 = s - p₁ := by rw [hp1]
      have e0 : s + ((1 : ℂ) + (τ : ℂ) * Complex.I) / 2 = s - p₀ := by rw [hp0]; ring
      rw [hEE, hE s hs g, e1, e0]
      simp only [hH]
      field_simp
      all_goals ring
    · intro s hs g
      have hs1 : s + p₁ ≠ 0 := by
        intro h; have := congrArg Complex.re (eq_neg_of_add_eq_zero_left h)
        rw [Complex.neg_re, hp1re] at this; linarith
      have hs0 : s + p₀ ≠ 0 := by
        intro h; have := congrArg Complex.re (eq_neg_of_add_eq_zero_left h)
        rw [Complex.neg_re, hp0re] at this; linarith
      have e0 : s - ((1 : ℂ) + (τ : ℂ) * Complex.I) / 2 = s - -p₀ := by rw [hp0]; ring
      have e1 : s + ((1 : ℂ) - (τ : ℂ) * Complex.I) / 2 = s - -p₁ := by rw [hp1]; ring
      rw [hEE', hE' s hs g, e0, e1]
      simp only [hH', sub_neg_eq_add]
      field_simp
      all_goals ring
    · intro s g
      simp only [hH, hH', hFE s g]
      ring
    · intro σ₁ σ₂ c u t hc
      obtain ⟨A, N, hA⟩ := hRb σ₁ σ₂ c u t hc
      obtain ⟨A', hA'⟩ := strip_bound σ₁ σ₂ p₁ p₀ p₁ p₀ c₁ c₀ A N
      refine ⟨A', N + 2, fun s h1 h2 g hg => ?_⟩
      simp only [hH]
      exact hA' s h1 h2 (R s (g * t)) (X (g * t)) _ (hHpos g) (hA s h1 h2 g hg) (hX1 (g * t)).le
    · intro σ₁ σ₂ c u t hc
      obtain ⟨A, N, hA⟩ := hR'b σ₁ σ₂ c u t hc
      obtain ⟨A', hA'⟩ := strip_bound σ₁ σ₂ (-p₀) (-p₁) (-p₁) (-p₀) (-c₁) (-c₀) A N
      refine ⟨A', N + 2, fun s h1 h2 g hg => ?_⟩
      simp only [hH']
      exact hA' s h1 h2 (R' s (g * t)) (X (g * t)) _ (hHpos g) (hA s h1 h2 g hg) (hX1 (g * t)).le

end P2MW.S_AutomorphicForm_exists_entire_eq_godementEisenstein_fe_norm_le_of_mem_schwartzBruhat2
