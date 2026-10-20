namespace P2MW.S_LanglandsTunnell_RankinSelberg_measurable_remainder_and_dualFactor_translate_mul_prod_eq_of_pureTensor_expansion

attribute [-instance] instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instCountableOfNumberField_definitions

set_option autoImplicit false

set_option linter.unusedVariables false

set_option linter.unusedSectionVars false

open IsDedekindDomain NumberField AutomorphicForm LanglandsTunnell LanglandsTunnell.Converse

open NumberField.TateGlobal NumberField.AdelicLevel NumberField.AdelicBox NumberField.InfinitePlace.Completion

open LanglandsTunnell.RankinSelberg LanglandsTunnell.CubicInduction MeasureTheory UnramifiedWhittaker AdelicDock

open LanglandsTunnell.TateLocal NumberField.StandardAddChar Topology

open scoped nonZeroDivisors NNReal ENNReal Matrix Pointwise

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel

noncomputable section

p2m_reactivate

open KcRsCellRem in
open LanglandsTunnell.TateLocal UnramifiedWhittaker in
theorem solution
    (K : Type) [Field K] [NumberField K]
    [Algebra (𝓞 ℚ) (𝓞 K)] [Algebra.IsIntegral (𝓞 ℚ) (𝓞 K)]
    (pins : CarrierPins ℚ) (ψ : AddChar (AdeleRing (𝓞 ℚ) ℚ) ℂ) (hψQ : ψ⁻¹ = NumberField.StandardAddChar.psiQ)
    (μ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (F : CubicInductionForm K pins ψ μ)
    (SQ : Finset (HeightOneSpectrum (𝓞 ℚ))) (hμf : finiteAdelicGL2Subgroup ℚ)
    (m : ℕ) (w : ∀ p : ↥SQ, Fin m → GL (Fin 2) ((p : HeightOneSpectrum (𝓞 ℚ)).adicCompletion ℚ) → ℂ)
    (_hwlaw : ∀ (p : ↥SQ) (α : Fin m) (x : (p : HeightOneSpectrum (𝓞 ℚ)).adicCompletion ℚ) (g : GL (Fin 2) ((p : HeightOneSpectrum (𝓞 ℚ)).adicCompletion ℚ)),
      w p α (UnramifiedWhittaker.unipotent x * g) = NumberField.StandardAddChar.psiLocal ℚ (p : HeightOneSpectrum (𝓞 ℚ)) x * w p α g)
    (Wrem : Fin m → AdelicGL2 (𝓞 ℚ) ℚ → ℂ)
    (_hWinv : ∀ (α : Fin m) (p : ↥SQ) (x : GL (Fin 2) ((p : HeightOneSpectrum (𝓞 ℚ)).adicCompletion ℚ)) (g : AdelicGL2 (𝓞 ℚ) ℚ),
      Wrem α (g * UnramifiedWhittaker.placeEmbed ℚ (p : HeightOneSpectrum (𝓞 ℚ)) x) = Wrem α g)
    (_hWlaw : ∀ (α : Fin m) (t : AdeleRing (𝓞 ℚ) ℚ), t.1 = 0 →
      (∀ p : ↥SQ, localAt ℚ (p : HeightOneSpectrum (𝓞 ℚ)) (unipotentGL2 t) = 1) →
      ∀ g : AdelicGL2 (𝓞 ℚ) ℚ, Wrem α (unipotentGL2 t * g) = NumberField.StandardAddChar.psiQ t * Wrem α g)
    (_hwmeas : ∀ (p : ↥SQ) (α : Fin m), Measurable (fun g : finiteAdelicGL2Subgroup ℚ =>
      w p α (localAt ℚ (p : HeightOneSpectrum (𝓞 ℚ)) (g : AdelicGL2 (𝓞 ℚ) ℚ))))
    (_hWmeas : ∀ α : Fin m, Measurable (fun g : finiteAdelicGL2Subgroup ℚ => Wrem α (g : AdelicGL2 (𝓞 ℚ) ℚ)))
    (Wf Wfd : finiteAdelicGL2Subgroup ℚ → ℂ)
    (w₀ : GL (Fin 2) ℚ) (hw₀ : (w₀ : Matrix (Fin 2) (Fin 2) ℚ) = !![0, 1; 1, 0])
    (hWfd : ∀ gf : finiteAdelicGL2Subgroup ℚ, Wfd gf =
      ((NumberField.TateGlobal.ideleNorm ℚ (Matrix.GeneralLinearGroup.det (gf : AdelicGL2 (𝓞 ℚ) ℚ)) : ℝ) : ℂ) *
        Wf (RSCarrier.finFactor (globalPoints (𝓞 ℚ) ℚ w₀ * transposeInvN (Fin 2) (gf : AdelicGL2 (𝓞 ℚ) ℚ))))
    (_hsplit : ∀ g : AdelicGL2 (𝓞 ℚ) ℚ,
      Wf (RSCarrier.finFactor g) = ∑ α : Fin m, (∏ p : ↥SQ, w p α (localAt ℚ (p : HeightOneSpectrum (𝓞 ℚ)) g)) * Wrem α g)
    (R : Fin m → AdelicGL2 (𝓞 ℚ) ℚ → ℂ)
    (_hRinv : ∀ (α : Fin m) (p : ↥SQ) (x : GL (Fin 2) ((p : HeightOneSpectrum (𝓞 ℚ)).adicCompletion ℚ)) (g : AdelicGL2 (𝓞 ℚ) ℚ),
      R α (g * UnramifiedWhittaker.placeEmbed ℚ (p : HeightOneSpectrum (𝓞 ℚ)) x) = R α g)
    (_hRexp : ∀ g : finiteAdelicGL2Subgroup ℚ, Wfd (RSCarrier.finFactor (g : AdelicGL2 (𝓞 ℚ) ℚ) * hμf) =
      ∑ α : Fin m, (∏ p : ↥SQ,
        ((LanglandsTunnell.TateLocal.modulus ((Matrix.GeneralLinearGroup.det (localAt ℚ (p : HeightOneSpectrum (𝓞 ℚ)) (g : AdelicGL2 (𝓞 ℚ) ℚ)) : ((p : HeightOneSpectrum (𝓞 ℚ)).adicCompletion ℚ)ˣ) : (p : HeightOneSpectrum (𝓞 ℚ)).adicCompletion ℚ) : ℝ) : ℂ) *
          w p α (localAt ℚ (p : HeightOneSpectrum (𝓞 ℚ)) (globalPoints (𝓞 ℚ) ℚ w₀) *
            transposeInvN (Fin 2) (localAt ℚ (p : HeightOneSpectrum (𝓞 ℚ)) (g : AdelicGL2 (𝓞 ℚ) ℚ)))) * R α (g : AdelicGL2 (𝓞 ℚ) ℚ))
    (yy : Fin m → ∀ p : ↥SQ, GL (Fin 2) ((p : HeightOneSpectrum (𝓞 ℚ)).adicCompletion ℚ)) (k₀ : ∀ p : ↥SQ, LocalGL3 (p : HeightOneSpectrum (𝓞 ℚ)))
    (U : ∀ p : ↥SQ, Subgroup (GL (Fin 2) ((p : HeightOneSpectrum (𝓞 ℚ)).adicCompletion ℚ)))
    (hU1 : (∀ (p : ↥SQ), ∀ u ∈ U p, ∀ (β : Fin m) (i : Fin m),
        w p β (localAt ℚ (p : HeightOneSpectrum (𝓞 ℚ)) (globalPoints (𝓞 ℚ) ℚ w₀) * transposeInvN (Fin 2) (u * yy i p)) =
          w p β (localAt ℚ (p : HeightOneSpectrum (𝓞 ℚ)) (globalPoints (𝓞 ℚ) ℚ w₀) * transposeInvN (Fin 2) (yy i p))))
    (hU2 : (∀ (p : ↥SQ), ∀ u ∈ U p,
        F.whittakerLoc (p : HeightOneSpectrum (𝓞 ℚ)) (longWeyl3 * transposeInv3 (iotaGL u) * k₀ p) =
          F.whittakerLoc (p : HeightOneSpectrum (𝓞 ℚ)) (longWeyl3 * k₀ p)))
    (hc₀ : (∀ p : ↥SQ, F.whittakerLoc (p : HeightOneSpectrum (𝓞 ℚ)) (longWeyl3 * k₀ p) ≠ 0))
    (hM : ((Matrix.of fun i j : Fin m => ∏ p : ↥SQ,
        w p j (localAt ℚ (p : HeightOneSpectrum (𝓞 ℚ)) (globalPoints (𝓞 ℚ) ℚ w₀) * transposeInvN (Fin 2) (yy i p))).det ≠ 0)) :
    Measurable Wfd ∧
    (∀ n : ↥RSCarrier.finUnipotent, ∃ θ : ℂ, ‖θ‖ = 1 ∧ ∀ g : finiteAdelicGL2Subgroup ℚ,
      Wfd ((n : finiteAdelicGL2Subgroup ℚ) * g) = θ * Wfd g) ∧
    (∀ α : Fin m, Measurable fun g : finiteAdelicGL2Subgroup ℚ => R α (g : AdelicGL2 (𝓞 ℚ) ℚ)) ∧
    (∀ (α : Fin m) (n : ↥RSCarrier.finUnipotent) (g : finiteAdelicGL2Subgroup ℚ),
      ‖R α (((n : finiteAdelicGL2Subgroup ℚ) * g : finiteAdelicGL2Subgroup ℚ) : AdelicGL2 (𝓞 ℚ) ℚ)‖ =
        ‖R α (g : AdelicGL2 (𝓞 ℚ) ℚ)‖) ∧
    (∀ (g yhat : finiteAdelicGL2Subgroup ℚ) (i : Fin m),
      (∀ p : ↥SQ, ∃ n ∈ (AutomorphicForm.unipotentGL2Hom (R := (p : HeightOneSpectrum (𝓞 ℚ)).adicCompletion ℚ)).range,
        ∃ u ∈ U p, n * u = localAt ℚ (p : HeightOneSpectrum (𝓞 ℚ)) (g : AdelicGL2 (𝓞 ℚ) ℚ)) →
      (∀ p : ↥SQ, localAt ℚ (p : HeightOneSpectrum (𝓞 ℚ)) (yhat : AdelicGL2 (𝓞 ℚ) ℚ) = yy i p) →
      (∀ v : HeightOneSpectrum (𝓞 ℚ), v ∉ SQ → localAt ℚ v (yhat : AdelicGL2 (𝓞 ℚ) ℚ) = 1) →
      Wfd (g * yhat * hμf) *
          (∏ p : ↥SQ, F.whittakerLoc (p : HeightOneSpectrum (𝓞 ℚ))
            (longWeyl3 * transposeInv3 (iotaGL (localAt ℚ (p : HeightOneSpectrum (𝓞 ℚ)) ((g * yhat : finiteAdelicGL2Subgroup ℚ) : AdelicGL2 (𝓞 ℚ) ℚ))) *
              ((transposeInv3 (iotaGL (yy i p)))⁻¹ * k₀ p))) =
        (∏ p : ↥SQ, F.whittakerLoc (p : HeightOneSpectrum (𝓞 ℚ)) (longWeyl3 * k₀ p) *
            ((LanglandsTunnell.TateLocal.modulus ((Matrix.GeneralLinearGroup.det (localAt ℚ (p : HeightOneSpectrum (𝓞 ℚ)) (g : AdelicGL2 (𝓞 ℚ) ℚ)) : ((p : HeightOneSpectrum (𝓞 ℚ)).adicCompletion ℚ)ˣ) : (p : HeightOneSpectrum (𝓞 ℚ)).adicCompletion ℚ) : ℝ) : ℂ) *
            ((LanglandsTunnell.TateLocal.modulus ((Matrix.GeneralLinearGroup.det (yy i p) : ((p : HeightOneSpectrum (𝓞 ℚ)).adicCompletion ℚ)ˣ) : (p : HeightOneSpectrum (𝓞 ℚ)).adicCompletion ℚ) : ℝ) : ℂ)) *
          ∑ β : Fin m, (∏ p : ↥SQ, w p β (localAt ℚ (p : HeightOneSpectrum (𝓞 ℚ)) (globalPoints (𝓞 ℚ) ℚ w₀) *
            transposeInvN (Fin 2) (yy i p))) * R β (g : AdelicGL2 (𝓞 ℚ) ℚ)) := by
  refine ⟨measurable_Wfd _hsplit hWfd _hwmeas _hWmeas, fun n => ?_,
    fun α => measurable_R F hψQ hw₀ hμf R _hRinv _hRexp _hwlaw yy k₀ U hU1 hU2 hc₀ hM _hsplit hWfd _hwmeas _hWmeas α,
    fun α n g => norm_R_unipotent_mul F hψQ hw₀ hμf R _hRinv _hRexp _hwlaw yy k₀ U hU1 hU2 hc₀ hM _hsplit hWfd _hWinv _hWlaw α
      (coe_finUnipotent_mem n) g, fun g yhat i hg hy1 hy2 => ?_⟩
  · obtain ⟨t, ht⟩ := eq_unipotentGL2_of_mem_adelicUnipotent (coe_finUnipotent_mem n)
    have hmem : unipotentGL2 t ∈ finiteAdelicGL2Subgroup ℚ := ht ▸ (n : finiteAdelicGL2Subgroup ℚ).2
    obtain ⟨θ, hθ, h⟩ := exists_phase_Wfd _hsplit _hwlaw _hWinv _hWlaw hw₀ hWfd t hmem
    refine ⟨θ, hθ, fun g => ?_⟩
    have hn : (n : finiteAdelicGL2Subgroup ℚ) = ⟨unipotentGL2 t, hmem⟩ := Subtype.ext ht
    rw [hn]
    exact h g
  · have hy : yhat = embS SQ (yy i) := by
      refine Subtype.ext (ext_of_glArch_localAt ?_ fun v => ?_)
      · rw [(mem_finiteAdelicGL2Subgroup_iff ℚ _).1 yhat.2, glArch_embS]
      · by_cases hv : v ∈ SQ
        · rw [hy1 ⟨v, hv⟩, localAt_embS_of_mem SQ (yy i) ⟨v, hv⟩]
        · rw [hy2 v hv, localAt_embS_of_not_mem SQ (yy i) hv]
    rw [hy]
    exact isolation_identity F hψQ hw₀ hμf R _hRinv _hRexp _hwlaw yy k₀ U hU1 hU2 g hg i

end
end P2MW.S_LanglandsTunnell_RankinSelberg_measurable_remainder_and_dualFactor_translate_mul_prod_eq_of_pureTensor_expansion
