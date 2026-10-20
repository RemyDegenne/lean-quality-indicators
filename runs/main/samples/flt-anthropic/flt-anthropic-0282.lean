namespace P2MW.S_AutomorphicForm_LocalWeightedOrbital_splitOrbital_eq_zero_of_not_exists_norm_eq_of_areMatchingLocal

attribute [-instance] instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instCountableOfNumberField_definitions

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicHaar IsDedekindDomain

attribute [local instance] NumberField.AdelicHaar.glBorel AutomorphicForm.centralizerBorel
  AutomorphicForm.twistedCentralizerBorel

open LanglandsTunnell.CubicInduction (diagUnits2)

open MeasureTheory NumberField IsDedekindDomain TopologicalSpace Filter

open scoped Topology NNReal ENNReal Pointwise

noncomputable section

namespace C7NonNorm

section Unfold

variable (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))

open AutomorphicForm

attribute [local instance] t2Space_GL secondCountableTopology_GL locallyCompactSpace_localGL
  AutomorphicForm.localGLBorel AutomorphicForm.borelSpace_localGLBorel AutomorphicForm.isHaarMeasure_localHaar

variable [MeasurableSpace (v.adicCompletion K)] [BorelSpace (v.adicCompletion K)]

theorem unfold_unipotent_integral (ν : Measure (v.adicCompletion K)) [ν.IsAddHaarMeasure] {C B : ℝ}
    (Φ : GL (Fin 2) (v.adicCompletion K) → ℂ) (hΦm : Measurable Φ) (hΦb : ∀ x, ‖Φ x‖ ≤ B)
    (hΦs : ∀ x, Φ x ≠ 0 → x ∈ unipKSet K v C) :
    ((ν.real (Metric.closedBall (0 : v.adicCompletion K) 1) : ℝ) : ℂ) * ∫ x, Φ x ∂(localHaar K v) =
      ∫ y, ∫ k, (localIntegralSet K v).indicator (fun _ => (1 : ℂ)) k * Φ (unipotentGL2 y * k)
        ∂(localHaar K v) ∂ν := by

  have hpt : ∀ x, ((ν.real (Metric.closedBall (0 : v.adicCompletion K) 1) : ℝ) : ℂ) * Φ x =
      ∫ y, Φ x * (localIntegralSet K v).indicator (fun _ => (1 : ℂ)) (unipotentGL2 (-y) * x) ∂ν := by
    intro x
    rw [integral_const_mul]
    have hind : (fun y => (localIntegralSet K v).indicator (fun _ => (1 : ℂ)) (unipotentGL2 (-y) * x)) =
        {y : v.adicCompletion K | unipotentGL2 (-y) * x ∈ localIntegralSet K v}.indicator (fun _ => (1 : ℂ)) := by
      ext y
      by_cases h : unipotentGL2 (-y) * x ∈ localIntegralSet K v
      · rw [Set.indicator_of_mem h, Set.indicator_of_mem (by exact h)]
      · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem (by exact h)]
    rw [hind, integral_indicator_const _ (measurableSet_setOf_unipotent_neg_mul_mem K v x), Complex.real_smul,
      mul_one]
    by_cases hx : Φ x = 0
    · rw [hx, zero_mul, mul_zero]
    · rw [mul_comm, measureReal_def, measureReal_def, measure_setOf_unipotent_neg_mul_mem K v ν (hΦs x hx)]

  have hInt : Integrable (Function.uncurry fun (x : GL (Fin 2) (v.adicCompletion K)) (y : v.adicCompletion K) =>
      Φ x * (localIntegralSet K v).indicator (fun _ => (1 : ℂ)) (unipotentGL2 (-y) * x)) ((localHaar K v).prod ν) := by
    have hcont : Continuous fun p : GL (Fin 2) (v.adicCompletion K) × v.adicCompletion K => unipotentGL2 (-p.2) * p.1 :=
      ((continuous_unipotentGL2' K v).comp continuous_snd.neg).mul continuous_fst
    refine integrable_of_bounded_of_support_subset
      ((hΦm.comp measurable_fst).mul ((measurable_const.indicator (measurableSet_localIntegralSet K v)).comp
        hcont.measurable)) (B := B) (fun p => ?_)
      (S := unipKSet K v C ×ˢ Metric.closedBall (0 : v.adicCompletion K) (max C 1)) ?_ ?_
    · change ‖Φ p.1 * (localIntegralSet K v).indicator (fun _ => (1 : ℂ)) (unipotentGL2 (-p.2) * p.1)‖ ≤ B
      rw [norm_mul]
      refine (mul_le_of_le_one_right (norm_nonneg _) ?_).trans (hΦb p.1)
      by_cases h : unipotentGL2 (-p.2) * p.1 ∈ localIntegralSet K v
      · rw [Set.indicator_of_mem h, norm_one]
      · rw [Set.indicator_of_notMem h, norm_zero]; exact zero_le_one
    · rw [Measure.prod_prod]
      exact (ENNReal.mul_lt_top ((isCompact_unipKSet K v C).measure_lt_top)
        ((isCompact_closedBall _ _).measure_lt_top)).ne
    · intro p hp
      rw [Function.mem_support, Function.uncurry_apply_pair] at hp
      have h1 : Φ p.1 ≠ 0 := left_ne_zero_of_mul hp
      have h2 : unipotentGL2 (-p.2) * p.1 ∈ localIntegralSet K v := by
        by_contra h
        exact (right_ne_zero_of_mul hp) (Set.indicator_of_notMem h _)
      refine ⟨hΦs _ h1, ?_⟩
      simp only [Metric.mem_closedBall, dist_zero_right]
      exact norm_le_of_unipotent_neg_mul_mem K v (hΦs _ h1) h2
  calc ((ν.real (Metric.closedBall (0 : v.adicCompletion K) 1) : ℝ) : ℂ) * ∫ x, Φ x ∂(localHaar K v)
      = ∫ x, ((ν.real (Metric.closedBall (0 : v.adicCompletion K) 1) : ℝ) : ℂ) * Φ x ∂(localHaar K v) :=
        (integral_const_mul _ _).symm
    _ = ∫ x, ∫ y, Φ x * (localIntegralSet K v).indicator (fun _ => (1 : ℂ)) (unipotentGL2 (-y) * x) ∂ν
          ∂(localHaar K v) := by
        congr 1 with x; exact hpt x
    _ = ∫ y, ∫ x, Φ x * (localIntegralSet K v).indicator (fun _ => (1 : ℂ)) (unipotentGL2 (-y) * x)
          ∂(localHaar K v) ∂ν := integral_integral_swap hInt
    _ = ∫ y, ∫ k, Φ (unipotentGL2 y * k) *
          (localIntegralSet K v).indicator (fun _ => (1 : ℂ)) (unipotentGL2 (-y) * (unipotentGL2 y * k))
          ∂(localHaar K v) ∂ν := by
        congr 1 with y
        exact (integral_mul_left_eq_self _ (unipotentGL2 y)).symm
    _ = ∫ y, ∫ k, (localIntegralSet K v).indicator (fun _ => (1 : ℂ)) k * Φ (unipotentGL2 y * k)
          ∂(localHaar K v) ∂ν := by
        congr 1 with y; congr 1 with k
        rw [← mul_assoc, ← unipotentGL2_add, neg_add_cancel, unipotentGL2_zero, one_mul, mul_comm]

end Unfold
end C7NonNorm
end
end P2MW.S_AutomorphicForm_LocalWeightedOrbital_splitOrbital_eq_zero_of_not_exists_norm_eq_of_areMatchingLocal
