namespace OAI

noncomputable section

namespace SphericalPerceptronFreeEnergy

open MeasureTheory ProbabilityTheory Set

open scoped ENNReal NNReal BigOperators

section

variable {X S : Type} [MeasurableSpace X] [MeasurableSpace S]

omit [MeasurableSpace X] in
lemma indexedTiltedProbability_lintegral (step : X×S → X) (n : ℕ) (F : Fin n → X×S → ℝ)
    (p : X×(IndexedCascadeBase n×IndexedCascadeMarks S n)) (f : IndexedLeaf n → ℝ≥0∞) :
    (∫⁻ l, f l ∂normalizedMeasure (indexedTiltedLeafMeasure step n F p.1 p.2.1 p.2.2)) =
      ∑' l, indexedTiltedProbability step n F p l*f l := by
  rw [normalizedMeasure,lintegral_smul_measure,smul_eq_mul,indexedTiltedLeafMeasure,
    withDensity_apply _ MeasurableSet.univ,Measure.restrict_univ,
    lintegral_withDensity_eq_lintegral_mul _ (measurable_of_countable _) (measurable_of_countable _),
    indexedLeafMeasure_lintegral,indexedLeafMeasure_lintegral,← ENNReal.tsum_mul_left]
  apply tsum_congr
  intro l
  change (∑' l, (indexedLeafWeight n p.2.1 l : ℝ≥0∞)*
    ENNReal.ofReal (Real.exp (indexedShiftSum step n F (p.1,p.2.2) l)))⁻¹ *
      ((indexedLeafWeight n p.2.1 l : ℝ≥0∞)*
        (ENNReal.ofReal (Real.exp (indexedShiftSum step n F (p.1,p.2.2) l))*f l)) = _
  simp only [indexedTiltedProbability,indexedTiltedTotal,indexedTiltedWeight,mul_assoc]

end
end SphericalPerceptronFreeEnergy
end
end OAI
