namespace OAI

section

namespace Erdos3.VectorPolynomial

theorem exists_allocatedCommonProductRadiusLog_bound (m : ℕ) :
    ∃ a : ℕ, 2 ≤ a ∧ ∀ {p g : ℝ}, 0 ≤ p → 0 ≤ g →
      allocatedCommonProductRadiusLog m p g ≤ (p + g + a) ^ a := by
  let poly : Polynomial ℕ := allocatedCommonProductRadiusLog m Polynomial.X Polynomial.X
  obtain ⟨a, ha, hb⟩ := exists_natPolynomial_eval_budget poly
  refine ⟨a, ha, ?_⟩
  intro p g hp hg
  apply (allocatedCommonProductRadiusLog_mono m hp hg (le_add_of_nonneg_right hg)
    (le_add_of_nonneg_left hp)).trans
  simpa [poly, allocatedCommonProductRadiusLog, allocatedCommonRadiusLog,
    allocatedBufferedRadiusLog, allocatedBufferedRadiusInput, allocatedProductChartLog,
    allocatedIdealCoverPrimitiveLog, allocatedIdealCoverInputLog, allocatedSiteCoefficientLog,
    allocatedComparisonDimension, Polynomial.eval₂_pow] using hb (p + g) (add_nonneg hp hg)

end Erdos3.VectorPolynomial
end
end OAI
