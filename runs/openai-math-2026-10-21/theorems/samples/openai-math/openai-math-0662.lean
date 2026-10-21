namespace OAI

section

namespace Erdos3

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem PolynomialIntervalPowerBound.lattice_recurrence {j C e : ℕ}
    (hW : PolynomialIntervalPowerBound (j + 1) C e)
    (Λ : Submodule ℤ E) [DiscreteTopology Λ] [IsZLattice ℝ Λ]
    (α : E) (N : ℕ) {t R : ℝ} (ht : 0 < t) (hR : 0 ≤ R)
    (hlength : 2 * schmidtMeanDenominator C e (Module.finrank ℝ E) (normalizedLatticeGaussian Λ t 0) *
      normalizedLatticeGaussian Λ t 0 < 2 * (N : ℝ) + 1)
    (htail : 2 * schmidtMeanDenominator C e (Module.finrank ℝ E) (normalizedLatticeGaussian Λ t 0) *
      (Real.exp (-Real.pi * t * R ^ 2 / 2) * (2 : ℝ) ^ Module.finrank ℝ E *
        normalizedLatticeGaussian Λ t 0) < 1) :
    ∃ q : ℕ, 0 < q ∧ q ≤ N ∧ ∃ v ∈ Λ, ‖(q : ℝ) ^ (j + 1) • α - v‖ < R := by
  exact exists_positive_lattice_approx_of_gaussian_mean Λ α j N ht hR
    (schmidtMeanDenominator_pos C e _ (normalizedLatticeGaussian_origin_ge_one Λ ht))
    (hW.gaussian_mean_lower_bound Λ ht α N) hlength htail

end Erdos3
end
end OAI
