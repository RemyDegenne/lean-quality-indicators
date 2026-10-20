public section

noncomputable section

namespace TauCeti

open Function MeasureTheory Metric Set Module TopologicalSpace

open scoped Distributions ENNReal NNReal Nat

section CompactSupport

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [Nontrivial E] [MeasurableSpace E] [BorelSpace E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  {μ : Measure E} [μ.IsAddHaarMeasure] {u : E → F} {Ω : Set E}

theorem eLpNorm_le_mul_measure_rpow_mul_eLpNorm_fderiv (hu : ContDiff ℝ 1 u)
    (h2u : HasCompactSupport u) (hΩ : MeasurableSet Ω) (hsupp : tsupport u ⊆ Ω) {q : ℝ≥0}
    (hq : (finrank ℝ E : ℝ≥0) ≤ q) :
    eLpNorm u q μ ≤
      ENNReal.ofReal ((finrank ℝ E : ℝ)⁻¹ * μ.real (ball 0 1) ^ (-(finrank ℝ E : ℝ)⁻¹) *
        (q * (1 - (finrank ℝ E : ℝ)⁻¹) + 1) ^ (1 - (finrank ℝ E : ℝ)⁻¹ + (q : ℝ)⁻¹)) *
        μ Ω ^ (q : ℝ)⁻¹ * eLpNorm (fderiv ℝ u) (finrank ℝ E) μ := by
  set n := finrank ℝ E
  have hn0 : (n : ℝ) ≠ 0 := by have : 0 < n := finrank_pos; positivity
  have hq0 : (0 : ℝ) < q := lt_of_lt_of_le (by have : 0 < n := finrank_pos; positivity)
    (by exact_mod_cast hq : (n : ℝ) ≤ q)
  have h := eLpNorm_le_mul_measure_rpow_mul_eLpNorm_fderiv_of_lt (μ := μ) hu h2u hΩ hsupp
    (p := n) (by exact_mod_cast finrank_pos) hq (δ := (n : ℝ)⁻¹ - (q : ℝ)⁻¹) (by simp)
    (by linarith [inv_pos.2 hq0])
  -- At `p = n`, `δ = 1/n - 1/q`, so `1/n - δ = 1/q` and `(1 - δ) / (1/n - δ) = q (1 - 1/n) + 1`.
  have hbase : (1 - ((n : ℝ)⁻¹ - (q : ℝ)⁻¹)) / ((n : ℝ)⁻¹ - ((n : ℝ)⁻¹ - (q : ℝ)⁻¹)) =
      q * (1 - (n : ℝ)⁻¹) + 1 := by
    field_simp [hn0]
    ring
  rwa [hbase, sub_sub_cancel, show 1 - ((n : ℝ)⁻¹ - (q : ℝ)⁻¹) = 1 - (n : ℝ)⁻¹ + (q : ℝ)⁻¹ by
    ring, ENNReal.coe_natCast] at h

end CompactSupport
end TauCeti
end
end
