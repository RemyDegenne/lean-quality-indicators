namespace OAI

noncomputable section

namespace PolycyclicRecognition

open MeasureTheory Set

open scoped NNReal ENNReal

variable {G W : Type*} [Group G] [MetricSpace G] [ProperSpace G]
  [IsTopologicalGroup G] [IsIsometricSMul G G] {Λ : ℝ≥0}
  [MeasurableSpace (NormalizedPair G Λ)] [BorelSpace (NormalizedPair G Λ)]
  [NormedAddCommGroup W] [NormedSpace ℝ W]

theorem exists_probability_with_same_pairHeight_slope
    (μ : Measure (NormalizedPair G Λ)) [IsFiniteMeasure μ]
    [SMulInvariantMeasure G (NormalizedPair G Λ) μ] (hμ : μ ≠ 0)
    (π l : G →* Multiplicative W) (hπ : Continuous fun g => (π g).toAdd)
    (hsub : ∀ ε : ℝ, 0 < ε → ∃ B : ℝ, 0 ≤ B ∧ ∀ g,
      ‖pairHeightL2 μ π hπ g - Lp.const 2 μ (l g).toAdd‖ ≤ ε * dist 1 g + B) :
    ∃ ν : Measure (NormalizedPair G Λ), ∃ hν : IsProbabilityMeasure ν,
      SMulInvariantMeasure G (NormalizedPair G Λ) ν ∧
      let := hν
      ∀ ε : ℝ, 0 < ε → ∃ B : ℝ, 0 ≤ B ∧ ∀ g,
        ‖pairHeightL2 ν π hπ g - Lp.const 2 ν (l g).toAdd‖ ≤ ε * dist 1 g + B := by
  have hmass : μ univ ≠ 0 := fun h => hμ (Measure.measure_univ_eq_zero.mp h)
  let ν := (μ univ)⁻¹ • μ
  have hν : IsProbabilityMeasure ν := by
    constructor
    change ((μ univ)⁻¹ • μ) univ = 1
    rw [Measure.smul_apply, smul_eq_mul]
    exact ENNReal.inv_mul_cancel hmass (measure_lt_top μ univ).ne
  let := hν
  refine ⟨ν, hν, inferInstance, ?_⟩
  exact pairHeight_sublinear_smul_measure μ (μ univ)⁻¹ π l hπ hsub

end PolycyclicRecognition
end
end OAI
