namespace OAI

section

open MeasureTheory ProbabilityTheory Filter Set Topology CompactlySupported

open scoped NNReal ENNReal

namespace ExactSLEGreen

open ExactSLEGenerator ExactSLEMain SLEExactGauge.MassVersions

theorem recoveredMass_progressive (a : ℝ) (ha : 1/4 < a)
    (s : ℕ → Finset ℕ) (c : ℕ → ℕ → ℝ) (hc : ∀ k j, j∈s k → 0≤c k j) :
    IsProgressive rawFiltration
      (fun t : ℝ≥0 => recoveredMass a ha s c hc t) := by
  intro T
  apply @measurable_radonLimit _ _ _ _ _ _ _ _
    (Subtype.instMeasurableSpace.prod (rawFiltration T))
  intro k f
  simp_rw [actualMassFunctionals_apply]
  apply Finset.measurable_sum
  intro j hj
  exact measurable_const.mul
    (actualUpperMass_eval_progressive a ha _ (Real.exp_pos _)
      (level_step_le_one a ha j) f T)

end ExactSLEGreen
end
end OAI
