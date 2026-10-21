namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory

open scoped NNReal

namespace Problem367.IsingCopyBrownian

open IsingObservationInnovation IsingObservationFactor

open ContinuousObservationHistory ContinuousNoiseSplit

variable {d : ℕ} {beta : ℝ}

variable {μ : Measure (TreeVertex d → IsingSpin)} [IsProbabilityMeasure μ]

theorem future_indep_joinedFiltration
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (s : ℝ≥0) :
    Indep (MeasurableSpace.comap
      (fun q : Paths d × (Paths d × Paths d) => futureArray s q.1) inferInstance)
      (ContinuousCopyBrownian.joinedFiltration s) (copies beta μ) := by
  have : IsProbabilityMeasure ((observationLaw μ).map (innovationMap beta)) :=
    inferInstance
  exact ContinuousCopyBrownian.indep_future_joinedFiltration
    ((observationLaw μ).map (innovationMap beta)) (kernel beta μ) s
    (graph_future_indep hμ s)

end Problem367.IsingCopyBrownian
end
end OAI
