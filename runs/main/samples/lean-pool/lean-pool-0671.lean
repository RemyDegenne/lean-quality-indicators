@[expose] public section

noncomputable section PortComputability

open Filter MeasureTheory

namespace MarkovProcess

namespace ContinuousPath

section

variable {alpha : Type*} [PseudoMetricSpace alpha]
  [MeasurableSpace alpha] [BorelSpace alpha]

theorem comap_densePastRestriction_eq_canonicalFiltration (S : DenseTime) :
    MeasurableSpace.comap (densePastRestriction (alpha := alpha) S) inferInstance =
      canonicalFiltration (alpha := alpha) (DenseTime.castOrderEmbedding S) := by
  rw [comap_densePastRestriction_eq_denseCanonicalFiltration,
    denseCanonicalFiltration_eq_canonicalFiltration]

end
end ContinuousPath
end MarkovProcess
end PortComputability
end
