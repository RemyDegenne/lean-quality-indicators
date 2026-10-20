@[expose] public section

open MeasureTheory Real

open TopologicalSpace

open scoped BigOperators

noncomputable section

namespace OS4Ergodicity

open OS4infra

export OS4infra (
  timeTranslationDistribution_pairingℂ
  gff_generating_time_invariant
)

theorem OS4''_implies_OS4_Ergodicity (m : ℝ) [Fact (0 < m)] :
    os4DoublePrimeClustering m → OS4Ergodicity (gaussianFreeFieldFree m) := by
  intro h_cluster
  exact OS4'_implies_OS4 m (OS4''_implies_OS4' m h_cluster)

end OS4Ergodicity
end
end
