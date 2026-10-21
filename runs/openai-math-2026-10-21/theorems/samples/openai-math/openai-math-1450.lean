namespace OAI

noncomputable section

namespace SphericalPerceptronFreeEnergy

open MeasureTheory ProbabilityTheory Filter Set

open scoped Classical ENNReal NNReal BigOperators Topology

lemma indexedLeafMeasure_singleton (n : ℕ) (b : IndexedCascadeBase n) (l : IndexedLeaf n) :
    (indexedLeafMeasure n b) {l} = indexedLeafWeight n b l := by
  rw [indexedLeafMeasure, Measure.sum_apply _ (measurableSet_singleton l), tsum_eq_single l]
  · simp [Measure.smul_apply]
  · intro i hi
    simp [Measure.smul_apply, hi]

end SphericalPerceptronFreeEnergy
end
end OAI
