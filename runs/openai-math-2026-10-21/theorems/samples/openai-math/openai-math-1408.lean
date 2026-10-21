namespace OAI

section

section

noncomputable section

open MeasureTheory ProbabilityTheory InformationTheory Real Set

open scoped NNReal ENNReal

open Filter

open scoped Topology

noncomputable section

open Matrix Real

open scoped BigOperators Matrix.Norms.Frobenius ENNReal NNReal

noncomputable section

open Matrix Real

open scoped BigOperators Matrix.Norms.Frobenius NNReal

noncomputable section

open MeasureTheory ProbabilityTheory Real Set Filter

open MeasureTheory.Measure

open scoped ENNReal NNReal MeasureTheory Topology

open MeasureTheory

noncomputable section

noncomputable section

open MeasureTheory Set NormedSpace

open scoped Topology

noncomputable section

open Matrix Real

open scoped BigOperators Matrix.Norms.Frobenius

noncomputable section

open Set Real

open scoped Topology

noncomputable section

open Matrix Set Filter

open scoped Topology Matrix.Norms.Frobenius

noncomputable section

open Matrix NormedSpace ContinuousLinearMap

open scoped Matrix.Norms.Frobenius

noncomputable section

open Matrix

noncomputable section

open MeasureTheory ProbabilityTheory Real Set

open scoped ENNReal NNReal

noncomputable section

open MeasureTheory ProbabilityTheory InformationTheory Real Set

open scoped NNReal ENNReal

noncomputable section

open scoped BigOperators

open MeasureTheory ProbabilityTheory

open Real

noncomputable section

open scoped BigOperators Topology

open Filter Real

namespace SKRatioGaussian

section GOEProbability

variable {ι : Type*} [Fintype ι] [Nonempty ι]

omit [Nonempty ι] in
lemma diagonalT_memLp {r : ℝ} (hr : 0 ≤ r) {a : ι → ℝ} (ha : ∀ i, 0 ≤ a i) :
    MemLp (diagonalT r a) 2 (gaussianCoordinates (MatrixCoordinates ι)) := by
  apply memLp_sqrt_of_nonneg ((gaussianQuadratic_memLp (diagonalWeights r a)).integrable
    (by norm_num))
  intro g
  apply Finset.sum_nonneg
  intro k _
  apply mul_nonneg _ (sq_nonneg _)
  cases k <;> simp only [diagonalWeights]
  · exact le_rfl
  · exact mul_nonneg hr (ha _)

end GOEProbability
end SKRatioGaussian
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end OAI
