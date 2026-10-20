@[expose] public section

open EuclideanGeometry

open scoped Finset RealInnerProductSpace

variable {V P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P]

variable [NormedAddTorsor V P]

variable {V₂ P₂ : Type*} [NormedAddCommGroup V₂] [InnerProductSpace ℝ V₂] [MetricSpace P₂]

variable [NormedAddTorsor V₂ P₂]

noncomputable section

namespace Affine

namespace Simplex

variable {m n : ℕ} [NeZero m] [NeZero n] (s : Simplex ℝ P n)

/-- The normalized weights of the vertices in an affine combination that gives an excenter with
signs determined by the given set of indices.  An excenter with those signs exists if and only if
the sum of these weights is 1. -/
def excenterWeights (signs : Finset (Fin (n + 1))) : Fin (n + 1) → ℝ :=
  (∑ i, s.excenterWeightsUnnorm signs i)⁻¹ • s.excenterWeightsUnnorm signs

end Simplex
end Affine
end
end
