namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

noncomputable section

namespace MatrixMultiplication.AllFieldPairMarginals

open MatrixMultiplication.Foundation AllFieldParameters AllFieldHistory AllFieldNativeCapacity

open scoped BigOperators

attribute [local instance] Classical.propDecidable Classical.decEq

theorem littleLaw_positive_weight (t : Shape) (ht : t ∈ positiveSecond)
    (u : Shape) (hu : u ∈ below t) (side : Fin 3) (a : Fin 6)
    (ha : 0 < (littleLaw t u side a : ℝ)) : (statisticWeightCode a).val = u side := by
  change statisticWeight a = u side
  by_contra hne
  have hz := littleLaw_outside_support t u side
    (child_statistic_weight_bounded t ht u hu side) a hne
  have hz' : (littleLaw t u side a : ℝ) = 0 := by exact_mod_cast hz
  linarith

end MatrixMultiplication.AllFieldPairMarginals
end
end MatrixAllFields
end OAI
