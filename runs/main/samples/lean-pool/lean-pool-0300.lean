@[expose] public section

open scoped BigOperators ContDiff

open MeasureTheory Real

open scoped Matrix

noncomputable
section

namespace NashEmbedding

lemma deriv_dil_continuous (n : ℕ) (β : ℝ) : Continuous (deriv (dil n β)) :=
  (dil_contDiff n β).continuous_deriv NashEmbedding.Sobolev.one_le_infty

end NashEmbedding
end
end
