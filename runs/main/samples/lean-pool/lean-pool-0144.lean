@[expose] public section

open scoped BigOperators

namespace BooleanIsoperimetry.CoherentGap

lemma dot_sub {n : ℕ} (first second weights : Relation n) :
    dot (first - second) weights =
      dot first weights - dot second weights := by
  simp [dot, sub_mul, Finset.sum_sub_distrib]

end BooleanIsoperimetry.CoherentGap
end
