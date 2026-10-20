@[expose] public section

open MeasureTheory Real Set

open scoped ENNReal

namespace Feige

namespace LikelihoodRatio

theorem measurable_expWeight : Measurable expWeight := by
  unfold expWeight
  fun_prop

end LikelihoodRatio
end Feige
end
