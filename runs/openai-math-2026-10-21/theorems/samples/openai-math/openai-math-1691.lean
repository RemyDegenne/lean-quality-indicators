namespace OAI

namespace SharpPlanar.CachedData

open IntegerIntervals IntegerBasis IntegerGrid

namespace cm25_4_0_1

lemma contains : ans.Contains (momentRuleValue quadraturePoint fejerWeight 25 4 false true) := by
  rw [← checked]
  exact cachedMomentRuleBox_contains column25_0_contains kernel4_1_contains

end cm25_4_0_1
end SharpPlanar.CachedData
end OAI
