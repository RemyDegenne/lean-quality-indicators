namespace OAI

namespace SharpPlanar.CachedData

open IntegerIntervals IntegerBasis IntegerGrid Numerical

namespace hm9_1_1_14

lemma checked : cachedMomentRuleBox density1 hk9_1_14 = ans := by
  change (finSum (fun j => (finSum (fun i => chunk j i)).scale 1 6)) = ans
  simp_rw [sums_eq]
  decide +kernel

end hm9_1_1_14
end SharpPlanar.CachedData
end OAI
