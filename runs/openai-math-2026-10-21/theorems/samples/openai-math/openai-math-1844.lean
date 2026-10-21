namespace OAI

namespace SharpPlanar.CachedData

open IntegerIntervals IntegerBasis IntegerGrid Numerical

namespace hm4_0_0_7

lemma checked : cachedMomentRuleBox density0 hk4_0_7 = ans := by
  change (finSum (fun j => (finSum (fun i => chunk j i)).scale 1 6)) = ans
  simp_rw [sums_eq]
  decide +kernel

end hm4_0_0_7
end SharpPlanar.CachedData
end OAI
