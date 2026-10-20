@[expose] public section

noncomputable section MetricCodesNoncomputable

namespace MetricCodes

namespace Spherical

namespace HigherHarmonicYoung

section

open scoped BigOperators

namespace ArbitraryRankMixedTraceRegularity

open MetricCodes.Spherical.HigherHarmonicYoung

theorem gramPivotExponent_support_disjoint {r n : ℕ}
    (hn : 2 * r < n) (z w : UpperGramPair r) (hzw : z ≠ w) :
    Disjoint (gramPivotExponent hn z).support
      (gramPivotExponent hn w).support := by
  simpa only [gramPivotExponent_support] using gramPivotVariables_disjoint hn z w hzw

end ArbitraryRankMixedTraceRegularity
end
end HigherHarmonicYoung
end Spherical
end MetricCodes
end MetricCodesNoncomputable
end
