@[expose] public section

noncomputable section MetricCodesNoncomputable

namespace MetricCodes

namespace Spherical

namespace HigherHarmonicYoung

section

open scoped BigOperators

namespace ArbitraryRankMixedTraceRegularity

open MetricCodes.Spherical.HigherHarmonicYoung

/-- The sum of the two variable weights in a coordinate summand of a Gram pairing. -/
def gramSummandWeight {r n : ℕ}
    (z : UpperGramPair r) (k : Fin n) : ℤ :=
  gramVariableWeight r n z.val.1 k +
    gramVariableWeight r n z.val.2 k

end ArbitraryRankMixedTraceRegularity
end
end HigherHarmonicYoung
end Spherical
end MetricCodes
end MetricCodesNoncomputable
end
