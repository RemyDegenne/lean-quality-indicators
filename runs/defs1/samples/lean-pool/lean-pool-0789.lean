@[expose] public section

noncomputable section MetricCodesNoncomputable

namespace MetricCodes

namespace Spherical

section

open scoped BigOperators

namespace HigherWeylGramAlternantCoefficient

open MetricCodes.Spherical.HigherHarmonicYoung

open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRankMixedTraceRegularity

/-- The sum of the row-degree exponent vectors of a finite family of Gram pairs. -/
def gramFamilyExponent {r : ℕ}
    (s : Finset (UpperGramPair r)) : Fin (r + 1) →₀ ℕ :=
  ∑ z ∈ s, gramPairExponent z

end HigherWeylGramAlternantCoefficient
end
end Spherical
end MetricCodes
end MetricCodesNoncomputable
end
