universe v

open scoped NatOrdinal

public noncomputable section

namespace Berarducci

variable {K : Type v} [Field K]

namespace SeriesWithOrdinalValueAboveOne

theorem principalValue_isInfiniteMultiplicativelyPrincipal
    (b : SeriesWithOrdinalValueAboveOne K) :
    Ordinal.IsInfiniteMultiplicativelyPrincipal b.principalValue.val := by
  simp only [principalValue, NatOrdinal.val_of]
  exact b.factorOrdinal.principalFactor_isInfiniteMultiplicativelyPrincipal

end SeriesWithOrdinalValueAboveOne
end Berarducci
end
