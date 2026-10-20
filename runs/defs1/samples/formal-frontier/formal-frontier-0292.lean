@[expose] public section

universe u v w

namespace Valuation

variable {K : Type u} [Field K] {ι : Type v} {Γ₀ : Type w}
  [LinearOrderedCommGroupWithZero Γ₀] (val : ι → Valuation K Γ₀)

/-- The common valuation integers of a family, with no finiteness assumption. -/
def intersectionSubring : Subring K :=
  ⨅ i, (val i).valuationSubring.toSubring

end Valuation
end
