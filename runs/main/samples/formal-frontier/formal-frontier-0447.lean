@[expose] public section

universe u v

namespace Valuation

variable {K : Type u} [DivisionRing K] {Γ₀ : Type v}
  [LinearOrderedCommGroupWithZero Γ₀] (v : Valuation K Γ₀) [v.RankLeOne]

theorem absoluteValueUniformEquiv_toEquiv :
    v.absoluteValueUniformEquiv.toEquiv =
      ((WithVal.equiv v).trans (WithAbs.equiv v.absoluteValue).symm).toEquiv := rfl

end Valuation
end
