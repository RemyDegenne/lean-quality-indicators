@[expose] public section

universe u v w

namespace Valuation

variable {K : Type u} [DivisionRing K] {Γ₀ : Type v} {Δ₀ : Type w}
  [LinearOrderedCommGroupWithZero Γ₀] [LinearOrderedCommGroupWithZero Δ₀]

section RankLeOne

variable (v : Valuation K Γ₀) [v.RankLeOne]

@[simp]
theorem absoluteValue_lt_iff (x y : K) :
    v.absoluteValue x < v.absoluteValue y ↔ v x < v y := by
  simp only [absoluteValue_apply, NNReal.coe_lt_coe,
    (RankLeOne.strictMono' (v := v)).lt_iff_lt, restrict_lt_iff]

end RankLeOne
end Valuation
end
