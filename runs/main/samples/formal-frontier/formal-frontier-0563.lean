@[expose] public section

universe u v w

namespace Valuation

variable {K : Type u} [DivisionRing K] {Γ₀ : Type v} {Δ₀ : Type w}
  [LinearOrderedCommGroupWithZero Γ₀] [LinearOrderedCommGroupWithZero Δ₀]

section RankOne

variable (v : Valuation K Γ₀) [v.RankOne]

theorem absoluteValue_isNontrivial : v.absoluteValue.IsNontrivial := by
  obtain ⟨x, hx₀, hx₁⟩ := RankOne.nontrivial v
  refine ⟨x, ?_, (absoluteValue_eq_one_iff v x).not.mpr hx₁⟩
  intro hzero
  exact hx₀ (by simp [hzero])

end RankOne
end Valuation
end
