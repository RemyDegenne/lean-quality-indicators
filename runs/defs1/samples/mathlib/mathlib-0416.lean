@[expose] public section

noncomputable section

open Function Multiplicative MonoidWithZeroHom MonoidWithZeroHom.ValueGroup₀

open scoped NNReal

variable {R Γ₀ : Type*} [Ring R] [LinearOrderedCommGroupWithZero Γ₀]

namespace Valuation

open WithZero

namespace RankLeOne

variable {K : Type*} [DivisionRing K] (v : Valuation K Γ₀) [RankLeOne v]

/-- If a valuation has rank at most one and is non trivial,
then it has rank one -/
@[instance_reducible]
def rankOne_of_nontrivial (H : Nontrivial v.ValueGroup₀ˣ) : RankOne v where
  exists_val_nontrivial := by
    by_contra! H'
    rw [nontrivial_iff_exists_ne 1] at H
    obtain ⟨x, hx⟩ := H
    obtain ⟨k, hk⟩ := ValueGroup₀.restrict₀_surjective _ x.val
    have h0 : v k ≠ 0 := by
      apply_fun embedding at hk
      simp only [embedding_restrict₀, coe_toMonoidWithZeroHom] at hk
      simp [hk]
    have h1 : v k ≠ 1 := by
      apply_fun embedding at hk
      simp only [embedding_restrict₀, coe_toMonoidWithZeroHom] at hk
      apply_fun Units.val at hx using
          Units.val_injective (α := v.ValueGroup₀)
      intro h
      apply_fun embedding at hx using embedding_injective (f := (v : K →*₀ Γ₀))
      simp [← hk, h] at hx
    exact h1 (H' k h0)

end RankLeOne
end Valuation
end
end
