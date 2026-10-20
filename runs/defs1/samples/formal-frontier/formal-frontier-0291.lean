@[expose] public section

universe u v w

namespace Valuation

variable {K : Type u} [DivisionRing K] {Γ₀ : Type v} {Δ₀ : Type w}
  [LinearOrderedCommGroupWithZero Γ₀] [LinearOrderedCommGroupWithZero Δ₀]

section RankLeOne

variable (v : Valuation K Γ₀) [v.RankLeOne]

/-- The real absolute value of a valuation on a division ring with rank-at-most-one data.
It uses the embedding of the restricted value group carried by those data, and does not
choose a numerical normalization. Trivial valuations are allowed. -/
noncomputable def absoluteValue : AbsoluteValue K ℝ where
  toFun x := (RankLeOne.hom' v (v.restrict x) : ℝ)
  map_mul' x y := by simp only [map_mul, NNReal.coe_mul]
  nonneg' x := NNReal.coe_nonneg _
  eq_zero' x := by
    rw [NNReal.coe_eq_zero, ← map_zero (RankLeOne.hom' v),
      (RankLeOne.strictMono' (v := v)).injective.eq_iff, restrict_eq_zero_iff, map_eq_zero]
  add_le' x y := by
    change (RankLeOne.hom' v (v.restrict (x + y)) : ℝ) ≤
      (RankLeOne.hom' v (v.restrict x) : ℝ) + (RankLeOne.hom' v (v.restrict y) : ℝ)
    rw [← NNReal.coe_add, NNReal.coe_le_coe]
    calc
      RankLeOne.hom' v (v.restrict (x + y)) ≤
          RankLeOne.hom' v (max (v.restrict x) (v.restrict y)) :=
        (RankLeOne.strictMono' (v := v)).monotone (v.restrict.map_add x y)
      _ = max (RankLeOne.hom' v (v.restrict x)) (RankLeOne.hom' v (v.restrict y)) :=
        (RankLeOne.strictMono' (v := v)).monotone.map_max
      _ ≤ _ := max_le (le_add_of_nonneg_right zero_le)
        (le_add_of_nonneg_left zero_le)

end RankLeOne
end Valuation
end
