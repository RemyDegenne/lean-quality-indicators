public noncomputable section

open Set Filter Topology MvPolynomial

open scoped NatOrdinal DirectSum

universe u v w x

namespace HahnSeries.Nonpositive

variable {G : Type u} {K : Type v} [AddCommGroup G] [LinearOrder G] [IsOrderedAddMonoid G]
  [UniformSpace G] [IsUniformAddGroup G] [OrderTopology G] [Nontrivial G] [CompleteSpace G]
  [Field K] [CharZero K]

local notation "ν" => (cantorBendixsonDegreeValuation (G := G) (R := K))

theorem hasLowerTruncationDegree_strictTail {c : G} (hc : c < 0) {b : Nonpositive G K}
    {m : NatOrdinal.{u}} (h : HasLowerTruncationDegree b m) :
    HasLowerTruncationDegree (strictTail c b) m := by
  have hbot := degree_sub_strictTail_eq_bot hc b
  have hdeg : ν b = ν (strictTail c b) := degree_eq_of_degree_sub_eq_bot hbot
  rw [hasLowerTruncationDegree_iff]
  refine ⟨hdeg ▸ h.degree_le, fun y hy ↦ ?_⟩
  by_cases hcy : c < y
  · have hdiff := degree_translatedTruncLE_sub_strictTail_eq_bot hcy b
    have heq := degree_eq_of_degree_sub_eq_bot
      (a := translatedTruncLE y b) (b := translatedTruncLE y (strictTail c b))
      (by rw [← map_sub]; exact hdiff)
    rw [← heq]
    exact h.degree_translatedTruncLE_lt hy
  · rw [translatedTruncLE_strictTail_eq_zero (not_lt.mp hcy), (ν).map_zero]
    exact WithBot.bot_lt_coe m

end HahnSeries.Nonpositive
end
