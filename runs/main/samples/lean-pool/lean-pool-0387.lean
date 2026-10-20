@[expose] public section

namespace Bananas

open Utilities

theorem rankDelta_one_chip_eq_one_of_distinct_mark_classes
    (B : Banana 2) (u v w : B.graph.V)
    (hwu : ¬ linearEquiv B.graph (oneChip w - oneChip u) 0)
    (hwv : ¬ linearEquiv B.graph (oneChip w - oneChip v) 0) :
    rankDelta (mark B.graph u v) (oneChip w) = 1 := by
  have hW : rank B.graph (oneChip w) = 0 := rank_one_chip_zero_banana_two B w
  have hWU : rank B.graph (oneChip w - oneChip u) = -1 := by
    have hLower := rank_geq_neg_one B.graph (oneChip w - oneChip u)
    by_contra hNot
    have hNonneg : 0 ≤ rank B.graph (oneChip w - oneChip u) := by omega
    exact hwu (linearEquiv_zero_of_rank_nonneg_degree_zero' B.graph _ hNonneg (by
      rw [CFDiv.degree.map_sub, deg_one_chip, deg_one_chip]
      norm_num))
  have hWV : rank B.graph (oneChip w - oneChip v) = -1 := by
    have hLower := rank_geq_neg_one B.graph (oneChip w - oneChip v)
    by_contra hNot
    have hNonneg : 0 ≤ rank B.graph (oneChip w - oneChip v) := by omega
    exact hwv (linearEquiv_zero_of_rank_nonneg_degree_zero' B.graph _ hNonneg (by
      rw [CFDiv.degree.map_sub, deg_one_chip, deg_one_chip]
      norm_num))
  have hWUV : rank B.graph (oneChip w - oneChip u - oneChip v) = -1 := by
    apply rank_neg_one_of_deg_neg
    rw [CFDiv.degree.map_sub, CFDiv.degree.map_sub, deg_one_chip, deg_one_chip, deg_one_chip]
    norm_num
  change rank B.graph (oneChip w) -
      rank B.graph (oneChip w - oneChip u) -
      rank B.graph (oneChip w - oneChip v) +
      rank B.graph (oneChip w - oneChip u - oneChip v) = 1
  rw [hW, hWU, hWV, hWUV]
  norm_num

end Bananas
end
